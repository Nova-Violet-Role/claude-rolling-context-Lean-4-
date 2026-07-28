# SPDX-FileCopyrightText: 2026 Saimono / Nova-Violet Role
# SPDX-License-Identifier: AGPL-3.0-or-later OR EUPL-1.2

"""
Rolling Context Proxy — VIBE CODE port (Mistral)

Vendored from nestor-plugins/rolling-context 1.8.0. The pristine files are kept
beside this one in ../upstream/ and are never executed; diff against them to see
every porting change.

Same idea as upstream: a transparent proxy that summarizes OLD messages and keeps
recent ones verbatim, so the context wall is never hit. What changed is the wire:
Claude Code speaks Anthropic /v1/messages, vibe speaks Mistral
/v1/chat/completions.

THE FOUR THINGS THAT ARE NOT COSMETIC (each measured, not assumed):

1. `system` IS AN IN-ARRAY MESSAGE HERE. Anthropic carries it out-of-band in a
   top-level `system` field, so upstream can replace messages[0:cut] freely.
   Vibe sends roles ['system', 'user', 'assistant', 'tool', ...] with the system
   prompt AT INDEX 0 (measured: dumps/req-011.json). Replacing from index 0 would
   DELETE THE SYSTEM PROMPT and silently lobotomize the agent — the model would
   still answer, so nothing would look broken. Every cut is anchored past it.

2. Tool shape differs. Anthropic: `tool_use`/`tool_result` blocks inside content.
   Mistral: `tool_calls` on the assistant message, and a separate
   {"role":"tool","tool_call_id","name","content"} message, content a plain string.

3. Hashing must cover `tool_calls`. Upstream hashes role+content only. Two
   assistant turns can have identical content ("") and different tool calls, which
   would collide and let a wrong compression match. tool_calls are hashed here.

4. Compression is PROACTIVE, not reactive. Upstream compresses for the NEXT
   request, which loses a race against vibe's own auto-compaction
   (vibe/core/middleware.py:104). See the [PROACTIVE] block below.

Pure stdlib — no external dependencies needed.
"""

import hashlib
import json
import os
import sys
import logging
import threading
import time
import ssl
import http.client
from http.server import HTTPServer, BaseHTTPRequestHandler
from urllib.parse import urlparse

from compressor import RollingCompressor

class FlushFileHandler(logging.FileHandler):
    def emit(self, record):
        super().emit(record)
        self.flush()

# 5590, NOT upstream's 5588. A Claude-side rolling-context proxy may be running on
# this same machine; two proxies on one port is a silent cross-wire, so the vibe
# port is distinct by construction. (5589 is the GLM fork's port — also avoided.)
#
# READ BEFORE THE LOGGING SETUP, not after: the log file name is derived from it.
LISTEN_PORT = int(os.environ.get("ROLLING_CONTEXT_VIBE_PORT") or "5590")

# DEFECT D-I (review 4). Every instance used to append to ONE
# `rolling-context-debug.log`, with no port or pid in the name or in the line
# format. Consequences, both measured rather than argued:
#   - a scratch instance started for testing interleaved its lines into the LIVE
#     proxy's log, so the operator's only record of production behaviour was
#     contaminated by a test run;
#   - the two processes also have byte-identical command lines
#     (`python.exe vibe-rc-server.py`), so the log was the ONLY way to tell them
#     apart, and it could not. That is why the no-pattern-kill rule is
#     load-bearing: nothing else distinguishes them.
# The port is in the FILENAME (one file per listener, the thing that is unique by
# construction) and the pid is in every LINE (so a restart on the same port is
# still attributable). Old `rolling-context-debug.log` files are left alone.
_log_dir = os.path.join(os.path.expanduser("~"), ".vibe", "logs")
os.makedirs(_log_dir, exist_ok=True)
_log_path = os.path.join(_log_dir, f"rolling-context-debug.{LISTEN_PORT}.log")
_LOG_FORMAT = f"%(asctime)s [pid {os.getpid()}] [%(levelname)s] %(message)s"
_log_handler = FlushFileHandler(_log_path, mode="a", encoding="utf-8", errors="replace")
_log_handler.setFormatter(logging.Formatter(_LOG_FORMAT))

# DEFECT D-Q (measured in review 5). The launcher starts this process with
# `-RedirectStandardOutput`, so on Windows `sys.stdout` is a cp1252 file stream.
# Every log record carrying a character cp1252 cannot encode — an em dash in a
# refusal reason, or the message CONTENT that the [MATCH] mismatch diagnostic
# prints verbatim — made the handler raise UnicodeEncodeError. MEASURED: 22
# tracebacks in one 5-minute agent run, every one of them destroying a [MATCH]
# diagnostic. That is precisely the output D-A is investigated with, so the
# failure hid the evidence for the defect class this proxy has already been bitten
# by twice. Upstream traffic was unaffected (35/35 responses were 200), which is
# why it went unnoticed: the proxy works, only its diagnostics evaporate.
try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
except (AttributeError, OSError):        # not a reconfigurable stream; not fatal
    pass
logging.basicConfig(
    level=logging.DEBUG,
    format=_LOG_FORMAT,
    handlers=[logging.StreamHandler(sys.stdout), _log_handler],
)
log = logging.getLogger("rolling-context")


def _load_upstream() -> str:
    """Resolve the upstream API endpoint.

    Upstream read ~/.claude/settings.json here, because the Claude Code hook wrote
    ROLLING_CONTEXT_UPSTREAM there without exporting it (their issue #3). Vibe has
    no settings.json and no such hook, so that whole fallback is DROPPED rather
    than ported to a file that does not exist.

    Env var wins; otherwise Mistral direct. Never route back at ourselves.
    """
    up = os.environ.get("ROLLING_CONTEXT_VIBE_UPSTREAM")
    if up:
        if (urlparse(up).port or 0) == LISTEN_PORT:
            log.error(
                f"[CFG] ROLLING_CONTEXT_VIBE_UPSTREAM points at our own port "
                f"{LISTEN_PORT} — that is an infinite loop. Ignoring it."
            )
        else:
            return up
    return "https://api.mistral.ai"


UPSTREAM_URL = _load_upstream()

# EVERY knob is read from a _VIBE_-scoped name. This is not tidiness — it was a
# MEASURED bug. A Claude-side rolling-context install exports the unscoped names
# into the user environment:
#
#   ROLLING_CONTEXT_PORT=5588
#   ROLLING_CONTEXT_TRIGGER=250000
#   ROLLING_CONTEXT_TARGET=120000
#   ROLLING_CONTEXT_UPSTREAM=http://127.0.0.1:47821   <-- a CHAINED proxy
#
# This proxy booted with trigger=250,000 / target=120,000 inherited from the
# Claude side before the rename, and had the upstream name been left unscoped it
# would have pointed Mistral summarization traffic at 127.0.0.1:47821 — into the
# Anthropic chain, with a Mistral bearer token attached. Two products sharing a
# namespace on one machine silently configure each other.
# 220000/120000 are the OPERATING POINT, not upstream's defaults. Upstream 1.8.0
# ships 100000/40000 (upstream/server.py:77-78) and the port inherited them, which
# meant the documented 220k trigger was never actually live.
#
# ORDERING IS LOAD-BEARING: this trigger must stay BELOW the model's
# `auto_compact_threshold` in ~/.vibe/config.toml, currently 245000. Rolling
# compresses at 220k; native compaction is the floor at 245k that only catches the
# case where the proxy correctly declines to compress because it cannot shrink
# ("Compression no longer helps: merged=77,288 >= current=76,115"). If this number
# ever rises above that one, native wins the race and replaces the whole
# conversation with a lossy summary — the exact behaviour this proxy replaces.
# Change one, change the other, and keep the 25k of headroom.
TRIGGER_TOKENS = int(os.environ.get("ROLLING_CONTEXT_VIBE_TRIGGER") or "220000")
TARGET_TOKENS = int(os.environ.get("ROLLING_CONTEXT_VIBE_TARGET") or "120000")
# Summarizer model; empty falls back to compressor.LEGACY_DEFAULT_MODEL.
SUMMARIZER_MODEL = os.environ.get("ROLLING_CONTEXT_VIBE_MODEL") or ""
# After a failed compression, wait this long before trying again — otherwise a
# failing summarizer (e.g. rate-limited) gets re-hammered on every request.
FAILURE_COOLDOWN = int(os.environ.get("ROLLING_CONTEXT_VIBE_FAILURE_COOLDOWN") or "300")

ssl_ctx = ssl.create_default_context()
_parsed_upstream = urlparse(UPSTREAM_URL)
UPSTREAM_PATH = _parsed_upstream.path or ""


def _join_path(upstream_path: str, request_path: str) -> str:
    """Join upstream path with request path, handling edge cases."""
    if not upstream_path:
        return request_path
    if not request_path or request_path == "/":
        return upstream_path
    if upstream_path.endswith("/") and request_path.startswith("/"):
        return upstream_path[:-1] + request_path
    if not upstream_path.endswith("/") and not request_path.startswith("/"):
        return upstream_path + "/" + request_path
    return upstream_path + request_path


compressor = RollingCompressor(
    trigger_tokens=TRIGGER_TOKENS,
    target_tokens=TARGET_TOKENS,
    summarizer_model=SUMMARIZER_MODEL,
)


def _upstream_conn():
    """Create a connection to the upstream server."""
    if _parsed_upstream.scheme == "https":
        return http.client.HTTPSConnection(
            _parsed_upstream.hostname,
            _parsed_upstream.port or 443,
            context=ssl_ctx,
            timeout=600,
        )
    else:
        return http.client.HTTPConnection(
            _parsed_upstream.hostname,
            _parsed_upstream.port or 80,
            timeout=600,
        )


# ---------------------------------------------------------------------------
# Content-based matching
# ---------------------------------------------------------------------------

import re

# Upstream stripped Claude Code's tags (system-reminder, local-command-stdout, ...).
# Those strings NEVER appear in vibe traffic, so porting them verbatim would leave
# the hash unstable and every match would silently miss — the proxy would look
# healthy and compress nothing.
#
# Vibe's equivalents are the four in vibe/core/utils/tags.py:8-13, and that module
# exposes them as KNOWN_TAGS precisely because they wrap injected, turn-varying text.
_VIBE_TAGS = ("user_cancellation", "tool_error", "vibe_stop_event", "vibe_warning")
_VOLATILE_TAGS_RE = re.compile(
    r"<(?:" + "|".join(_VIBE_TAGS) + r")>.*?</(?:" + "|".join(_VIBE_TAGS) + r")>",
    re.DOTALL,
)


def _strip_volatile_tags(text: str) -> str:
    """Strip vibe's dynamic tags that change between requests."""
    return _VOLATILE_TAGS_RE.sub("", text)


# --- /pin rate limit ---------------------------------------------------------
# A token bucket, not a security control. `/pin` is unauthenticated on loopback
# and the secret it uses is a readable file, so a tool-capable caller mints tags
# with or without this. What it buys is a BOUND and a LOG LINE: a runaway loop
# minting thousands of pins now shows up instead of quietly succeeding.
_PIN_RATE_MAX = int(os.environ.get("ROLLING_CONTEXT_PIN_RATE_MAX") or 30)
_PIN_RATE_WINDOW = int(os.environ.get("ROLLING_CONTEXT_PIN_RATE_WINDOW") or 60)
_pin_rate_hits = []
_pin_rate_lock = threading.Lock()


def _pin_rate_limit_ok() -> bool:
    """True when a mint is allowed now. Sliding window, never raises."""
    now = time.time()
    with _pin_rate_lock:
        cutoff = now - _PIN_RATE_WINDOW
        _pin_rate_hits[:] = [t for t in _pin_rate_hits if t > cutoff]
        if len(_pin_rate_hits) >= _PIN_RATE_MAX:
            return False
        _pin_rate_hits.append(now)
        return True


def _normalize_content(content):
    """Strip volatile metadata (cache_control, system-reminder) for stable hashing."""
    if isinstance(content, str):
        return _strip_volatile_tags(content)
    if isinstance(content, list):
        result = []
        for block in content:
            if isinstance(block, dict):
                b = {}
                for k, v in block.items():
                    if k == "cache_control":
                        continue
                    if k == "content" and isinstance(v, (list, str)):
                        b[k] = _normalize_content(v)
                    elif k == "text" and isinstance(v, str):
                        b[k] = _strip_volatile_tags(v)
                    else:
                        b[k] = v
                result.append(b)
            else:
                result.append(block)
        return result
    return content


def _hash_message(msg: dict) -> str:
    """Stable hash of a message.

    PORT NOTE — upstream hashed role+content ONLY. That is safe in Anthropic shape,
    where a tool call lives *inside* content as a tool_use block and is therefore
    already covered. In Mistral shape the call sits in a SIBLING key, `tool_calls`,
    and the assistant's content is routinely "" — so two different tool calls hash
    identically under the upstream formula. Colliding hashes are not a cosmetic
    problem here: find_match() replaces history by hash chain, so a collision can
    splice a summary over the wrong messages.

    `tool_call_id` is included for the same reason on the tool-result side.
    """
    role = msg.get("role", "")
    content = _normalize_content(msg.get("content", ""))
    if not isinstance(content, str):
        content = json.dumps(content, sort_keys=True)

    extra = ""
    tcs = msg.get("tool_calls")
    if tcs:
        # Hash name+arguments, NOT the id: ids are regenerated per request by the
        # provider, so including them would make every hash unstable across turns.
        sig = []
        for tc in tcs:
            if isinstance(tc, dict):
                fn = tc.get("function") or {}
                sig.append({"name": fn.get("name", ""), "arguments": fn.get("arguments", "")})
        extra += ":tc=" + json.dumps(sig, sort_keys=True)
    if role == "tool":
        # Same reasoning: the id is volatile, the tool NAME is not.
        extra += ":tn=" + str(msg.get("name", ""))

    raw = f"{role}:{content}{extra}"
    return hashlib.sha256(raw.encode("utf-8", errors="replace")).hexdigest()[:16]


def _hash_messages(messages: list) -> list:
    return [_hash_message(m) for m in messages]


class CompressionStore:
    """Content-based compression tracking. No sessions, no fingerprints, no keys.

    Stores a list of compressions. Each has original_hashes (what was compressed)
    and prefix (the replacement). On ANY request, scans messages — if the hashes
    match a stored compression, replaces them with the prefix.
    """

    def __init__(self):
        self._lock = threading.Lock()
        self._compressions = []  # list of compression entries

    def find_match(self, msg_hashes: list, messages: list = None):
        """Find a compression whose hash chain appears in msg_hashes.

        Returns the match whose chain ends furthest into the request
        (latest compression = covers the most history).
        Replaces everything up to and including the match, since the
        compression already contains a summary of everything before it.
        """
        with self._lock:
            best = None
            best_end = -1  # position in msg_hashes where the match ends
            for entry in self._compressions:
                oh = entry["original_hashes"]
                if not oh:
                    continue
                # Search for the hash chain in msg_hashes
                chain_len = len(oh)
                found = False
                for start in range(len(msg_hashes) - chain_len + 1):
                    if msg_hashes[start:start + chain_len] == oh:
                        end = start + chain_len
                        if end > best_end:
                            best = entry
                            best_end = end
                        found = True
                        break
                if not found and chain_len <= len(msg_hashes):
                    # Count total mismatches
                    mismatches = []
                    for i in range(min(chain_len, len(msg_hashes))):
                        if oh[i] != msg_hashes[i]:
                            mismatches.append(i)
                    log.warning(
                        f"[MATCH] No match: chain={chain_len} req={len(msg_hashes)} "
                        f"mismatches={len(mismatches)} at positions: "
                        f"{mismatches[:10]}{'...' if len(mismatches) > 10 else ''}"
                    )
                    # Dump content of first mismatched message for debugging
                    if mismatches and messages and entry.get("_debug_messages"):
                        idx = mismatches[0]
                        stored_msg = entry["_debug_messages"][idx] if idx < len(entry["_debug_messages"]) else None
                        incoming_msg = messages[idx] if idx < len(messages) else None
                        if stored_msg and incoming_msg:
                            s_content = str(stored_msg.get("content", ""))[:500]
                            i_content = str(incoming_msg.get("content", ""))[:500]
                            log.warning(
                                f"[MATCH] Mismatch at [{idx}] role={stored_msg.get('role')}:\n"
                                f"  STORED:   {s_content}\n"
                                f"  INCOMING: {i_content}"
                            )
            return best, best_end

    def add(self) -> dict:
        entry = {
            "original_hashes": [],   # hashes of original messages we replaced
            "prefix": None,          # compressed replacement messages
            "pending": None,         # pending compression result
            "pending_hashes": None,  # hashes for pending
            "thread": None,          # background compression thread
        }
        with self._lock:
            self._compressions.append(entry)
        return entry

    def remove(self, entry: dict):
        with self._lock:
            self._compressions = [e for e in self._compressions if e is not entry]

    @property
    def compressions(self):
        return self._compressions


store = CompressionStore()


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _forward_headers(req_headers: dict, body: bytes = None, strip_encoding: bool = False) -> dict:
    headers = {}
    for key, value in req_headers.items():
        lower = key.lower()
        if lower in ("host", "transfer-encoding", "connection", "content-length"):
            continue
        if strip_encoding and lower == "accept-encoding":
            continue
        headers[key] = value
    if body is not None:
        headers["content-length"] = str(len(body))
    log.debug(f"[HDR] Forwarding headers: {list(headers.keys())}")
    return headers


def get_passthrough_headers(req_headers: dict) -> dict:
    headers = {}
    for key, value in req_headers.items():
        lower = key.lower()
        if lower not in ("host", "content-length", "transfer-encoding"):
            headers[key] = value
    return headers


def _system_prefix_len(messages: list) -> int:
    """How many leading messages are system messages that must never be compressed.

    THE core structural difference from upstream. Anthropic puts the system prompt in
    a top-level `system` field, so upstream's cut logic starts at index 0 with no
    risk. Vibe puts it IN the array at index 0 (measured on live traffic:
    roles=['system','user','assistant','tool','tool']). If a compression replaced
    from index 0, the system prompt would be summarized away and the agent would
    keep answering — losing its tools contract, its identity, and its rules with no
    error anywhere. Every cut is floored at this value.
    """
    n = 0
    for m in messages:
        if m.get("role") == "system":
            n += 1
        else:
            break
    return n


def _validate_tool_pairs(messages: list) -> list:
    """Drop a leading run that references tool calls which are no longer present.

    Mistral shape, not Anthropic: the call is `tool_calls` on the assistant message
    and the result is a whole message with role "tool" carrying `tool_call_id`.
    A tool message whose call was summarized away is a hard 400 from the API, so it
    must be dropped rather than merely tolerated.

    The system prefix is preserved and re-attached — dropping it to fix a tool pair
    would trade a 400 for a silent lobotomy.
    """
    head = _system_prefix_len(messages)
    system_msgs, body = messages[:head], messages[head:]

    known_ids = set()
    valid_from = 0
    for i, msg in enumerate(body):
        if msg.get("role") == "assistant":
            for tc in msg.get("tool_calls") or []:
                if isinstance(tc, dict) and tc.get("id"):
                    known_ids.add(tc["id"])
        elif msg.get("role") == "tool":
            if msg.get("tool_call_id", "") not in known_ids:
                valid_from = i + 1

    if valid_from == 0:
        # DEFECT D-K (review 4): this used to `return system_msgs + body` — i.e. the
        # final sweep was applied ONLY on the branch where the prefix walk found a
        # leading orphan. The comment below claimed the result was "orphan-free by
        # CONSTRUCTION"; MEASURED by exhaustive search over all message sequences of
        # length <= 5, that claim was false on this branch. `[system, assistant(call
        # a), user]` — a DANGLING tool_call, which is precisely what a cut landing
        # between a call and its results produces — was forwarded untouched and is a
        # hard Mistral 400 ("Not the same number of function calls and responses").
        # The sweep is now unconditional, which is what Compressor.lean's
        # `validateToolPairsFixed` always modelled: the Lean applied `dropOrphansAux`
        # with no `vf = 0` special case, so the proof described a function this file
        # did not implement.
        return _drop_broken_tool_groups(system_msgs + body)

    # DEFECT D-E: `return system_msgs + body[valid_from:]` discarded EVERYTHING
    # before the orphan — including the [summary, ack] pair and the entire pinned
    # block. Measured: 10 messages in, 2 out, summary gone, every pin gone. This
    # function runs AFTER `rebuild`, so `pinned_never_cut` — which is a theorem
    # about `rebuild` — cannot see it. Hard memory that survives compression by
    # construction and is then deleted by a downstream sanitizer is not hard.
    #
    # Only messages that are part of a BROKEN tool group need to go. The summary,
    # the ack and pinned messages carry no tool_calls and no tool_call_id (both are
    # ineligible for pinning precisely because hoisting them orphans the other
    # half), so re-attaching them is always wire-legal.
    dropped = body[:valid_from]
    rescued = [m for m in dropped if _rescue_eligible(m)]
    log.info(
        f"Dropping {valid_from - len(rescued)} messages with orphaned tool_call_id "
        f"references (system prefix of {head} preserved, "
        f"{len(rescued)} pinned/summary messages rescued)"
    )
    if len(rescued) != len(dropped):
        # Name what was actually lost. The old log line said only how many
        # messages went, never that the summary or a pin was among them.
        lost = [m.get("role") for m in dropped if m not in rescued]
        log.warning(f"[TOOLPAIR] discarded roles: {lost}")
    # The prefix walk above is NOT sufficient on its own, and was not before the
    # rescue existed: `known_ids` accumulates from index 0 including messages the
    # walk then drops, so a surviving tool message can have been validated against
    # an assistant that did not survive. A final sweep makes the result orphan-free
    # by CONSTRUCTION rather than by argument.
    return _drop_broken_tool_groups(system_msgs + rescued + body[valid_from:])


def _rescue_eligible(msg: dict) -> bool:
    """May this message be lifted out of a dropped run and re-attached?

    Content alone is NOT enough. `_is_synthetic` tests text, so a TOOL RESULT whose
    body happens to equal ACK_TEXT counted as synthetic and was rescued while the
    assistant that issued its `tool_call_id` was dropped — emitting the very orphan
    this function exists to remove, and a stable one: re-running the sanitizer left
    it unchanged, so the session was wedged with a hard Mistral 400.
    The structural tests below are what make the rescue safe.
    """
    if msg.get("role") not in ("user", "assistant"):
        return False
    if msg.get("tool_calls") or msg.get("tool_call_id"):
        return False
    return compressor._effective_pinned(msg) or compressor._is_synthetic(msg)


def _drop_broken_tool_groups(messages: list) -> list:
    """Remove every incomplete tool group, both halves. ORDER-AWARE.

    Mistral rejects BOTH directions: a tool result with no call is
    "Unexpected role 'tool'", and a call with no result is "Not the same number of
    function calls and responses". So a group is kept only when the assistant and
    all of its results are present; otherwise the whole group goes.

    DEFECT D-L (review 4). The previous implementation decided membership with
    SETS and never looked at position, so it accepted a tool result whose call
    appeared LATER in the list. MEASURED: `[system, tool(a), assistant(call a)]`
    was returned unchanged, which is the "Unexpected role 'tool'" 400 — the exact
    failure this function exists to prevent. Exhaustive search over sequences of
    length <= 5 found 460 such inputs, plus 434 on which the old sweep was not even
    idempotent.

    Two further set-based holes, both measured:
      - an id appearing on two assistants (one group complete, one not) landed in
        complete_ids AND doomed_ids; both assistants were dropped and the result
        was KEPT, emitting an orphan.
      - an assistant whose `tool_calls` carry no usable `id` produced `ids = set()`,
        and `set() <= complete_ids` is vacuously true, so it survived as a dangling
        call.

    The rule is now positional and mutually recursive, computed to a fixpoint:
      - a tool result is kept only if a KEPT assistant EARLIER carries its id;
      - an assistant call is kept only if every one of its ids has a KEPT result
        LATER.
    Dropping one can invalidate the other, so the passes repeat until stable. Each
    pass only ever flips keep True -> False, so it terminates.

    This mirrors `dropOrphansAux` in Compressor.lean, extended to the dangling-call
    direction that `orphanFree` alone does not capture.
    """
    n = len(messages)
    keep = [True] * n

    def _ids_of(m):
        """Non-empty ids on an assistant tool_call, or None if the call is unusable."""
        raw = m.get("tool_calls") or []
        ids = [tc.get("id") for tc in raw if isinstance(tc, dict)]
        return ids

    changed = True
    while changed:
        changed = False

        # Pass 1 - orphan results: a tool message needs a KEPT assistant EARLIER.
        known = set()
        for i, m in enumerate(messages):
            if not keep[i]:
                continue
            role = m.get("role")
            if role == "assistant" and m.get("tool_calls"):
                for tid in _ids_of(m):
                    if tid:
                        known.add(tid)
            elif role == "tool":
                if m.get("tool_call_id") not in known:
                    keep[i] = False
                    changed = True

        # Pass 2 - dangling calls: every id needs a KEPT result LATER.
        results = {}
        for i, m in enumerate(messages):
            if keep[i] and m.get("role") == "tool":
                results.setdefault(m.get("tool_call_id"), []).append(i)
        for i, m in enumerate(messages):
            if not keep[i] or m.get("role") != "assistant" or not m.get("tool_calls"):
                continue
            ids = _ids_of(m)
            ok = bool(ids) and all(
                tid and any(j > i for j in results.get(tid, ())) for tid in ids
            )
            if not ok:
                keep[i] = False
                changed = True

    out = [m for i, m in enumerate(messages) if keep[i]]
    if len(out) != len(messages):
        log.warning(f"[TOOLPAIR] final sweep removed {len(messages) - len(out)} "
                    f"message(s) belonging to incomplete tool groups")
    return out


_compression_failed_at = 0.0


def _do_background_compression(entry: dict, messages: list, auth_headers: dict,
                               real_token_count: int = None, payload: dict = None):
    """Compress messages. Key = hashes of messages that were summarized (not kept verbatim)."""
    global _compression_failed_at
    log.info(f"[BG] Starting compression of {len(messages)} messages...")
    try:
        result = compressor.compress_ex(messages, auth_headers,
                                        real_token_count=real_token_count, payload=payload)
        if not result.ok:
            # Nothing stored — but say WHICH refusal, because "compress returned
            # None" is what made defect D3 invisible for weeks.
            log.info(f"[BG] Declined ({result.refusal}): {result.detail}")
            store.remove(entry)
            return
        # result.messages = [summary, ack] + pinned_verbatim + recent_verbatim
        # Prefix = [summary, ack] + pinned. The recent messages come from the
        # incoming request during injection, so including them here would
        # duplicate them; the PINNED ones must be here, because they live inside
        # the replaced span and injection deletes that whole span.
        prefix = result.prefix
        # AUDIT-FIX (defect 4), second half: take the cut index from the
        # compressor's own result instead of recovering it as
        # `len(messages) - (len(compressed) - 2)`. That subtraction was already
        # wrong once, and with hard memory it is wrong AGAIN and differently:
        # pinned messages are in `compressed` but are NOT part of the verbatim
        # tail, so the derived index would run past the true cut and the stored
        # chain would omit real messages. An index that is reported cannot drift
        # from an index that is used. Lean: `cut_in_range`.
        cut_index = result.cut_index
        # AUDIT-FIX (defect 4): floor at the system prefix, exactly like the
        # [PROACTIVE] block in _handle_messages. This function was left
        # upstream-shaped, i.e. `summarized = messages[:N]` starting at index 0.
        #
        # Two consequences, both silent:
        #  a) the stored hash chain began with the SYSTEM message. Cycle 1 still
        #     matched by luck (the merge re-attaches messages[:sys_head]), which is
        #     why this hid.
        #  b) the SUMMARY_MARKER probe read summarized[0] — the system prompt — so
        #     it never found the marker and never set start=2. On the second cycle,
        #     run against an already-injected history, the chain therefore contained
        #     the proxy's own synthetic [summary, ack] pair. vibe never sends those
        #     messages, so that chain can NEVER match: the entry is dead on arrival,
        #     every later request logs "[MATCH] No match", and the conversation keeps
        #     re-injecting the FIRST, increasingly stale summary.
        sys_head = _system_prefix_len(messages)
        summarized = messages[sys_head:cut_index]
        # Skip old summary prefix if present
        from compressor import SUMMARY_MARKER
        start = 0
        if summarized and isinstance(summarized[0].get("content", ""), str):
            # AUTHENTICATED, not a substring test. `_is_synthetic` verifies the
            # HMAC. Gating on a bare marker let forged text steer the key chain
            # while the compressor itself refused to honour it — hardening one
            # half of a pair and leaving the twin is how D4 survived its first fix.
            if compressor._is_synthetic(summarized[0]):
                # DEFECT D-A: `start = 2` alone skips only [summary, ack]. With hard
                # memory the injected prefix is [summary, ack] + pinned_kept, so the
                # key chain would begin on a PINNED message — which in the client's
                # real history sits near the front, not at the recent tail. The chain
                # then never matches: every later round logs "[MATCH] No match",
                # stores another dead entry, and pays for another summarization while
                # the injection point never advances. MEASURED over 90 rounds with a
                # single pin: 46 paid summarizer calls vs 7, 45 dead entries, and a
                # 205,366-char final payload against 49,600 with no pin — a 4.1x
                # BLOWUP caused by the feature that exists to save context, with
                # /health green throughout. Same signature as D3/D4: healthy
                # dashboard, work paid for, no effect.
                #
                # Over-skipping is harmless here: only `match_end` determines the
                # injection point, so skipping a message that was not actually
                # pinned costs nothing. Under-skipping breaks matching entirely.
                start = 2
                while start < len(summarized) and compressor._effective_pinned(summarized[start]):
                    start += 1
        key_hashes = _hash_messages(summarized[start:])
        entry["pending"] = prefix
        entry["pending_hashes"] = key_hashes
        entry["_debug_messages"] = summarized[start:]  # for mismatch debugging
        log.info(
            f"[BG] Compression ready: "
            f"{compressor._count_chars(prefix):,} chars "
            f"({len(prefix)} prefix messages, key={len(key_hashes)} hashes, "
            f"summarized {len(summarized) - start} messages)"
        )
    except Exception as e:
        _compression_failed_at = time.time()
        log.error(
            f"[BG] Compression failed (cooling down {FAILURE_COOLDOWN}s): {e}",
            exc_info=True,
        )
        entry["pending"] = None


class ProxyHandler(BaseHTTPRequestHandler):
    """Handle HTTP requests, proxy to upstream API."""
    protocol_version = "HTTP/1.1"

    def log_message(self, format, *args):
        pass

    def _read_body(self) -> bytes:
        length = int(self.headers.get("content-length", 0))
        return self.rfile.read(length) if length > 0 else b""

    def _get_headers_dict(self) -> dict:
        return {key: value for key, value in self.headers.items()}

    def _proxy_raw(self, method: str):
        """Raw proxy — forward request and stream response back."""
        body = self._read_body()
        headers = _forward_headers(self._get_headers_dict(), body if body else None)

        log.info(f"[RAW] {method} {self.path} -> {UPSTREAM_URL} (body={len(body)} bytes)")

        try:
            conn = _upstream_conn()
            upstream_full_path = _join_path(UPSTREAM_PATH, self.path)
            conn.request(method, upstream_full_path, body=body if body else None, headers=headers)
            resp = conn.getresponse()

            log.info(f"[RAW] Response: {resp.status} {resp.reason}")

            self.send_response(resp.status)
            resp_headers = resp.getheaders()
            log.debug(f"[RAW] Response headers: {resp_headers}")
            has_content_length = False
            for key, value in resp_headers:
                lower = key.lower()
                if lower in ("connection", "transfer-encoding"):
                    continue
                if lower == "content-length":
                    has_content_length = True
                self.send_header(key, value)
            if not has_content_length:
                self.send_header("Connection", "close")
            self.end_headers()

            total_bytes = 0
            while True:
                chunk = resp.read(8192)
                if not chunk:
                    break
                self.wfile.write(chunk)
                self.wfile.flush()
                total_bytes += len(chunk)

            log.info(f"[RAW] Done streaming {total_bytes:,} bytes")
            conn.close()
        except Exception as e:
            log.error(f"[RAW] Upstream error: {e}", exc_info=True)
            error_body = json.dumps({"error": str(e)}).encode()
            self.send_response(502)
            self.send_header("content-type", "application/json")
            self.send_header("content-length", str(len(error_body)))
            self.end_headers()
            self.wfile.write(error_body)

    def do_GET(self):
        log.info(f"[REQ] GET {self.path}")
        parsed = urlparse(self.path)
        normalized_path = parsed.path
        if normalized_path == "/health":
            self._handle_health()
        elif normalized_path == "/debug/compressions":
            self._handle_debug_compressions()
        else:
            self._proxy_raw("GET")

    def do_POST(self):
        log.info(f"[REQ] POST {self.path}")
        # Vibe routes ALL traffic through api_base, not just completions: measured
        # /v1/connectors/bootstrap and several /v1/datalake/events per turn. Only
        # the completion call is rewritten; everything else must pass through
        # untouched, and must never 502 — vibe surfaces a failed telemetry post.
        if self.path.startswith("/v1/chat/completions"):
            self._handle_messages()
        elif urlparse(self.path).path == "/pin":
            self._handle_mint_pin()
        else:
            self._proxy_raw("POST")

    def _send_json(self, status: int, payload: dict):
        """Send a JSON body. Used by /pin; /health predates it and builds its own."""
        body = json.dumps(payload).encode()
        self.send_response(status)
        self.send_header("content-type", "application/json")
        self.send_header("content-length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _handle_mint_pin(self):
        """Mint an authenticated pin SPAN for a body of text.

            POST /pin  {"text": "remember the port is 5590"}
            -> {"tagged": "[PIN:9f2c…]remember the port is 5590[/PIN]", "tag": "9f2c…"}

        Paste `tagged` anywhere inside a message you send — it no longer has to be
        the whole message (defect D-P) — and exactly that span is retained across
        every compression round.

        ROLE IS FIXED AT "user" AND THE ROUTE WILL NOT MINT ANY OTHER (D-O). The
        MAC commits to the role of the message that carries the tag, and
        `_pin_eligible` refuses non-user roles structurally, so an assistant-role
        tag would be a tag that can never work: a silent no-op, which is exactly
        defect D3's failure class. Asking for one is a 400 that says why.

        THIS ROUTE IS NOT AN AUTHENTICATION BOUNDARY, and the previous version of
        this docstring claimed it was ("the model … has no way to reach this route
        or read PIN_SECRET"). Both halves are false and were measured in review 5:
        every caveman agent has `bash`, the route is unauthenticated on loopback,
        and `state/pin-secret` is a mode-0644 file under the user profile that any
        such agent can simply read and HMAC with. The rate limit below bounds
        automated abuse and makes it visible in the log; it does not stop a
        determined tool-capable caller, and nothing here can. What contains that
        caller is structural: `_pin_eligible`, span-scoped retention, and the loud
        `pinBudget` refusal.
        """
        if not _pin_rate_limit_ok():
            log.warning("[PIN] /pin rate limit exceeded (%d mints/%ds); refusing",
                        _PIN_RATE_MAX, _PIN_RATE_WINDOW)
            self._send_json(429, {
                "error": f"rate limit: at most {_PIN_RATE_MAX} pins per "
                         f"{_PIN_RATE_WINDOW}s",
            })
            return
        try:
            length = int(self.headers.get("Content-Length") or 0)
            body = json.loads(self.rfile.read(length) or b"{}")
            text = (body.get("text") or "").strip()
            role = body.get("role") or "user"
        except (ValueError, json.JSONDecodeError) as exc:
            self._send_json(400, {"error": f"bad request: {exc}"})
            return
        if not text:
            self._send_json(400, {"error": "field 'text' is required and must be non-empty"})
            return
        if role != "user":
            self._send_json(400, {
                "error": f"role {role!r} is not pinnable; only 'user' is. A tag "
                         f"minted for any other role would verify against nothing "
                         f"and silently do nothing (D-O). Quote the text in a user "
                         f"message instead.",
            })
            return
        from compressor import _mint_tag, TAG_PIN, PIN_OPEN, PIN_CLOSE
        tag = _mint_tag(TAG_PIN, "user", text)
        self._send_json(200, {
            "tag": tag,
            "role": "user",
            "tagged": f"{PIN_OPEN}{tag}]{text}{PIN_CLOSE}",
            "note": "paste 'tagged' anywhere inside a user message; the bare "
                    "marker alone is inert, and only the span between the "
                    "delimiters is retained",
        })

    def do_PUT(self):
        log.info(f"[REQ] PUT {self.path}")
        self._proxy_raw("PUT")

    def do_DELETE(self):
        log.info(f"[REQ] DELETE {self.path}")
        self._proxy_raw("DELETE")

    def do_PATCH(self):
        log.info(f"[REQ] PATCH {self.path}")
        self._proxy_raw("PATCH")

    def do_OPTIONS(self):
        log.info(f"[REQ] OPTIONS {self.path}")
        self._proxy_raw("OPTIONS")

    def _handle_debug_compressions(self):
        entries = []
        for i, entry in enumerate(store.compressions):
            info = {
                "index": i,
                "hash_chain_length": len(entry.get("original_hashes") or []),
                "has_prefix": entry["prefix"] is not None,
                "prefix_content": None,
            }
            if entry["prefix"]:
                # The marker EMITTED carries an HMAC tag, so it is
                # `[ROLLING_CONTEXT_SUMMARY:<hex>]`, never the bare constant. This
                # tested for the bare form and therefore reported
                # `prefix_content: null` for every entry since the D-D fix — a
                # debug route that silently shows nothing. Match the prefix.
                from compressor import SUMMARY_MARKER
                _emitted = SUMMARY_MARKER[:-1] + ":"
                for msg in entry["prefix"]:
                    content = msg.get("content", "")
                    if isinstance(content, str) and _emitted in content:
                        info["prefix_content"] = content
            entries.append(info)
        body = json.dumps(entries, indent=2).encode()
        self.send_response(200)
        self.send_header("content-type", "application/json")
        self.send_header("content-length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _handle_health(self):
        active = sum(
            1 for e in store.compressions
            if e["thread"] is not None and e["thread"].is_alive()
        )
        from compressor import NATIVE_MODE, SUMMARIZER_FORMAT, PIN_MARKER
        data = {
            "status": "ok",
            "trigger_tokens": TRIGGER_TOKENS,
            "target_tokens": TARGET_TOKENS,
            # REVIEW-6 DEFECT R6-1: this was `SUMMARIZER_MODEL or "(session
            # model)"`, which is a claim about _summarize_native. Production runs
            # flattened/openai, where _summarize_flattened ignores the payload and
            # always sends LEGACY_DEFAULT_MODEL. Measured live on 5590 AND 5591
            # AFTER the review-5 model fix: both still answered "(session model)"
            # while every summarizer call went out as mistral-large-2512. Derive
            # the answer from the send path instead of restating an intention.
            "summarizer_model": compressor.effective_summarizer_model(),
            # Kept separately so "nothing was configured" stays visible rather
            # than being hidden behind the resolved value.
            "summarizer_model_configured": SUMMARIZER_MODEL or None,
            "summarizer_mode": "native" if NATIVE_MODE else f"flattened/{SUMMARIZER_FORMAT}",
            "upstream_url": UPSTREAM_URL,
            "compression_count": compressor.compression_count,
            "total_tokens_saved": compressor.total_tokens_saved,
            "stored_compressions": len(store.compressions),
            "active_compressions": active,
            # Refusals are part of the status, not just the log. A compressor
            # that declines every request looks identical to a healthy idle one
            # from the outside — that WAS defect D3, for weeks.
            "refusal_counts": compressor.refusal_counts,
            "last_refusal": compressor.last_refusal,
            "pin_marker": PIN_MARKER,
            # Two lists on purpose (defect D-H): `pin_rejections` ACCUMULATES, so a
            # refusal raised three calls ago is still visible; `pin_rejections_last`
            # is the most recent call only. Reporting just the latter made "no pin
            # was ever refused" look identical to "one was refused a moment ago".
            "pin_rejections": compressor.pin_rejections,
            "pin_rejections_last": compressor.pin_rejections_last,
            # Pins are HMAC-authenticated; a bare marker is inert (defects D-C/D-D).
            # REVIEW-6: was the bare literal "hmac". Now DERIVED by exercising the
            # shipped verifier (accepts a minted tag, refuses a forged one), so a
            # future degraded path is reported here instead of hidden by a literal.
            "pin_auth": compressor.pin_auth_scheme(),
        }
        body = json.dumps(data).encode()
        self.send_response(200)
        self.send_header("content-type", "application/json")
        self.send_header("content-length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _handle_messages(self):
        # AUDIT-FIX (defect 1): the [PROACTIVE] block below ASSIGNS
        # _compression_failed_at in its except handler. Without this declaration
        # that assignment makes the name function-local for the WHOLE method, so
        # the READ at the top of the proactive block raises
        #   UnboundLocalError: cannot access local variable '_compression_failed_at'
        # the first time the trigger is crossed — before anything is forwarded.
        # The handler thread dies, the socket closes with no response, and vibe
        # reports "Server disconnected without sending a response". Measured live:
        # trigger=2000, 6-message/117,577-char request, server.py:739.
        # _do_background_compression already declares this global; the proactive
        # block was ported from the GLM fork without it.
        global _compression_failed_at
        raw_body = self._read_body()
        req_headers = self._get_headers_dict()
        auth_headers = get_passthrough_headers(req_headers)

        log.info(f"[MSG] POST {self.path} (body={len(raw_body)} bytes)")
        log.debug(f"[MSG] Request headers: {list(req_headers.keys())}")

        try:
            payload = json.loads(raw_body)
        except json.JSONDecodeError:
            log.error("[MSG] Invalid JSON in request body")
            error_body = b'{"error":"Invalid JSON"}'
            self.send_response(400)
            self.send_header("content-length", str(len(error_body)))
            self.end_headers()
            self.wfile.write(error_body)
            return

        messages = payload.get("messages", [])
        is_streaming = payload.get("stream", False)
        model = payload.get("model", "unknown")

        # Hash all messages for content-based matching
        msg_hashes = _hash_messages(messages)
        msg_chars = compressor._count_chars(messages)

        log.info(
            f"[MSG] model={model} stream={is_streaming} "
            f"messages={len(messages)} chars={msg_chars:,}"
        )

        # Promote any pending compressions
        for entry in store.compressions:
            if entry["pending"] is not None:
                entry["prefix"] = entry["pending"]
                entry["original_hashes"] = entry["pending_hashes"]
                entry["pending"] = None
                entry["pending_hashes"] = None
                log.info(
                    f"[MSG] Compression promoted: {len(entry['prefix'])} prefix messages "
                    f"replacing {len(entry['original_hashes'])} originals"
                )

        # Scan: do any stored compressions match this request's messages?
        match, match_end = store.find_match(msg_hashes, messages)
        injected = False

        sys_head = _system_prefix_len(messages)

        if match and match["prefix"] is not None and match_end > sys_head:
            # Replace everything up to match_end with the prefix
            # (prefix contains summary of everything before it)
            #
            # PORT: messages[:sys_head] is re-attached in the merge below. Upstream
            # wrote `merged = prefix + new_messages`, which is correct when system
            # travels out-of-band and WRONG here — it would drop vibe's system
            # message. Guarded by match_end > sys_head so a match that somehow
            # begins inside the system prefix is refused instead of half-applied.
            new_messages = messages[match_end:]

            # Strip cache_control from injected prefix messages ONLY.
            # The verbatim tail keeps Claude Code's cache_control breakpoints —
            # stripping those disabled prompt caching entirely, so every request
            # after the first injection paid full input-token cost (issue #1/#4).
            for msg in match["prefix"]:
                content = msg.get("content", "")
                if isinstance(content, list):
                    for block in content:
                        if isinstance(block, dict):
                            block.pop("cache_control", None)

            merged = messages[:sys_head] + match["prefix"] + new_messages
            merged = _validate_tool_pairs(merged)

            merged_chars = compressor._count_chars(merged)
            if merged_chars < msg_chars:
                log.info(
                    f"[MSG] Injecting: {msg_chars:,} -> {merged_chars:,} chars "
                    f"({len(messages)} -> {len(merged)} messages, "
                    f"replaced 0-{match_end} with {len(match['prefix'])} prefix "
                    f"+ {len(new_messages)} new)"
                )
                payload["messages"] = merged
                msg_chars = merged_chars
                injected = True
            else:
                log.info(
                    f"[MSG] Compression no longer helps: "
                    f"merged={merged_chars:,} >= current={msg_chars:,} chars, removing"
                )
                store.remove(match)
                match = None

        # Save current state for post-response compression trigger
        current_messages = payload.get("messages", messages)

        # ---- PROACTIVE synchronous compression (pre-forward) ----
        # Ported from the GLM fork of this plugin, and it is REQUIRED here, not an
        # optimisation.
        #
        # Upstream compresses REACTIVELY: it reads the token count off the response
        # and spawns a background job for the NEXT request. So the request that
        # first crosses the trigger is forwarded FULL-SIZE. Vibe then sees the true
        # count — vibe/core/agent_loop/_loop.py:2219 sets context_tokens straight
        # from usage.prompt_tokens — and vibe/core/middleware.py:104 fires its OWN
        # compaction at auto_compact_threshold. Native compaction wins the race and
        # replaces the WHOLE conversation with a lossy summary, which is precisely
        # what this proxy exists to prevent.
        #
        # Compressing synchronously before forwarding means upstream only ever
        # reports the compressed count, so vibe's tracker never crosses its own line.
        # Belt and braces: the generated config also sets auto_compact_threshold = 0.
        if not injected and len(current_messages) >= 6:
            est_tokens = msg_chars // 4  # same basis as the fallback estimate below
            if est_tokens > TRIGGER_TOKENS:
                already_compressing = any(
                    e["thread"] is not None and e["thread"].is_alive()
                    for e in store.compressions
                )
                cooldown_left = FAILURE_COOLDOWN - (time.time() - _compression_failed_at)
                if not already_compressing and cooldown_left <= 0:
                    log.info(
                        f"[PROACTIVE] Request ~{est_tokens:,} tokens > trigger "
                        f"{TRIGGER_TOKENS:,}; compressing synchronously before forward..."
                    )
                    try:
                        result = compressor.compress_ex(
                            current_messages, auth_headers,
                            real_token_count=est_tokens, payload=payload,
                        )
                        if result.ok:
                            # Reported, not re-derived: see the same fix in
                            # _do_background_compression. With hard memory the old
                            # `len(current_messages) - (len(compressed) - 2)` is
                            # wrong, because pinned messages are in the result but
                            # are not part of the verbatim tail.
                            tail_start = result.cut_index
                            # PORT: floor the summarized span at the system prefix.
                            summarized = current_messages[sys_head:tail_start]
                            from compressor import SUMMARY_MARKER
                            start = 0
                            if summarized and isinstance(summarized[0].get("content", ""), str) \
                                    and compressor._is_synthetic(summarized[0]):  # AUTHENTICATED, see twin above
                                # DEFECT D-A, second site. Identical reasoning to the
                                # twin in _do_background_compression: with hard memory
                                # the prefix is [summary, ack] + pinned_kept, so a bare
                                # `start = 2` leaves the key chain beginning on a pinned
                                # message and it can never match. The cut_index half of
                                # this defect class was fixed 20 lines above at the
                                # AUDIT-FIX comment; this hashing half was missed.
                                start = 2
                                while start < len(summarized) and compressor._effective_pinned(summarized[start]):
                                    start += 1
                            key_hashes = _hash_messages(summarized[start:])
                            merged = (current_messages[:sys_head]
                                      + result.prefix
                                      + current_messages[tail_start:])
                            merged = _validate_tool_pairs(merged)
                            merged_chars = compressor._count_chars(merged)
                            if merged_chars < msg_chars:
                                payload["messages"] = merged
                                msg_chars = merged_chars
                                injected = True
                                # Store so the NEXT request matches and injects
                                # without paying for another compression.
                                entry = store.add()
                                entry["prefix"] = result.prefix
                                entry["original_hashes"] = key_hashes
                                entry["_debug_messages"] = summarized[start:]
                                current_messages = merged
                                log.info(
                                    f"[PROACTIVE] Compressed inline: "
                                    f"{len(messages)} -> {len(merged)} messages, "
                                    f"~{est_tokens:,} -> ~{merged_chars // 4:,} est tokens; "
                                    f"stored (key={len(key_hashes)} hashes, "
                                    f"system prefix {sys_head} preserved)"
                                )
                            else:
                                log.info(
                                    "[PROACTIVE] Inline compression did not shrink "
                                    f"(merged={merged_chars:,} >= current={msg_chars:,} chars); "
                                    "forwarding as-is"
                                )
                        else:
                            # Named refusal, not a bare None. `pinBudget` in
                            # particular means the user must unpin something —
                            # nothing the proxy retries will ever fix it.
                            log.info(
                                f"[PROACTIVE] Declined ({result.refusal}): "
                                f"{result.detail}; forwarding as-is"
                            )
                    except Exception as e:
                        _compression_failed_at = time.time()
                        log.error(
                            f"[PROACTIVE] Synchronous compression failed "
                            f"(cooling down {FAILURE_COOLDOWN}s): {e}",
                            exc_info=True,
                        )

        # Forward request — strip Accept-Encoding so we get plain text SSE
        body = json.dumps(payload).encode()
        headers = _forward_headers(req_headers, body, strip_encoding=True)

        log.info(f"[MSG] Forwarding to {UPSTREAM_URL}{self.path} ({len(body):,} bytes)")

        try:
            conn = _upstream_conn()
            upstream_full_path = _join_path(UPSTREAM_PATH, self.path)
            conn.request("POST", upstream_full_path, body=body, headers=headers)
            resp = conn.getresponse()

            log.info(f"[MSG] Upstream response: {resp.status} {resp.reason}")

            self.send_response(resp.status)
            resp_headers = resp.getheaders()
            log.debug(f"[MSG] Response headers: {resp_headers}")
            has_content_length = False
            for key, value in resp_headers:
                lower = key.lower()
                if lower in ("connection", "transfer-encoding"):
                    continue
                if lower == "content-length":
                    has_content_length = True
                self.send_header(key, value)
            if not has_content_length:
                self.send_header("Connection", "close")
            self.end_headers()

            log.info(f"[MSG] Streaming response...")

            # Stream response and capture SSE token data
            buffer = b""
            total_bytes = 0
            total_input = 0
            while True:
                chunk = resp.read(8192)
                if not chunk:
                    break
                self.wfile.write(chunk)
                self.wfile.flush()
                total_bytes += len(chunk)
                # PORT: upstream buffered ONLY when streaming, so its own
                # `elif not is_streaming and buffer:` branch below was unreachable
                # — harmless for Claude Code, which always streams. Vibe's headless
                # `-p` mode sends stream:false (measured), so without this the real
                # token count is never read and the proxy silently runs on the
                # chars//4 estimate forever.
                buffer += chunk

            log.info(f"[MSG] Done streaming {total_bytes:,} bytes")

            # Extract input tokens from SSE stream
            if is_streaming and buffer:
                try:
                    text = buffer.decode("utf-8", errors="replace")
                    for line in text.split("\n"):
                        if not line.startswith("data: "):
                            continue
                        data_str = line[6:]
                        if data_str == "[DONE]":
                            continue
                        try:
                            data = json.loads(data_str)
                        except json.JSONDecodeError:
                            continue
                        # PORT: Anthropic's `message_start` / `message_delta` event
                        # types do not exist here. Mistral streams
                        # `chat.completion.chunk` objects and attaches usage to a
                        # late chunk (vibe asks for it via
                        # stream_options={"include_usage": True},
                        # vibe/core/llm/backend/generic.py:142-145).
                        #
                        # REVIEW-6: this branch is no longer [UNVERIFIED-STREAM].
                        # It was driven end to end through a fake upstream (proxy
                        # on :5594 -> canned Mistral-shaped SSE on :5597, sole
                        # listener) and the late-chunk usage IS read:
                        #   "Input tokens from stream usage: 31,337"
                        # cached_tokens is correctly NOT summed (it is a subset).
                        #
                        # RETRACTION, and it is recorded because the false finding
                        # was briefly committed to this file as "DEFECT R6-5".
                        # I claimed the fallback below "estimates from the RESPONSE
                        # buffer, so it cannot approximate input size at all: a
                        # ~31,000x undercount". THAT WAS WRONG, and it was an
                        # artifact of my own test design: the fake upstream planted
                        # prompt_tokens=31337 while the probe request was the
                        # 4-char string "ping". The 31,000x gap was between a
                        # fabricated usage value and a tiny real request -- it
                        # measured my fixture, not this code.
                        #
                        # The fallback reads `msg_chars`, which is
                        # `compressor._count_chars(messages)` over the REQUEST
                        # (line ~1020), exactly as it should. RE-MEASURED on a
                        # realistic request: 40,000 request chars -> "estimating
                        # from chars: 40,000 chars -> ~10,000 tokens". Proportionate.
                        # The ORIGINAL port comment -- "a wrong guess here degrades
                        # accuracy, not correctness" -- was CORRECT and is restored
                        # in substance. Residual question is only chars//4 versus
                        # real tokenization (order 1.2-1.5x), unmeasured without a
                        # live key, and it degrades accuracy, not correctness.
                        #
                        # Lesson worth more than the finding: a probe whose fixture
                        # asserts a value the system under test cannot corroborate
                        # measures the fixture. Size the request to the claim.
                        usage = data.get("usage") or {}
                        tokens = int(usage.get("prompt_tokens", 0) or 0)
                        if tokens > total_input:
                            total_input = tokens
                            log.info(f"[MSG] Input tokens from stream usage: {total_input:,}")

                    if total_input == 0:
                        sse_lines = [l for l in text.split("\n") if l.startswith("data: ")]
                        log.warning(
                            f"[MSG] No input tokens found in SSE! "
                            f"Total events: {len(sse_lines)}"
                        )
                except Exception as e:
                    log.warning(f"[MSG] Failed to parse SSE for tokens: {e}")
            elif not is_streaming and buffer:
                try:
                    data = json.loads(buffer)
                    usage = data.get("usage", {})
                    # PORT: Mistral reports `prompt_tokens` and it is ALREADY the
                    # full billed input — cached tokens are a *subset*, reported
                    # separately under prompt_tokens_details.cached_tokens for
                    # information. Upstream SUMMED Anthropic's three fields because
                    # there they are disjoint. Summing here would double-count the
                    # cached portion and trip the trigger early.
                    # Measured: {"prompt_tokens":6394,...,"cached_tokens":2080}.
                    total_input = int(usage.get("prompt_tokens", 0) or 0)
                    if total_input > 0:
                        cached = (usage.get("prompt_tokens_details") or {}).get("cached_tokens", 0)
                        log.info(
                            f"[MSG] Input tokens from response: {total_input:,} "
                            f"(of which cached: {cached:,})"
                        )
                except Exception as e:
                    log.warning(f"[MSG] Failed to parse response for tokens: {e}")

            conn.close()

            # Fallback: estimate tokens from chars if SSE didn't provide usage
            if total_input == 0 and msg_chars > 0:
                total_input = msg_chars // 4  # rough chars-to-tokens estimate
                log.info(
                    f"[MSG] No tokens from SSE, estimating from chars: "
                    f"{msg_chars:,} chars -> ~{total_input:,} tokens"
                )

            # Trigger compression based on token count. The minimum message
            # count keeps us from "compressing" sessions whose bulk is the
            # system prompt / first-message context, which we can't remove.
            if total_input > 0 and total_input > TRIGGER_TOKENS and len(current_messages) >= 6:
                already_compressing = any(
                    e["thread"] is not None and e["thread"].is_alive()
                    for e in store.compressions
                )
                cooldown_left = FAILURE_COOLDOWN - (time.time() - _compression_failed_at)
                if already_compressing:
                    pass
                elif cooldown_left > 0:
                    log.info(
                        f"[MSG] Over trigger but last compression failed — "
                        f"cooling down another {cooldown_left:.0f}s"
                    )
                else:
                    log.info(
                        f"[MSG] API reported {total_input:,} tokens (trigger: {TRIGGER_TOKENS:,}). "
                        f"Compressing in background..."
                    )
                    entry = store.add()
                    t = threading.Thread(
                        target=_do_background_compression,
                        args=(entry, current_messages, auth_headers),
                        kwargs={"real_token_count": total_input, "payload": payload},
                        daemon=True,
                    )
                    t.start()
                    entry["thread"] = t

        except Exception as e:
            log.error(f"[MSG] Upstream error: {e}", exc_info=True)
            error_body = json.dumps({"error": str(e)}).encode()
            self.send_response(502)
            self.send_header("content-type", "application/json")
            self.send_header("content-length", str(len(error_body)))
            self.end_headers()
            self.wfile.write(error_body)


class ThreadedHTTPServer(HTTPServer):
    """Handle each request in a new thread."""
    def process_request(self, request, client_address):
        t = threading.Thread(target=self._handle, args=(request, client_address))
        t.daemon = True
        t.start()

    def _handle(self, request, client_address):
        try:
            self.finish_request(request, client_address)
        except Exception:
            self.handle_error(request, client_address)
        finally:
            self.shutdown_request(request)


def main():
    from compressor import NATIVE_MODE, SUMMARIZER_FORMAT
    log.info(f"Starting Rolling Context Proxy on port {LISTEN_PORT}")
    log.info(f"  Trigger at: {TRIGGER_TOKENS:,} tokens")
    log.info(f"  Compress down to: {TARGET_TOKENS:,} tokens (recent context)")
    # REVIEW-6 DEFECT R6-1, second site. Same false claim as /health; the banner
    # is what a reader greps when the dashboard is not up, so both must agree
    # with the send path rather than with each other.
    log.info(f"  Summarizer model: {compressor.effective_summarizer_model()}")
    log.info(f"  Summarizer mode: "
             f"{'native (cloned session request, prompt-cached)' if NATIVE_MODE else f'flattened/{SUMMARIZER_FORMAT}'}")
    log.info(f"  Forwarding to: {UPSTREAM_URL}")
    log.info(f"  Matching: content-based (no sessions/fingerprints)")

    server = ThreadedHTTPServer(("127.0.0.1", LISTEN_PORT), ProxyHandler)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        log.info("Shutting down...")
        server.shutdown()


if __name__ == "__main__":
    main()
