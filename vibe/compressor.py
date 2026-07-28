# SPDX-FileCopyrightText: 2026 Saimono / Nova-Violet Role
# SPDX-License-Identifier: AGPL-3.0-or-later OR EUPL-1.2

"""
Rolling Context Compressor

When context exceeds trigger_tokens, compresses old messages down to target_tokens
of recent context + a dense chronological summary of everything before.

Two summarization modes:

1. NATIVE (default): clones the exact request Claude Code just sent — same
   model, system prompt, tools, and message history up to the cut point — and
   appends one user message asking for the summary. Because the request is
   byte-identical Claude Code session traffic, it passes Anthropic's
   subscription OAuth classification (issue #4), and because the prefix was
   just sent by the chat request, it's a prompt-cache read instead of full
   input cost.

2. FLATTENED: used when a custom summarizer is configured
   (ROLLING_CONTEXT_SUMMARIZER_URL / _KEY / _FORMAT). Flattens the
   conversation to text and sends a standalone request — Anthropic format or
   OpenAI chat-completions format, so any local model or third-party API
   works (Ollama, LM Studio, vLLM, OpenRouter, DeepSeek, ...).

Pure stdlib — no external dependencies.
"""

import copy
import gzip
import hashlib
import hmac
import json
import os
import re
import secrets
import ssl
import logging
import http.client
from urllib.parse import urlparse

log = logging.getLogger("rolling-context.compressor")

_default_summarizer_url = (
    os.environ.get("ROLLING_CONTEXT_VIBE_UPSTREAM") or "https://api.mistral.ai"
)
# _VIBE_-scoped for the same reason as server.py's knobs: the unscoped names are
# live in this user's environment from the Claude-side install.
SUMMARIZER_URL_SET = bool(os.environ.get("ROLLING_CONTEXT_VIBE_SUMMARIZER_URL"))
SUMMARIZER_BASE_URL = (
    os.environ.get("ROLLING_CONTEXT_VIBE_SUMMARIZER_URL") or _default_summarizer_url
)
SUMMARIZER_API_KEY = os.environ.get("ROLLING_CONTEXT_VIBE_SUMMARIZER_KEY") or ""
# PORT: default flipped "anthropic" -> "openai". Mistral IS the openai
# chat-completions shape, and this path already existed upstream for third-party
# APIs — it is reused as-is rather than rewritten.
SUMMARIZER_FORMAT = (
    os.environ.get("ROLLING_CONTEXT_VIBE_SUMMARIZER_FORMAT") or "openai"
).lower()

# PORT: NATIVE mode is OFF here, and not merely by default — it is unusable.
# It clones the session request to /v1/messages (Anthropic) and parses Anthropic
# SSE back. Both are wrong for Mistral. Upstream's own rule already disables it the
# moment a custom summarizer is configured, and setting FORMAT=openai above trips
# exactly that rule, so no logic change is needed — only this note, because a future
# reader flipping FORMAT back to "anthropic" would silently re-enable a broken path.
#
# Cost of losing NATIVE: it re-sent the session prefix for a prompt-cache read.
# Mistral does report cached tokens (measured: cached_tokens 2080), so porting
# NATIVE against /v1/chat/completions is a real phase-2 win — not a phase-1 need.
NATIVE_MODE = not (SUMMARIZER_URL_SET or SUMMARIZER_API_KEY or SUMMARIZER_FORMAT != "anthropic")

# PORT: was claude-haiku. Cheap Mistral tier, shipped in vibe's own DEFAULT_MODELS
# (vibe/core/config/vibe_schema.py:130-137, in/out $0.1/$0.3).
# MODEL MAP (2026-07-27): was "devstral-small-latest". Measured against the live
# API: that id is ABSENT from the 60 models the key can reach, yet POST returns
# 200 — Mistral silently serves `devstral-latest` (= Devstral 2, `devstral-2512`),
# RETIREMENT 2026-07-31. Every summary in a `flattened` run was being written by
# a model nobody chose and which stops answering this week; when it does, the
# summarizer call fails and compression stops entirely.
#
# Caught by a 20,000/5,000 scratch run: at the production 220,000 trigger the
# summarizer fires so rarely that this path stayed dark through four audits.
# `/health` reported `summarizer_model: "(session model)"` the whole time, which
# is true of _summarize (line ~967, `payload.get("model", ...)`) but FALSE of
# _summarize_flattened below, which never consults the payload. SUMMARIZER_MODEL
# is "" by default and `summarizer_mode` is flattened, so the flattened path is
# the one production takes.
#
# Now Mistral Large 3, PINNED to a dated id — a floating `-latest` alias is a
# model substitution you cannot see. Summarizing is read-heavy, single-shot and
# tool-free, which is where Large 3 is strongest per dollar ($0.5/$1.5 per M vs
# Medium 3.5's $1.5/$7.5). Verified reachable: 262,144 ctx, function_calling True.
LEGACY_DEFAULT_MODEL = "mistral-large-2512"

ssl_ctx = ssl.create_default_context()

_parsed_summarizer = urlparse(SUMMARIZER_BASE_URL)
_SUMMARIZER_HOST = _parsed_summarizer.hostname
_SUMMARIZER_PORT = _parsed_summarizer.port
_SUMMARIZER_SCHEME = _parsed_summarizer.scheme
_SUMMARIZER_PATH = _parsed_summarizer.path or ""


def _summarizer_conn(timeout=600):
    """Create a connection to the summarizer server (same style as server.py)."""
    if _SUMMARIZER_SCHEME == "https":
        return http.client.HTTPSConnection(
            _SUMMARIZER_HOST,
            _SUMMARIZER_PORT or 443,
            context=ssl_ctx,
            timeout=timeout,
        )
    else:
        return http.client.HTTPConnection(
            _SUMMARIZER_HOST,
            _SUMMARIZER_PORT or 80,
            timeout=timeout,
        )


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

def _clean_headers(headers: dict) -> dict:
    """Drop hop-by-hop/stale headers case-insensitively. The passthrough
    headers keep Claude Code's original casing (e.g. Accept-Encoding), so
    plain dict assignment of 'accept-encoding' would DUPLICATE the header and
    the upstream would still gzip the response."""
    drop = ("accept-encoding", "content-length", "host", "transfer-encoding", "connection")
    return {k: v for k, v in headers.items() if k.lower() not in drop}


SUMMARY_MARKER = "[ROLLING_CONTEXT_SUMMARY]"
SUMMARY_END_MARKER = "[/ROLLING_CONTEXT_SUMMARY]"

# --- HARD MEMORY -------------------------------------------------------------
# Formalized in D:\Lean\proofs\Proofs\Compressor.lean section 5. Read that file
# before changing anything below; `check-compressor-drift.py` fails the build if
# the two disagree.
#
# A message carrying PIN_MARKER (or an explicit "pinned": true) is retained
# VERBATIM across every compression round. Retention is structural, not a request
# made of the summarizer: pinned messages are carried over the summary boundary
# the same way the system prefix already is, so no threshold, no summarizer
# prompt and no number of rounds can erode them. That is `pinned_never_cut`.
#
# Eligibility is narrow ON PURPOSE (`pinEligible`):
#   - role "system"                   : already in the never-cut head, and
#                                       hoisting one breaks the API's
#                                       "system follows user, precedes assistant".
#   - role "tool" / assistant with
#     tool_calls                      : hoisting either half of a tool-call group
#                                       orphans the other half. Mistral rejects
#                                       that with a hard 400 - a wedged session,
#                                       not a degraded one.
#   - the proxy's own summary / ack   : a summary that quoted the marker would
#                                       pin ITSELF, be retained verbatim AND
#                                       regenerated every round - an unbounded
#                                       stack of summaries. See
#                                       `synthetic_never_pinned`.
#
# An ineligible pin is REPORTED (`pin_rejections`, surfaced on /health), never
# silently dropped: a pin that quietly does nothing is defect D3's failure class
# all over again - healthy logs, no effect.
PIN_MARKER = os.environ.get("ROLLING_CONTEXT_VIBE_PIN_MARKER") or "[PIN]"

# A pin is a DELIMITED SPAN, not a message prefix (defect D-P, review 5):
#   [PIN:<16 hex>]  ...the pinned text...  [/PIN]
# The MAC covers exactly the text between the two, so a pin can sit INLINE in a
# longer message. Before this it covered the whole message body, which meant a
# pin authenticated only when the pinned text was the ENTIRE message - measured:
# pasting a valid pin into a longer message was rejected `unauthenticated`, which
# made pins unusable under `vibe -p` where the prompt is one message.
PIN_OPEN = PIN_MARKER[:-1] + ":"                    # "[PIN:"
PIN_CLOSE = PIN_MARKER[0] + "/" + PIN_MARKER[1:]    # "[/PIN]"

# --- PIN AUTHENTICATION (defects D-C / D-D / D-N / D-O / D-P) ----------------
# A BARE marker is no longer sufficient to pin anything, and this is a security
# boundary, not a nicety.
#
# MEASURED before this change: `_is_pinned` substring-matched PIN_MARKER over
# user AND assistant text, so an assistant reply containing "[PIN]" pinned
# ITSELF - the model could make its own output permanently unforgettable and
# unshrinkable - and a pasted document that merely MENTIONED the marker pinned
# the paste. Six self-pinned assistant turns took compression from useful to
# saving 2% (1,178 of 56,338 chars) without ever tripping pinBudget.
#
# The same "scan attacker-controllable text" root gave a worse one: forging
# SUMMARY_MARKER in the first non-system message made `_has_summary` fire, which
# moves start_idx past two REAL messages. Those two sit inside the replaced span
# but outside the summarizer input, so they were DELETED, never summarized -
# while the forged text was handed to every later summarizer call framed as
# "EXISTING ROLLING SUMMARY ... keep all details".
#
# Both markers are therefore AUTHENTICATED with an HMAC keyed by a secret that
# is not part of the conversation. A bare marker is INERT - and, for pins,
# reported as a rejection with reason `unauthenticated` rather than ignored,
# because a pin that quietly does nothing is D3's failure class again.
#
# WHAT THIS DOES NOT PREVENT - read this before trusting the word "cannot".
# The secret lives in `state/pin-secret`, mode 0644 under the user profile.
# MEASURED (review 5): `head -c 20 state/pin-secret` succeeds as the ordinary
# session user. Every caveman agent has `bash`. So an agent WITH TOOLS can read
# the key and mint any tag it likes; so can it reach `POST /pin` on loopback.
# Against a tool-capable attacker this MAC is worth nothing and no amount of
# domain separation changes that.
#
# The MAC's real threat model is narrower and worth stating exactly: it stops an
# attacker whose only capability is EMITTING TEXT into the conversation - a
# pasted document, a prompt-injected reply, a model with no shell. Everything
# below that survives a tool-capable attacker is STRUCTURAL, not cryptographic:
# eligibility (`_pin_eligible`), span-scoped retention (`_pin_extract`) and the
# loud `pinBudget` refusal.
#
# The secret is persisted (not per-process) so that pins survive a proxy restart.
# A restart that rotated it would silently unpin every already-tagged message -
# the exact silent-no-op class this file keeps having to defend against.
_STATE_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "state")
_PIN_SECRET_PATH = os.path.join(_STATE_DIR, "pin-secret")


def _load_pin_secret() -> bytes:
    """Read the session pin secret, creating it on first use."""
    try:
        os.makedirs(_STATE_DIR, exist_ok=True)
        if os.path.exists(_PIN_SECRET_PATH):
            with open(_PIN_SECRET_PATH, "rb") as fh:
                secret = fh.read().strip()
            if len(secret) >= 32:
                return secret
        secret = secrets.token_hex(32).encode("ascii")
        with open(_PIN_SECRET_PATH, "wb") as fh:
            fh.write(secret)
        try:
            os.chmod(_PIN_SECRET_PATH, 0o600)
        except OSError:
            # Windows ACLs do not map onto chmod; the file still sits under the
            # user profile. Best effort, never fatal.
            pass
        return secret
    except OSError as exc:
        # Never take the proxy down over this. Fall back to a process-local
        # secret: pins stop surviving restarts, which is a usability loss, not a
        # security one, and it is LOGGED rather than silent.
        log.error(f"[PIN] could not persist pin secret ({exc}); using process-local secret")
        return secrets.token_hex(32).encode("ascii")


PIN_SECRET = _load_pin_secret()

TAG_PIN = "pin"
TAG_SUMMARY = "summary"

# `[PIN:<hex>]…[/PIN]` (a SPAN) / `[ROLLING_CONTEXT_SUMMARY:<hex>]` (a prefix).
# The span regex is non-greedy so consecutive spans pair with the nearest close
# rather than swallowing everything between the first open and the last close.
_PIN_SPAN_RE = re.compile(
    re.escape(PIN_OPEN) + r"([0-9a-f]{16})\](.*?)" + re.escape(PIN_CLOSE),
    re.DOTALL,
)
# An OPEN marker with no close. Only used to REPORT `unterminated`, never to
# honour anything: a pin that silently does nothing is defect D3's signature.
_PIN_OPEN_RE = re.compile(re.escape(PIN_OPEN) + r"([0-9a-f]{16})\]")
_SUMMARY_TAG_RE = re.compile(re.escape(SUMMARY_MARKER[:-1]) + r":([0-9a-f]{16})\]")

# vibe injects MODEL-CONTROLLED text into role="user" messages, wrapped in these
# four tags. MEASURED in the installed package (review 5):
#   _loop.py:1499 `_handle_plan_review_ended`  -> the PLAN FILE's contents, which
#                  the model writes, inside <vibe_warning>…</vibe_warning>
#   _loop.py:2413 `_clear_context_after_plan_accept` -> the same
#   _loop.py:1164 middleware INJECT_MESSAGE, agent_loop_hooks.py:429 hook output
# vibe marks these `injected=True`, but that flag is CLIENT-SIDE: the Mistral
# mapper (`backend/mistral.py:81`) emits `UserMessage(role="user", content=…)`
# and nothing else, so the proxy cannot see it on the wire. The four tags CAN be
# seen, so pins are not honoured inside them - that closes the plan-file route by
# which model output reaches a user-role message.
#
# This list is duplicated in vibe-rc-server.py (`_VIBE_TAGS`) because compressor.py
# must import cleanly on its own; check-compressor-drift.py asserts the two agree.
_VIBE_INJECT_TAGS = ("user_cancellation", "tool_error", "vibe_stop_event", "vibe_warning")
_VIBE_INJECT_RE = re.compile(
    r"<(?:" + "|".join(_VIBE_INJECT_TAGS) + r")>.*?</(?:" + "|".join(_VIBE_INJECT_TAGS) + r")>",
    re.DOTALL,
)


def _frame(*parts: str) -> bytes:
    """Netstring-style length prefixing: `len:bytes` per part, concatenated.

    UNAMBIGUOUS BY CONSTRUCTION, which a separator byte is not. The previous
    encoding was `kind || 0x00 || body`, which is injective only while `kind`
    contains no NUL. That held for the two literals `"pin"` / `"summary"`, but
    the MAC now also commits to a ROLE taken straight out of request JSON, where
    a NUL is perfectly legal - `{"role": "user\\u0000x"}` survives `json.loads`.
    With a separator that would let one byte string decode as two different
    (kind, role, body) triples. Length prefixes remove the question instead of
    arguing about which characters are safe.
    """
    out = []
    for p in parts:
        b = p.encode("utf-8", "surrogatepass")
        out.append(str(len(b)).encode("ascii") + b":" + b)
    return b"".join(out)


def _mint_tag(kind: str, role: str, body: str) -> str:
    """HMAC tag over (KIND, ROLE, body).

    Three bindings, each closing a measured hole:

    KIND (domain separation, review 4). Committing to the body alone let one tag
    value authenticate under BOTH markers, so `/pin` became a summary-forgery
    oracle and the proxy's own summary tag could be lifted onto a `[PIN:]` marker.

    ROLE (defect D-O, review 5). MEASURED against the shipped code before this
    change: a valid pin copied verbatim into an ASSISTANT turn authenticated, so
    the model could make its own output permanently unforgettable and
    unshrinkable. Reproduced end to end - a 24-turn conversation went from 82.4%
    compressed to 13.5%, with 110,928 chars of model output pinned. The role of
    the message CARRYING the tag is now part of the MAC, so the copy verifies
    against role "assistant" and fails. `/pin` only mints role "user".

    BODY encoding (defect D-M, review 4): `errors="replace"` is MANY-TO-ONE, so
    `_mint_tag(…, "\\ud800")` equalled `_mint_tag(…, "?")` - two bodies, one valid
    MAC. `surrogatepass` is injective on the code-point sequence.

    Role binding is defence in depth, NOT the primary control: `_pin_eligible`
    also refuses assistant messages structurally, and that refusal survives an
    attacker who can read the secret. See the header comment.
    """
    return hmac.new(PIN_SECRET, _frame(kind, role, body), hashlib.sha256).hexdigest()[:16]


def _pin_scan_text(text: str) -> str:
    """Message text with vibe's injected regions removed, for pin scanning only."""
    return _VIBE_INJECT_RE.sub("", text)


def _verified_pin_spans(text: str, role: str) -> list:
    """Every `[PIN:…]…[/PIN]` span in `text` whose MAC this proxy minted for `role`.

    Returned WITH their delimiters, so the extracted message re-verifies on the
    next round (`_pin_extract` is idempotent - the drift checker executes that).

    `hmac.compare_digest` rather than `==`: a short-circuiting comparison on a MAC
    leaks position information under timing.
    """
    out = []
    for m in _PIN_SPAN_RE.finditer(_pin_scan_text(text)):
        if hmac.compare_digest(m.group(1), _mint_tag(TAG_PIN, role, m.group(2))):
            out.append(m.group(0))
    return out


def _verify_summary_tag(text: str, role: str) -> bool:
    """True when `text` is a summary message this proxy minted, carried by `role`.

    DEFECT D-N (review 5), and it was live. Verification used to canonicalise with
    `_strip_tags`, which removed EVERY tag of BOTH kinds, while minting used the
    raw body. The two disagreed the moment the summary text itself contained
    anything tag-shaped - and `SUMMARY_RULES` explicitly orders the summarizer to
    "Preserve ALL user requests … EXACTLY as written", so a summary that quotes a
    pinned message quotes its `[PIN:…]` marker. MEASURED on the shipped code:

        summary text "1. user pinned: [PIN:1113ca8ad6bc8cfd] …"
          -> _is_synthetic False, _has_summary False

    Consequences, all silent: `start_idx` stops skipping the previous
    [summary, ack] pair, so the old summary is re-summarized as ordinary
    conversation (summary-of-a-summary decay, the exact thing this plugin exists
    to prevent), and the summary message becomes pin-ELIGIBLE, which is the
    Python side of `synthetic_never_pinned` going away.

    Now only the proxy's OWN tag is removed, `count=1` (it is at index 0, so the
    first match is always ours), and nothing else is touched. A tag-shaped string
    inside the summary body is just body text, covered by the MAC.
    """
    m = _SUMMARY_TAG_RE.search(text)
    if not m:
        return False
    body = _SUMMARY_TAG_RE.sub("", text, count=1).strip()
    return hmac.compare_digest(m.group(1), _mint_tag(TAG_SUMMARY, role, body))

# Hoisted out of compress() so that (a) _is_synthetic can recognise the proxy's
# own ack exactly rather than by guesswork, and (b) check-compressor-drift.py can
# compute the summary-message overhead (212 chars) without reconstructing string
# literals. Editing either string changes that overhead - the drift checker
# recomputes it from these constants, so it will not go stale.
SUMMARY_TRAILER = (
    "The above is a chronological summary of our earlier conversation. "
    "All file paths, decisions, and code changes are preserved. "
    "Continue from where we left off."
)
ACK_TEXT = (
    "I have the full context from our previous conversation — "
    "the timeline, all files modified, decisions made, and current state. "
    "Continuing from where we left off."
)

# Refusal codes. These strings cross the boundary into the log and /health, and
# they are compared verbatim against Compressor.lean's `outcomeCode`.
REFUSAL_NOTHING = "nothingToCompress"
REFUSAL_PIN_BUDGET = "pinBudget"
REFUSAL_SUMMARY_TOO_LARGE = "summaryTooLarge"

SUMMARY_RULES = """RULES:
- Structure as a TIMELINE: use numbered steps showing what happened in order
- Preserve ALL file paths, function/class/variable names EXACTLY as written
- Preserve ALL technical decisions and WHY they were made
- Preserve ALL code changes: what file, what was changed, what the new code does
- Preserve ALL errors encountered and how they were resolved
- Preserve ALL user requests and instructions — what they asked for, what constraints they gave, what they said to do or NOT do
- Preserve user preferences, workflow choices, and recurring patterns (e.g. "always use X", "never do Y")
- Include key code snippets when they're central to understanding (keep them short)
- Do NOT editorialize or add commentary
- Be as DENSE as possible — every sentence should carry information

FORMAT:
## Active Goal
- [What the user is CURRENTLY asking for — their most recent request or focus]
- [Any constraints or rules the user has stated (do/don't do)]

## Previous Goals (completed or shifted away from)
- [Earlier goals that were finished or that the user moved on from — keep brief]

## Timeline
1. [First thing that happened]
2. [Second thing...]
...

## Current State
- [What's done, what's in progress, what's next]

## Key Details
- [File paths, configs, decisions that must not be forgotten]"""

# Native mode: appended as the final user message after the real conversation,
# like Claude Code's own /compact. Contains "context compressor" so test mocks
# can recognize summarization requests.
NATIVE_COMPACT_PROMPT = f"""Stop working on the current task. Act as a context compressor: produce a CHRONOLOGICAL, DENSE technical summary of our conversation above.

{SUMMARY_RULES}

If the conversation begins with a {SUMMARY_MARKER} block from an earlier compression, integrate it — keep all its details and extend the timeline with what happened since.

Write ONLY the chronological summary, nothing else."""

# Flattened mode: standalone prompt carrying the conversation as text.
SUMMARIZE_PROMPT = f"""You are a context compressor for an AI coding assistant conversation.

Your job: take the conversation below and produce a CHRONOLOGICAL, DENSE technical summary.

{SUMMARY_RULES}

{{existing_summary_section}}

CONVERSATION TO COMPRESS:
{{conversation}}

Write the chronological summary:"""


class CompressionResult:
    """What one compression step did, or why it declined.

    Lean: `Except Refusal Conv`. `cut_index` is carried explicitly so the server
    never has to recover it by subtracting a length — defect D4 was exactly that
    subtraction getting the range wrong and storing a hash chain that could never
    match anything again."""

    __slots__ = ("messages", "prefix", "cut_index", "pinned_count", "refusal", "detail")

    def __init__(self, messages, prefix, cut_index, pinned_count, refusal, detail):
        self.messages = messages
        self.prefix = prefix
        self.cut_index = cut_index
        self.pinned_count = pinned_count
        self.refusal = refusal
        self.detail = detail

    @property
    def ok(self) -> bool:
        return self.refusal is None

    def __repr__(self) -> str:
        if self.ok:
            return (f"<CompressionResult ok cut={self.cut_index} "
                    f"pinned={self.pinned_count} n={len(self.messages)}>")
        return f"<CompressionResult refused {self.refusal}: {self.detail}>"


class RollingCompressor:
    def __init__(
        self,
        trigger_tokens: int = 80000,
        target_tokens: int = 40000,
        summarizer_model: str = "",
    ):
        self.trigger_tokens = trigger_tokens
        self.target_tokens = target_tokens
        # Empty = native mode uses the session's own model (prompt-cache hit);
        # flattened mode falls back to LEGACY_DEFAULT_MODEL.
        self.summarizer_model = summarizer_model
        self.compression_count = 0
        self.total_tokens_saved = 0
        # Observability for the refusal paths. A silent decline is defect D3's
        # signature, so every decline is counted and the last one is kept.
        self.last_refusal = None
        self.refusal_counts = {}
        self.pin_rejections = []       # accumulated across calls (see D-H)
        self.pin_rejections_last = []  # just the most recent call

    def effective_summarizer_model(self) -> str:
        """The model the summarizer will ACTUALLY put on the wire, per mode.

        REVIEW-6 DEFECT R6-1. `/health` and the startup banner both reported
        `SUMMARIZER_MODEL or "(session model)"`. That string is true of
        `_summarize_native` (which does `payload.get("model", ...)`) and FALSE of
        `_summarize_flattened`, which never looks at the payload and always sends
        `LEGACY_DEFAULT_MODEL`. Production runs flattened/openai, so the one field
        an auditor would consult to learn which model writes the summaries named
        the wrong one — for every audit so far. Fixing the CONSTANT in review 5
        without fixing this REPORT left the misleading surface exactly as it was:
        /health still answered "(session model)" on both ports, measured live.

        The report is now derived from the same branch the send path takes, so it
        cannot drift from it again: a future edit to either mode's model choice
        must come through here.
        """
        if self.summarizer_model:
            return self.summarizer_model
        if NATIVE_MODE:
            # payload.get("model", LEGACY_DEFAULT_MODEL) — genuinely the session's
            # model, but only when a payload is supplied; name the fallback too
            # rather than implying the session model is guaranteed.
            return f"(session model, else {LEGACY_DEFAULT_MODEL})"
        return LEGACY_DEFAULT_MODEL

    def pin_auth_scheme(self) -> str:
        """The pin auth scheme, DERIVED by exercising the shipped verifier.

        REVIEW-6. `/health` reported a bare literal `"pin_auth": "hmac"`
        (vibe-rc-server.py:971). That is the R6-1 shape one notch weaker: a
        surface making a SECURITY claim about a path it is not bound to. It
        could not lie when measured — `_verified_pin_spans` and
        `_verify_summary_tag` both go through `hmac.compare_digest`, and no
        non-hmac branch exists — but "true today by inspection" is exactly the
        property that stops holding silently, and nobody adding a degraded path
        later will remember this literal is here.

        So do not restate the claim: RUN the real verifier and report what it
        actually does. A tag this proxy minted must be ACCEPTED and a forged one
        REFUSED. If either half stops holding, /health says so in the same field
        an auditor already reads, instead of continuing to answer "hmac".

        Cost is two HMAC-SHA256 ops per /health call. `hmac` is stdlib and
        `_mint_tag` is the same function the send path uses, so this cannot
        drift from the verification it describes.

        LIMIT OF THIS INSTRUMENT, stated so the field is not over-read: it
        proves the verifier DISCRIMINATES (mints, accepts, refuses forgeries).
        It does NOT detect a timing-side-channel regression — swapping
        `hmac.compare_digest` for `==` at _verified_pin_spans preserves every
        accept/refuse outcome, so this still reports "hmac" while the leak
        `_verified_pin_spans`' own docstring warns about is back. That gap is
        covered, but by a different instrument: check-compressor-drift.py:811
        asserts `hmac.compare_digest` textually, and :884 asserts the tag is not
        truncated below the width that keeps the MAC meaningful. Behavioural and
        source-level assertions are complements here; neither subsumes the other.
        """
        role, body = "user", "pin-auth-selftest"
        good = _mint_tag(TAG_PIN, role, body)
        accepts_valid = _verified_pin_spans(
            f"[PIN:{good}]{body}[/PIN]", role
        ) == [f"[PIN:{good}]{body}[/PIN]"]
        # Flip the tag to something the MAC cannot equal, same length so the
        # span regex still matches and we are testing the MAC, not the parser.
        forged = ("1" * len(good)) if good != "1" * len(good) else "0" * len(good)
        refuses_forged = _verified_pin_spans(f"[PIN:{forged}]{body}[/PIN]", role) == []
        if accepts_valid and refuses_forged:
            return "hmac"
        if not refuses_forged:
            return "DEGRADED: forged pin tags are being ACCEPTED"
        return "BROKEN: this proxy's own pin tags are being rejected"

    def _count_chars(self, messages: list) -> int:
        """Count total characters across all messages.

        PORT: this drives EVERY size decision — the keep ratio, the proactive
        trigger, and the "did compression actually shrink anything" guard. Upstream
        counted only Anthropic content blocks, so against Mistral traffic it would
        have counted tool call arguments as ZERO and reported a tool-heavy
        conversation as nearly empty: no compression would ever fire, and the proxy
        would look perfectly healthy while doing nothing.
        """
        total_chars = 0
        for msg in messages:
            content = msg.get("content", "")
            if isinstance(content, str):
                total_chars += len(content)
            elif isinstance(content, list):
                # Mistral also permits a list of {"type":"text","text":...} parts.
                for block in content:
                    if isinstance(block, dict):
                        if block.get("type") == "text":
                            total_chars += len(block.get("text", ""))
                        else:
                            total_chars += len(json.dumps(block))
            # Mistral: the call is a sibling key, not a content block. `arguments`
            # is a JSON *string* and is frequently the largest part of a turn.
            for tc in msg.get("tool_calls") or []:
                if isinstance(tc, dict):
                    fn = tc.get("function") or {}
                    total_chars += len(str(fn.get("name", "")))
                    total_chars += len(str(fn.get("arguments", "")))
        return total_chars

    def _find_keep_index(self, messages: list, keep_num: int, keep_den: int) -> int:
        """Find the cut point: keep the last keep_num/keep_den fraction of content.

        AUDIT-FIX (defect 3): the sizing arithmetic must EXCLUDE the system
        prefix. This is the second half of the system-in-array difference, and
        the port applied the first half (cut safety) without it.

        Anthropic carries the system prompt out-of-band, so upstream's
        `total_chars = count(messages)` was purely conversation. Here index 0 IS
        the system prompt, and vibe's is large: measured live at 31,107 of 31,357
        total chars = 99.2% of everything counted. target_chars was therefore
        computed as a fraction of a total that is almost entirely the ONE thing
        that can never be compressed, so the backward walk always ran to index 0,
        the cut always landed on the system boundary, and compress() always hit
        `keep_from_idx <= start_idx` and returned None.

        Measured before this fix, trigger=2000, a 20-message live session:
        "[PROACTIVE] compressor.compress() returned None (nothing to compress)"
        on EVERY request while over trigger — the plugin forwarded traffic
        correctly, logged healthily, and compressed nothing, ever.

        The walk is now floored at the system prefix and the budget is taken over
        the compressible body only.

        THE RATIO IS INTEGER ARITHMETIC. It used to be a float `keep_ratio` with
        `int(total_chars * keep_ratio)`. Floats were not modelled in
        Compressor.lean, they were REMOVED: an IEEE754 product is not integer
        division, so a float here would be a permanent unprovable gap between the
        proof and the code rather than merely untidy. Lean: `keepTarget`.
        """
        head = self._system_head(messages)
        if len(messages) - head <= 4:
            return head
        max_idx = len(messages) - 4
        total_chars = self._count_chars(messages[head:])
        target_chars = total_chars * keep_num // keep_den if keep_den else 0
        accumulated = 0
        for i in range(len(messages) - 1, head - 1, -1):
            msg_chars = self._count_chars([messages[i]])
            if accumulated + msg_chars > target_chars:
                for j in range(i + 1, len(messages)):
                    if messages[j].get("role") == "user":
                        if not self._has_tool_result(messages[j]):
                            return max(head, min(j, max_idx))
                return max(head, min(i + 1, max_idx))
            accumulated += msg_chars
        return head

    def _safe_cut(self, messages: list, cut: int, floor: int) -> int:
        """Walk cut back until the summarized prefix messages[:cut] ends
        cleanly: its last message must carry no tool_use blocks, since their
        tool_results would be cut off and the native compaction request would
        be rejected. Ending on a tool_result (or plain text) is valid — in
        agentic sessions that boundary exists after every tool round-trip.
        The cut also must not sit adjacent to a 'system'-role message on
        EITHER side: the API requires an in-array system message to follow a
        user message AND precede an assistant message. If the prefix ends on
        one, the appended compact prompt (user) lands after it; if the kept
        tail starts with one, the ack (plain assistant) lands before it —
        both are 400s. Interior system messages keep their original
        neighbors and stay valid, so only the boundary needs walking."""
        # PORT: the third condition is new and it is the one that matters here.
        # Upstream only had to keep the PREFIX from ending on a dangling tool call.
        # Mistral emits parallel calls as one assistant turn followed by SEVERAL
        # role:"tool" messages, so a cut can land BETWEEN two results: the message
        # before it has no tool_calls (it is itself a result), so upstream's check
        # passes, and the kept tail then begins with a tool message whose call was
        # summarized away. Mistral rejects that outright — a hard 400 on every
        # subsequent request, i.e. a wedged session rather than a degraded one.
        while cut > floor and (
            self._has_tool_use(messages[cut - 1])
            or messages[cut - 1].get("role") == "system"
            or (cut < len(messages) and messages[cut].get("role") == "system")
            or (cut < len(messages) and messages[cut].get("role") == "tool")
        ):
            cut -= 1
        # AUDIT-FIX (open nit): clamp. `_safe_cut(msgs, 0, 1)` used to return 0,
        # i.e. BELOW its own floor, because the loop never runs when cut <= floor.
        # That was unreachable only because compress() guards it immediately
        # afterwards. Lean `safeCut_ge_floor` now holds unconditionally, and
        # `clamp_preserves_guard` proves compress()'s verdict is bit-identical
        # either way: below the floor the old code returned something <= start_idx
        # and the new code returns exactly start_idx, and the guard is `<=`.
        return max(cut, floor)

    def _has_tool_use(self, message: dict) -> bool:
        """Mistral: an assistant turn carries `tool_calls` as a sibling of content,
        not a `tool_use` block inside it."""
        return bool(message.get("tool_calls"))

    def _has_tool_result(self, message: dict) -> bool:
        """Mistral: the result is its OWN message with role "tool" — there is no
        tool_result block to look for inside content."""
        return message.get("role") == "tool"

    # --- HARD MEMORY ---------------------------------------------------------
    # Lean: Compressor.lean section 5 (`pinEligible`, `effectivePinned`,
    # `pinnedIn`, `pinned_never_cut`).

    def _msg_text(self, message: dict) -> str:
        """Plain text of a message, for marker scanning only. Mirrors the text
        half of _count_chars; tool_calls arguments are deliberately NOT scanned,
        so a model that happens to emit the marker inside a JSON argument cannot
        pin a tool-call group it is not allowed to pin anyway."""
        content = message.get("content")
        if isinstance(content, str):
            return content
        if isinstance(content, list):
            return "".join(
                b.get("text", "")
                for b in content
                if isinstance(b, dict) and b.get("type") == "text"
            )
        return ""

    def _is_synthetic(self, message: dict) -> bool:
        """True for messages this proxy wrote itself. Lean: `Msg.synthetic`.

        Exact, not heuristic: the summary carries an AUTHENTICATED SUMMARY_MARKER
        and the ack is a fixed literal. Without this test a summary that quoted
        the pin marker would pin itself — see `synthetic_never_pinned`.

        DEFECT D-D: this used to be `SUMMARY_MARKER in text`, i.e. a substring
        test over content the conversation controls. Forging the marker in the
        first non-system message made `_has_summary` fire, moving start_idx past
        two REAL messages — inside the replaced span, outside the summarizer
        input, so deleted and never summarized — while the forged text was fed to
        every later summarizer call as "EXISTING ROLLING SUMMARY … keep all
        details". Only a tag this proxy minted counts now.
        """
        text = self._msg_text(message)
        return (_verify_summary_tag(text, message.get("role") or "")
                or text == ACK_TEXT)

    def _is_pinned(self, message: dict) -> bool:
        """Did the USER ask for this message to be kept? Lean: `Msg.pinned`.

        Two channels:
          1. `pinned: true` set structurally on the message (sidecar / API caller,
             never conversation content).
          2. At least one authenticated `[PIN:<hex>]…[/PIN]` SPAN whose MAC this
             proxy minted for THIS message's role.

        DEFECT D-C: a bare `PIN_MARKER` substring used to be enough, so any
        assistant reply containing it pinned itself permanently and a pasted
        document mentioning it pinned the paste. A bare marker is now INERT — and
        `_pin_rejections` reports it as `unauthenticated` rather than dropping it
        silently, because an ignored pin is D3's signature all over again.
        """
        if message.get("pinned") is True:
            return True
        return bool(_verified_pin_spans(self._msg_text(message),
                                        message.get("role") or ""))

    def _pin_extract(self, message: dict) -> dict:
        """The message actually carried over the boundary. Lean: `pinExtract`.

        RETENTION MUST EQUAL AUTHENTICATION. Now that the MAC covers a delimited
        span rather than the whole body, retaining the whole message would let one
        3-byte authenticated span drag an arbitrarily large payload across the
        boundary verbatim — mint over nothing, keep everything. The old
        whole-message MAC had no such gap (MEASURED before this change: a valid
        tag plus 50,000 extra chars did not verify at all), and losing that
        property while fixing inline usage would be a straight trade of one defect
        for a worse one.

        So a marker-pinned message is rebuilt from ONLY its verified spans, joined
        by newlines, delimiters kept. Unverified spans and surrounding prose are
        dropped. Lean states this as `(pinExtract m).chars ≤ m.pinChars ≤ m.chars`.

        IDEMPOTENT: extracting an already-extracted message returns the same
        content, which is what makes multi-round retention stable (Lean
        `pinExtract_idem`, and the drift checker executes it).

        The structural `pinned: true` channel keeps the WHOLE message: it does not
        come from conversation text, so there is no span to scope it to.
        """
        if message.get("pinned") is True:
            return message
        spans = _verified_pin_spans(self._msg_text(message),
                                    message.get("role") or "")
        if not spans:
            return message
        return {"role": message.get("role"), "content": "\n".join(spans)}

    def _pin_attempted(self, message: dict) -> bool:
        """A pin was ASKED FOR — authenticated or not. Drives the rejection
        report so an unauthenticated attempt is visible instead of inert."""
        if message.get("pinned") is True:
            return True
        return PIN_OPEN in self._msg_text(message)

    def _pin_eligible(self, message: dict) -> bool:
        """Can this message be hoisted over the summary boundary without breaking
        the wire format, and is it something vibe's USER wrote? Lean: `pinEligible`.

        DEFECT D-O (review 5): this used to admit `assistant` as well. Combined
        with a MAC that did not commit to the role, a valid pin copied into an
        assistant turn authenticated and the model pinned its own output — the
        unbounded stack `synthetic_never_pinned` exists to prevent, reachable from
        pure text. Role binding in `_mint_tag` also closes that, but only against
        an attacker who cannot read `state/pin-secret`. THIS check closes it
        against one who can, which is why both exist and why this one is the
        primary control.

        Cost, stated plainly: an assistant turn can no longer be pinned at all,
        even deliberately. To keep a model answer, quote it in a user message.

        REVIEW-6 / DEFECT R6-3 — DO NOT "simplify" this function.
        At 22:59 tonight the `4b-reviewer` agent run, whose task was to REVIEW
        this function, applied its own suggestion to it: it reordered the guards
        and rewrote the role test as a trailing `== "user"`. The rewrite was
        semantically inert (verified: 16 role x body x tool_calls shapes, zero
        divergences) but it moved the text `check-compressor-drift.py:985` anchors
        M18/M16 on, so the drift gate went red on a change nobody authorised, in
        the very file the audit was auditing.

        The same review also proposed REMOVING the role check entirely on the
        grounds that it is "redundant". It is not: it is the primary control for
        defect D-O against an attacker who can read `state/pin-secret` (which is
        mode-0644, and every agent has bash). Applying that suggestion would have
        been a silent security regression that no test in this tree would catch,
        because the MAC role-binding it would have relied on protects a different
        attacker. The order below is the audited order; keep it.
        """
        if message.get("role") != "user":
            return False
        if self._has_tool_use(message):
            return False
        return not self._is_synthetic(message)

    def _effective_pinned(self, message: dict) -> bool:
        """Lean: `effectivePinned` = pinned && pinEligible."""
        return self._is_pinned(message) and self._pin_eligible(message)

    def _pinned_in(self, messages: list, lo: int, hi: int) -> list:
        """The pinned messages inside the half-open span [lo, hi), in order.
        Lean: `pinnedIn`.

        NOTE the span starts at the SYSTEM HEAD, not at start_idx. Scanning from
        start_idx would leave the previous [summary, ack] pair outside the scan
        and make the preservation theorem conditional on those two never being
        pinned. Starting at the head makes it unconditional and costs nothing —
        the pair is synthetic, so never eligible.

        Each survivor is passed through `_pin_extract`, so what crosses the
        boundary is exactly what was authenticated. Lean: `pinnedIn` is the same
        filter followed by `List.map pinExtract`."""
        return [self._pin_extract(m) for m in messages[lo:hi]
                if self._effective_pinned(m)]

    def _pin_rejections(self, messages: list) -> list:
        """Pins that were asked for and cannot be honoured, with the reason.

        Reported, never silently dropped. A pin that quietly does nothing has the
        same signature as defect D3: healthy logs, no effect."""
        out = []
        for i, m in enumerate(messages):
            role = m.get("role")
            if not self._pin_attempted(m):
                continue
            if self._effective_pinned(m):
                continue                       # asked for and honoured

            # Something was asked for and not honoured. STRUCTURAL reasons are
            # diagnosed FIRST, before the MAC. Since the MAC also commits to the
            # role (D-O), a valid user pin pasted into a tool result fails
            # verification before eligibility is ever consulted — so ordering the
            # other way reported `unauthenticated` for a message that is refused
            # for wire-shape reasons and would be refused however it was signed.
            # That answer sends the reader hunting a forgery that is not there.
            if not self._pin_eligible(m):
                if role == "system":
                    reason = "system messages are already in the never-cut prefix"
                elif role == "tool":
                    reason = "pinning a tool result would orphan its call (Mistral 400)"
                elif role == "assistant":
                    reason = ("assistant turns are not pinnable: the model would "
                              "be able to make its own output unshrinkable (D-O). "
                              "Quote it in a user message instead")
                elif self._has_tool_use(m):
                    reason = "pinning a tool call would orphan its results (Mistral 400)"
                elif self._is_synthetic(m):
                    reason = "proxy-generated summary/ack cannot be pinned"
                else:
                    reason = "ineligible"
                out.append({"index": i, "role": role, "reason": reason,
                            "code": "ineligible"})
                continue

            # Eligible, but nothing authenticated. The three sub-reasons matter:
            # "unauthenticated" is the wrong diagnosis for a typo and for a pin
            # the proxy deliberately refuses to read.
            text = self._msg_text(m)
            scanned = _pin_scan_text(text)
            if _PIN_OPEN_RE.search(scanned) and not _PIN_SPAN_RE.search(scanned):
                out.append({
                    "index": i, "role": role, "code": "unterminated",
                    "reason": f"pin opened but never closed — add {PIN_CLOSE}",
                })
            elif _PIN_SPAN_RE.search(text) and not _PIN_SPAN_RE.search(scanned):
                out.append({
                    "index": i, "role": role, "code": "injected",
                    "reason": ("pin sits inside a vibe-injected region "
                               "(<vibe_warning> / <tool_error> / …), which "
                               "carries model-controlled text, not the user's"),
                })
            else:
                out.append({
                    "index": i, "role": role, "code": "unauthenticated",
                    "reason": "unauthenticated pin marker — mint a tag via POST /pin",
                })
        return out

    def _system_head(self, messages: list) -> int:
        """Count leading system messages. See server._system_prefix_len — vibe puts
        the system prompt IN the message array, so index 0 is not the conversation."""
        n = 0
        for m in messages:
            if m.get("role") == "system":
                n += 1
            else:
                break
        return n

    def _has_summary(self, messages: list) -> bool:
        # PORT: was messages[0]. With a system message at index 0 that check reads
        # the system prompt, never finds the marker, and reports "no previous
        # summary" on every cycle — so each compression would summarize from
        # scratch instead of MERGING with the last one. That is the exact
        # summary-of-a-summary decay this plugin exists to avoid, reintroduced
        # silently by an off-by-one.
        head = self._system_head(messages)
        if len(messages) <= head:
            return False
        content = messages[head].get("content", "")
        if isinstance(content, str):
            # AUTHENTICATED (defect D-D). A bare marker no longer counts: forging
            # it here moved start_idx past two real messages, which were then
            # dropped inside the replaced span without ever reaching the
            # summarizer. Only a tag this proxy minted is honoured.
            return _verify_summary_tag(content, messages[head].get("role") or "")
        return False

    def _extract_summary(self, messages: list) -> str:
        if not self._has_summary(messages):
            return ""
        content = messages[self._system_head(messages)].get("content", "")
        if isinstance(content, str):
            m = _SUMMARY_TAG_RE.search(content)
            if m:
                start = m.end()
                end = content.find(SUMMARY_END_MARKER)
                if end > start:
                    return content[start:end].strip()
        return ""

    def _messages_to_text(self, messages: list) -> str:
        parts = []
        for msg in messages:
            role = msg.get("role", "unknown")
            content = msg.get("content", "")
            # PORT: rebuilt for Mistral shape. This text is what the summarizer
            # actually reads, so anything not rendered here is invisible to the
            # summary. Under the upstream version a tool-heavy vibe conversation
            # flattened to a wall of empty assistant turns — the summary would come
            # back fluent and content-free, which is the worst failure mode
            # available: it looks like it worked.
            if isinstance(content, str):
                text = content
            elif isinstance(content, list):
                text_parts = []
                for block in content:
                    if isinstance(block, dict):
                        if block.get("type") == "text":
                            text_parts.append(block.get("text", ""))
                        else:
                            text_parts.append(json.dumps(block)[:1000])
                text = "\n".join(text_parts)
            else:
                text = str(content)

            # Assistant tool calls (sibling key).
            for tc in msg.get("tool_calls") or []:
                if isinstance(tc, dict):
                    fn = tc.get("function") or {}
                    name = fn.get("name", "?")
                    args = str(fn.get("arguments", ""))
                    if len(args) > 500:
                        args = args[:400] + "...[truncated]"
                    text = (text + f"\n[Tool: {name}({args})]").strip()

            # Tool result messages: label them so the summarizer can tell a result
            # from a user turn — role alone is printed below, but "tool" reads as a
            # speaker rather than an outcome.
            if role == "tool":
                text = f"[Result of {msg.get('name', '?')}]: {text}"

            if len(text) > 4000:
                text = text[:3000] + "\n...[truncated]...\n" + text[-1000:]
            parts.append(f"**{role}**: {text}")
        return "\n\n".join(parts)

    # ------------------------------------------------------------------
    # Native mode: clone the session's own request, append "compact this"
    # ------------------------------------------------------------------

    def _count_breakpoints(self, payload: dict, convo: list) -> int:
        """Count cache_control breakpoints across system, tools, and convo."""
        count = 0
        system = payload.get("system")
        if isinstance(system, list):
            for block in system:
                if isinstance(block, dict) and "cache_control" in block:
                    count += 1
        for tool in payload.get("tools") or []:
            if isinstance(tool, dict) and "cache_control" in tool:
                count += 1
        for msg in convo:
            content = msg.get("content", "")
            if isinstance(content, list):
                for block in content:
                    if isinstance(block, dict) and "cache_control" in block:
                        count += 1
        return count

    def _summarize_native(self, payload: dict, messages: list, cut: int, auth_headers: dict) -> str:
        """Send the session's own request shape with a compact instruction.

        The conversation prefix is identical to what Claude Code just sent, so
        upstream serves it from the prompt cache, and subscription OAuth
        classification sees genuine Claude Code session traffic.
        """
        convo = list(messages[:cut])

        # Place a cache breakpoint on the last conversation message (budget
        # permitting, max 4 per request) so the lookup reads the deepest
        # cache entry created by earlier chat requests.
        if convo and self._count_breakpoints(payload, convo) < 4:
            last = copy.deepcopy(convo[-1])
            c = last.get("content")
            if isinstance(c, str):
                last["content"] = [{
                    "type": "text",
                    "text": c,
                    "cache_control": {"type": "ephemeral"},
                }]
            elif isinstance(c, list) and c and isinstance(c[-1], dict):
                c[-1]["cache_control"] = {"type": "ephemeral"}
            convo[-1] = last

        model = self.summarizer_model or payload.get("model", LEGACY_DEFAULT_MODEL)
        max_tokens = 16000
        body = {
            "model": model,
            "max_tokens": max_tokens,
            "stream": True,
            "messages": convo + [{"role": "user", "content": NATIVE_COMPACT_PROMPT}],
        }
        for key in ("system", "tools", "metadata"):
            if payload.get(key) is not None:
                body[key] = payload[key]
        if body.get("tools"):
            # The summary must be text — without this the model may answer
            # the cloned request with a tool_use and the summary comes back empty
            body["tool_choice"] = {"type": "none"}
        thinking = payload.get("thinking")
        if isinstance(thinking, dict) and thinking.get("type") == "enabled":
            body["thinking"] = thinking
            body["max_tokens"] = max(max_tokens, int(thinking.get("budget_tokens", 0)) + 4000)

        req_body = json.dumps(body).encode()
        headers = _clean_headers(auth_headers)
        headers["content-length"] = str(len(req_body))
        headers["accept-encoding"] = "identity"

        summarizer_path = _join_path(_SUMMARIZER_PATH, "/v1/messages")
        log.info(
            f"Native compaction request -> {SUMMARIZER_BASE_URL} "
            f"model={model} messages={len(body['messages'])} ({len(req_body):,} bytes)"
        )

        conn = _summarizer_conn()
        conn.request("POST", summarizer_path, body=req_body, headers=headers)
        resp = conn.getresponse()
        resp_body = resp.read()
        conn.close()
        if resp_body[:2] == b"\x1f\x8b":  # upstream gzipped despite identity
            resp_body = gzip.decompress(resp_body)

        if resp.status != 200:
            error = resp_body.decode("utf-8", errors="replace")
            raise RuntimeError(f"Summarization API returned {resp.status}: {error[:500]}")

        parts = []
        for line in resp_body.decode("utf-8", errors="replace").split("\n"):
            if not line.startswith("data: "):
                continue
            try:
                data = json.loads(line[6:])
            except json.JSONDecodeError:
                continue
            evt = data.get("type", "")
            if evt == "message_start":
                usage = data.get("message", {}).get("usage", {})
                log.info(
                    f"Native compaction usage: input={usage.get('input_tokens', 0):,} "
                    f"cache_read={usage.get('cache_read_input_tokens', 0):,} "
                    f"cache_write={usage.get('cache_creation_input_tokens', 0):,}"
                )
            elif evt == "content_block_delta":
                delta = data.get("delta", {})
                if delta.get("type") == "text_delta":
                    parts.append(delta.get("text", ""))
            elif evt == "error":
                raise RuntimeError(f"Summarization stream error: {json.dumps(data)[:500]}")
        summary = "".join(parts).strip()
        if not summary:
            snippet = resp_body.decode("utf-8", errors="replace")[:300]
            raise RuntimeError(f"Summarization returned empty text; response starts: {snippet}")
        return summary

    # ------------------------------------------------------------------
    # Flattened mode: standalone request to a custom summarizer
    # ------------------------------------------------------------------

    def _summarize_flattened(self, prompt: str, auth_headers: dict) -> str:
        summary_max_tokens = 16000
        model = self.summarizer_model or LEGACY_DEFAULT_MODEL

        if SUMMARIZER_FORMAT == "openai":
            # PORT: upstream hard-failed when no model was named, because in its
            # world "openai format" meant an arbitrary third-party endpoint whose
            # model names it could not guess. Here the endpoint is known to be
            # Mistral, so LEGACY_DEFAULT_MODEL (`mistral-large-2512`) is a correct
            # default and refusing to run without ROLLING_CONTEXT_MODEL would make
            # the common case fail closed for no reason.
            #
            # REVIEW-6: this comment still said "devstral-small-latest" after the
            # review-5 edit moved the constant to Large 3 — the exact stale-doc
            # shape that sent four audits looking at the wrong model. The name is
            # spelled here only because it is load-bearing for the argument; if
            # the constant moves again, this line moves with it.
            path = _join_path(_SUMMARIZER_PATH, "/v1/chat/completions")
            req_body = json.dumps({
                "model": model,
                "max_tokens": summary_max_tokens,
                "messages": [{"role": "user", "content": prompt}],
            }).encode()
            # AUDIT-FIX (defect 2): fall back to the CALLER's auth headers, exactly
            # as the anthropic branch below already does.
            #
            # Upstream defaulted to SUMMARIZER_FORMAT="anthropic", whose branch ends
            # in `_clean_headers(auth_headers)` — so with no explicit summarizer key
            # it reused the credentials of the request being proxied. The port flipped
            # the default to "openai" (correct: Mistral IS the chat-completions
            # shape), but this branch only ever sent an Authorization header when
            # ROLLING_CONTEXT_VIBE_SUMMARIZER_KEY was set, and nothing sets it.
            #
            # Result before the fix: every summarization got
            #   401 {"detail":"Unauthorized"}
            # -> compress() raised -> 300s cooldown -> retry -> 401 forever. The
            # proxy passed health checks, forwarded traffic correctly and NEVER
            # compressed anything. Measured directly against api.mistral.ai:
            # same call 401s without auth, returns 200 with it.
            #
            # vibe authenticates from the OS keyring (vibe/core/config/vibe_schema.py
            # :94-100), never from an env var, so the key only ever reaches this
            # process as a header on the request being proxied — this fallback is the
            # only path by which the summarizer can be authenticated by default.
            if SUMMARIZER_API_KEY:
                headers = {"content-type": "application/json",
                           "authorization": f"Bearer {SUMMARIZER_API_KEY}"}
            else:
                # Drop content-type case-insensitively before re-adding it: the
                # passthrough headers keep vibe's original casing, and a plain
                # assignment would send the header TWICE (the same trap
                # _clean_headers documents for accept-encoding).
                headers = {k: v for k, v in _clean_headers(auth_headers).items()
                           if k.lower() != "content-type"}
                headers["content-type"] = "application/json"
        else:
            path = _join_path(_SUMMARIZER_PATH, "/v1/messages")
            req_body = json.dumps({
                "model": model,
                "max_tokens": summary_max_tokens,
                "messages": [{"role": "user", "content": prompt}],
            }).encode()
            if SUMMARIZER_API_KEY:
                headers = {
                    "content-type": "application/json",
                    "anthropic-version": "2023-06-01",
                    "x-api-key": SUMMARIZER_API_KEY,
                }
            else:
                headers = _clean_headers(auth_headers)
        headers["content-length"] = str(len(req_body))
        headers["accept-encoding"] = "identity"

        log.info(
            f"Compression request -> {SUMMARIZER_BASE_URL} path={path} "
            f"format={SUMMARIZER_FORMAT} model={model}"
        )

        conn = _summarizer_conn(timeout=120)
        conn.request("POST", path, body=req_body, headers=headers)
        resp = conn.getresponse()
        resp_body = resp.read()
        conn.close()
        if resp_body[:2] == b"\x1f\x8b":  # upstream gzipped despite identity
            resp_body = gzip.decompress(resp_body)

        if resp.status != 200:
            error = resp_body.decode("utf-8", errors="replace")
            raise RuntimeError(f"Summarization API returned {resp.status}: {error[:500]}")
        data = json.loads(resp_body)

        if SUMMARIZER_FORMAT == "openai":
            return data["choices"][0]["message"]["content"]
        return data["content"][0]["text"]

    # ------------------------------------------------------------------

    def compress_ex(self, messages: list, auth_headers: dict, real_token_count: int = None,
                    payload: dict = None):
        """Compress, reporting WHAT happened rather than just whether it worked.

        Returns a CompressionResult. `refusal` is None on success, otherwise one
        of the REFUSAL_* codes, which are compared verbatim against
        Compressor.lean's `outcomeCode` by check-compressor-drift.py.

        This exists because `compress() -> None` conflated three different
        situations, and the one that actually fired in production (defect D3) was
        indistinguishable from the benign one. `cut_index` is REPORTED here rather
        than re-derived by subtraction at the call site — re-deriving it is
        exactly how defect D4 stored an unmatchable hash chain.

        Lean: `stepE`. The guard order below is the guard order there."""
        # Use real API token count to determine what fraction of content to keep.
        # Integer numerator/denominator, never a float — see _find_keep_index.
        if real_token_count and real_token_count > 0:
            keep_num, keep_den = self.target_tokens, real_token_count
            log.info(
                f"Keep ratio: {keep_num}/{keep_den} "
                f"(target={self.target_tokens:,} / real={real_token_count:,})"
            )
        else:
            # Fallback: keep half (conservative)
            keep_num, keep_den = 1, 2
            log.info("Keep ratio: 1/2 (fallback, no real token count)")

        keep_from_idx = self._find_keep_index(messages, keep_num, keep_den)

        has_existing_summary = self._has_summary(messages)
        # PORT: floor every index at the system prefix. Upstream's 0 / 2 was correct
        # when system travelled out-of-band; here it would let the summarizer eat the
        # system prompt. `+2` still skips the previous [summary, ack] pair, it just
        # starts counting after the system messages.
        sys_head = self._system_head(messages)
        start_idx = sys_head + (2 if has_existing_summary else 0)

        keep_from_idx = self._safe_cut(messages, keep_from_idx, start_idx)

        rejections = self._pin_rejections(messages)
        # DEFECT D-H: this was `self.pin_rejections = rejections`, i.e. the status
        # surface reported only the LAST call. A rejection raised on call 1 read
        # as `[]` on /health after call 2, making "no pins were ever refused"
        # indistinguishable from "a pin was refused a moment ago". Accumulate, and
        # dedupe on (code, role, reason) so a pin refused on every round does not
        # grow the list without bound.
        self.pin_rejections_last = rejections
        _seen = {(r.get("code"), r.get("role"), r.get("reason")) for r in self.pin_rejections}
        for r in rejections:
            key = (r.get("code"), r.get("role"), r.get("reason"))
            if key not in _seen:
                _seen.add(key)
                self.pin_rejections.append(r)
        for r in rejections:
            log.warning(
                f"[PIN] ignoring pin on message {r['index']} (role={r['role']}): "
                f"{r['reason']}"
            )

        if keep_from_idx <= start_idx:
            log.info("Not enough old messages to compress, passing through")
            return self._refuse(REFUSAL_NOTHING, keep_from_idx,
                                "no compressible span above start_idx")

        # HARD MEMORY: everything pinned inside the replaced span is carried
        # across the boundary verbatim. Span starts at sys_head because the OLD
        # [summary, ack] pair is replaced too. Lean: `pinnedIn`, `spanChars`.
        pinned_kept = self._pinned_in(messages, sys_head, keep_from_idx)
        span_chars = self._count_chars(messages[sys_head:keep_from_idx])
        pin_chars = self._count_chars(pinned_kept)

        # PIN SATURATION, decided BEFORE spending an API call. If the pins inside
        # the span already account for all of it then no summary of any length can
        # shrink this conversation — Lean `pin_saturation_cannot_shrink` quantifies
        # over every possible summarizer, including one that returns "".
        # Without this check the request is made, the summary comes back, the
        # server's `merged_chars < msg_chars` guard rejects it, and the only
        # evidence is a line saying compression "no longer helps".
        if span_chars <= pin_chars:
            log.warning(
                f"[PIN] pin budget exhausted: pinned {pin_chars:,} chars of a "
                f"{span_chars:,}-char compressible span across "
                f"{len(pinned_kept)} pinned message(s). No summary can shrink "
                f"this; declining WITHOUT calling the summarizer. "
                f"Unpin something or raise the trigger."
            )
            return self._refuse(REFUSAL_PIN_BUDGET, keep_from_idx,
                                f"pins {pin_chars} >= span {span_chars}")

        # DEFECT D-F (review 4), PARTIAL and deliberately so. The post-summary
        # guard below compares `span_chars` against `pin_chars + overhead`, where
        # `overhead` is the size of [summary_message, ack_message] — and the summary
        # message CONTAINS the model's summary text. So the full test is NOT
        # decidable before the call, contrary to how D-F was stated: only its
        # constant part is.
        #
        # What IS decidable is the FLOOR. Every summary, including the empty one,
        # carries the same scaffolding: the tag line, the end marker, the trailer
        # and the ack. If the span cannot even fit THAT, then no summary of any
        # length can shrink the conversation and the summarizer call is guaranteed
        # waste — the same argument as `pin_saturation_cannot_shrink`, extended
        # with a constant. This is a sound lower bound, never a false decline:
        # overhead >= overhead_min holds by construction because `new_summary` only
        # ever adds characters.
        #
        # Measured on the live scratch instance: a real vibe session declined with
        # "pins+summary 1781 >= span 320" AFTER paying for the summary. That
        # particular case had span 320 > overhead_min, so this gate would not have
        # caught it — the saving is real but narrower than D-F claimed, and saying
        # so is the point.
        _empty_body = f"\n{SUMMARY_END_MARKER}\n\n{SUMMARY_TRAILER}"
        _overhead_min = self._count_chars([
            {"role": "user",
             "content": f"{SUMMARY_MARKER[:-1]}:{'0' * 16}]\n{_empty_body}"},
            {"role": "assistant", "content": ACK_TEXT},
        ])
        if span_chars <= pin_chars + _overhead_min:
            log.warning(
                f"[COMPRESS] declining BEFORE calling the summarizer: the "
                f"{span_chars:,}-char span cannot fit pins ({pin_chars:,}) plus the "
                f"minimum summary scaffolding ({_overhead_min:,} chars), so no "
                f"summary of any length can shrink it."
            )
            return self._refuse(REFUSAL_SUMMARY_TOO_LARGE, keep_from_idx,
                                f"pins+minimum overhead {pin_chars + _overhead_min} "
                                f">= span {span_chars} (pre-call)")

        recent_messages = messages[keep_from_idx:]

        use_native = NATIVE_MODE and payload is not None
        if use_native:
            new_summary = self._summarize_native(payload, messages, keep_from_idx, auth_headers)
        else:
            existing_summary = self._extract_summary(messages) if has_existing_summary else ""
            to_compress = messages[start_idx:keep_from_idx]
            if not to_compress:
                log.info("Nothing to compress")
                return self._refuse(REFUSAL_NOTHING, keep_from_idx,
                                    "empty summarizer span")
            conversation_text = self._messages_to_text(to_compress)
            existing_section = ""
            if existing_summary:
                existing_section = (
                    "EXISTING ROLLING SUMMARY FROM PREVIOUS COMPRESSIONS "
                    "(integrate this timeline with the new conversation below — "
                    "keep all details, extend the timeline):\n"
                    f"{existing_summary}\n\n"
                )
            prompt = SUMMARIZE_PROMPT.format(
                existing_summary_section=existing_section,
                conversation=conversation_text,
            )
            log.info(
                f"Summarizing {keep_from_idx - start_idx} messages "
                f"({len(conversation_text):,} chars, flattened)..."
            )
            new_summary = self._summarize_flattened(prompt, auth_headers)

        log.info(f"Summary generated: {len(new_summary):,} chars")

        # The marker carries an HMAC over the summary body (defect D-D). Only a
        # marker this proxy minted makes `_is_synthetic` / `_has_summary` fire, so
        # conversation content quoting the bare marker is inert.
        #
        # The tag is computed over EXACTLY the body `_verify_summary_tag` will
        # recover: the content with the leading tag removed once, stripped. It
        # commits to the summary text as written, INCLUDING anything tag-shaped
        # the model put there — which is defect D-N, where mint used the raw body
        # and verify canonicalised with `_strip_tags`, so a summary that quoted a
        # pinned message failed its own MAC. The role is bound too, and it is the
        # role this message is emitted with.
        _summary_body = (
            f"{new_summary}\n"
            f"{SUMMARY_END_MARKER}\n\n"
            f"{SUMMARY_TRAILER}"
        )
        _tag = _mint_tag(TAG_SUMMARY, "user", _summary_body.strip())
        summary_message = {
            "role": "user",
            "content": (
                f"{SUMMARY_MARKER[:-1]}:{_tag}]\n"
                f"{_summary_body}"
            ),
        }
        ack_message = {"role": "assistant", "content": ACK_TEXT}

        # The replacement for messages[sys_head:keep_from_idx]. The pinned block
        # sits AFTER the ack so it cannot separate the summary (user) from its ack
        # (assistant), and it can never begin with a tool message or end on a
        # dangling tool call because neither is pin-eligible
        # (Lean `pinned_never_tool`).
        prefix = [summary_message, ack_message] + pinned_kept
        compressed = prefix + recent_messages

        # Post-summary shrink guard. Only decidable now: the summary's size is the
        # model's choice, which is why Lean models it as an arbitrary function.
        # Lean: `monotone_shrink` — this inequality IS the theorem's hypothesis.
        overhead = self._count_chars([summary_message, ack_message])
        if span_chars <= pin_chars + overhead:
            log.warning(
                f"[COMPRESS] declining: summary+ack+pins ({pin_chars + overhead:,} "
                f"chars) would not fit under the {span_chars:,}-char span it "
                f"replaces. Nothing forwarded; conversation left untouched."
            )
            return self._refuse(REFUSAL_SUMMARY_TOO_LARGE, keep_from_idx,
                                f"pins+summary {pin_chars + overhead} >= span {span_chars}")

        if pinned_kept:
            log.info(
                f"[PIN] retaining {len(pinned_kept)} pinned message(s) verbatim "
                f"({pin_chars:,} chars) across the summary boundary"
            )

        original_chars = self._count_chars(messages)
        compressed_chars = self._count_chars(compressed)
        summary_chars = len(new_summary)
        recent_chars = self._count_chars(recent_messages)
        self.compression_count += 1
        if real_token_count:
            reduction = compressed_chars / original_chars if original_chars > 0 else 0
            estimated_output_tokens = int(real_token_count * reduction)
            self.total_tokens_saved += real_token_count - estimated_output_tokens
            log.info(
                f"Compression #{self.compression_count}: "
                f"~{real_token_count:,} -> ~{estimated_output_tokens:,} real tokens "
                f"({reduction:.0%} of original, "
                f"summary={summary_chars:,} chars, recent={recent_chars:,} chars)"
            )
        else:
            self.total_tokens_saved += (original_chars - compressed_chars) // 2
            log.info(
                f"Compression #{self.compression_count}: "
                f"{original_chars:,} -> {compressed_chars:,} chars "
                f"(summary={summary_chars:,}, recent={recent_chars:,})"
            )

        self.last_refusal = None
        return CompressionResult(
            messages=compressed,
            prefix=prefix,
            cut_index=keep_from_idx,
            pinned_count=len(pinned_kept),
            refusal=None,
            detail="ok",
        )

    def _refuse(self, code: str, cut_index: int, detail: str):
        """Record and return a refusal. Every decline goes through here so that
        none of them can be a bare `None` again."""
        self.last_refusal = {"code": code, "detail": detail}
        self.refusal_counts[code] = self.refusal_counts.get(code, 0) + 1
        return CompressionResult(
            messages=None, prefix=None, cut_index=cut_index,
            pinned_count=0, refusal=code, detail=detail,
        )

    def compress(self, messages: list, auth_headers: dict, real_token_count: int = None,
                 payload: dict = None) -> list:
        """Backwards-compatible wrapper: the compressed list, or None.

        Prefer compress_ex(). Callers that only test `is None` cannot tell a
        pin-saturated conversation from an empty one, and cannot learn the cut
        index without re-deriving it."""
        result = self.compress_ex(messages, auth_headers, real_token_count, payload)
        return result.messages
