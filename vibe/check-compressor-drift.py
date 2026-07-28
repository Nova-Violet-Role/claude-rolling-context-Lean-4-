#!/usr/bin/env python3
"""Fail when compressor.py and Compressor.lean stop describing the same thing.

WHY THIS EXISTS
---------------
A Lean file is green whatever the Python does. `Router.lean` was green for a week
while two of its theorems asserted the exact NEGATION of the shipped regex
(findings F1/F5). A proof that does not touch shipped code proves nothing about
shipped code, so the binding has to be mechanical and it has to fail loudly.

Four phases, all run, exit codes OR-ed. A structural complaint must NOT return
early: doing so suppresses the behavioural phase, which is the one that actually
executes the code.

  1. STRUCTURE  - constants and control flow that the Lean model assumes.
  2. CORPUS     - regenerate Compressor.lean's section 8 from compressor-cases.json
                  and diff. The Lean file cannot drift from the corpus.
  3. BEHAVIOUR  - run every corpus case through the REAL RollingCompressor and
                  compare all fifteen observables against Lean's values.
  4. ORDERING   - TRIGGER_TOKENS < auto_compact_threshold, checked against the
                  source AND the live /health, so an env-var override cannot slip
                  past. This is a config invariant with no code to protect it.

PHASE 2/3 MUST NOT FAIL OPEN. A `Drift` raised inside them fails (1). Only a
genuinely absent file skips. The lesson is from check-router-drift.py, where a
bare `except` once let a quote-style edit disable the corpus permanently and
silently.

  python check-compressor-drift.py              # check, exit 0/1
  python check-compressor-drift.py --emit-lean  # print the generated Lean block
"""

import json
import os
import re
import sys
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
PY = os.path.join(HERE, "compressor.py")
SERVER = os.path.join(HERE, "vibe-rc-server.py")
CASES = os.path.join(HERE, "compressor-cases.json")
LEAN = r"D:\Lean\proofs\Proofs\Compressor.lean"
CONFIG = os.path.expanduser(r"~\.vibe\config.toml")
HEALTH = "http://127.0.0.1:5590/health"

# The model alias that actually routes through this proxy. The stock
# "mistral-medium-3.5" entry shares the same `name`, so keying on `name` reads
# the wrong block; `alias` is the discriminator.
RC_ALIAS = "mistral-medium-3.5-rc"


class Drift(Exception):
    pass


def read(path):
    with open(path, encoding="utf-8") as fh:
        return fh.read()


# ---------------------------------------------------------------- phase 1

def _executable(text):
    """Strip docstrings and comments.

    Both directions matter. A "must not contain" test that reads comments raises
    a false alarm the moment someone DOCUMENTS the thing they removed - which is
    exactly what happened here: the docstring saying "it used to be a float
    `keep_ratio`" tripped the float check. A "must contain" test that reads
    comments is worse: it is satisfied by a fragment someone commented out.
    check-router-drift.py learned both the hard way."""
    text = re.sub(r'"""(?:.|\n)*?"""', "", text)
    text = re.sub(r"'''(?:.|\n)*?'''", "", text)
    return "\n".join(re.sub(r"#.*$", "", ln) for ln in text.split("\n"))


def _body(src, signature, path):
    """Extract a def body by signature, up to the next def at the same indent.

    Returns EXECUTABLE text only."""
    i = src.find(signature)
    if i < 0:
        raise Drift(f"{os.path.basename(path)}: `{signature}` is gone. "
                    f"The Lean model names it; renaming it silently unbinds the proof.")
    rest = src[i + len(signature):]
    m = re.search(r"\n    def ", rest)
    return _executable(rest[: m.start()] if m else rest)


def check_structure():
    """Facts Compressor.lean assumes about compressor.py's text."""
    problems = []
    src = _executable(read(PY))

    def want(cond, msg):
        if not cond:
            problems.append(msg)

    # -- refusal codes cross the boundary as strings; Lean compares them verbatim
    lean = read(LEAN)
    for code in ("nothingToCompress", "pinBudget", "summaryTooLarge"):
        want(f'"{code}"' in src,
             f"refusal code {code!r} missing from compressor.py")
        want(f'"{code}"' in lean,
             f"refusal code {code!r} missing from Compressor.lean outcomeCode")

    # -- D3: the budget must be over the BODY, never the whole array
    fki = _body(src, "def _find_keep_index(self, messages: list, keep_num: int, keep_den: int) -> int:", PY)
    want("self._count_chars(messages[head:])" in fki,
         "D3 REGRESSION: _find_keep_index no longer takes the total over "
         "messages[head:]. Taking it over the whole array makes the budget a "
         "fraction of the system prompt and compress() refuses forever.")
    want("total_chars * keep_num // keep_den" in fki,
         "the keep ratio is no longer integer arithmetic. Lean models it as "
         "Nat division (`keepTarget`); a float reintroduces an unprovable gap.")
    want("keep_ratio" not in fki,
         "a float `keep_ratio` is back in _find_keep_index.")
    want("max_idx = len(messages) - 4" in fki,
         "the `len - 4` retention pin is gone (Lean `maxIdx`, `retention_floor`).")
    want("if len(messages) - head <= 4:" in fki,
         "the short-conversation early return is gone.")
    want("return max(head, min(j, max_idx))" in fki and
         "return max(head, min(i + 1, max_idx))" in fki,
         "D3 REGRESSION: a return in _find_keep_index lost its `max(head, ...)` "
         "floor (Lean `findKeepIndex_ge_systemHead`).")

    # -- _safe_cut: four disjuncts and the clamp
    sc = _body(src, "def _safe_cut(self, messages: list, cut: int, floor: int) -> int:", PY)
    for frag, why in [
        ("self._has_tool_use(messages[cut - 1])", "prefix ends on a dangling tool call"),
        ('messages[cut - 1].get("role") == "system"', "prefix ends on a system message"),
        ('messages[cut].get("role") == "system"', "tail starts with a system message"),
        ('messages[cut].get("role") == "tool"', "tail starts with an orphan tool result"),
    ]:
        want(frag in sc, f"_safe_cut lost the guard against: {why} (Lean `badCut`)")
    want("return max(cut, floor)" in sc,
         "_safe_cut lost its clamp (Lean `safeCut_ge_floor` is then false).")
    want("while cut > floor and (" in sc, "_safe_cut's loop condition changed shape.")
    want("cut -= 1" in sc, "_safe_cut no longer steps DOWN; termination is Lean "
                           "`safeCutAux_enough`, which bounds the loop by `cut`.")

    # -- pin eligibility is structural and narrow (Lean `pinEligible`)
    pe = _body(src, "def _pin_eligible(self, message: dict) -> bool:", PY)
    want('message.get("role") != "user"' in pe,
         "D-O REGRESSION: _pin_eligible no longer restricts pins to role 'user'. "
         "Admitting 'assistant' lets the model pin its OWN output — measured on "
         "the shipped code, a 24-turn conversation fell from 82.4% compressed to "
         "13.5% with 110,928 chars of model output retained. Role binding in the "
         "MAC is NOT a substitute: it fails against anyone who can read "
         "state/pin-secret, which is a mode-0644 file every agent with a shell "
         "can read. This check is the half that survives that attacker.")
    want('"assistant"' not in pe,
         "D-O REGRESSION: _pin_eligible mentions 'assistant' again.")
    want("self._has_tool_use(message)" in pe,
         "_pin_eligible no longer rejects assistants carrying tool_calls - "
         "hoisting one orphans its results (Mistral 400).")
    want("self._is_synthetic(message)" in pe,
         "_pin_eligible no longer rejects the proxy's own summary/ack "
         "(Lean `synthetic_never_pinned`); a summary quoting the marker would "
         "pin itself and stack without bound.")
    syn = _body(src, "def _is_synthetic(self, message: dict) -> bool:", PY)
    want("_verify_summary_tag(text," in syn and "text == ACK_TEXT" in syn,
         "_is_synthetic no longer recognises both proxy-written messages. It must "
         "test the AUTHENTICATED marker: a bare `SUMMARY_MARKER in text` is what "
         "defect D-D exploited — forging it deleted two real messages unsummarized "
         "and fed attacker text to every later summarizer call as a prior summary.")

    # -- the pin scan must start at the system head, not start_idx
    want("self._pinned_in(messages, sys_head, keep_from_idx)" in src,
         "the pin scan no longer starts at sys_head. Starting it at start_idx "
         "makes Lean `pinned_preserved` conditional instead of unconditional.")

    # -- RETENTION MUST EQUAL AUTHENTICATION (Lean `pinExtract_le_pinChars`).
    # The MAC now covers a delimited span, not the whole message. Retaining the
    # whole message would let one tiny authenticated span drag an arbitrarily
    # large payload across the boundary verbatim — mint over nothing, keep
    # everything. The pre-review-5 whole-message MAC had no such gap (measured: a
    # valid tag plus 50,000 extra chars did not verify at all), so dropping the
    # extraction would be a straight trade of one defect for a worse one.
    pin_in = _body(src, "def _pinned_in(self, messages: list, lo: int, hi: int) -> list:", PY)
    want("self._pin_extract(m)" in pin_in,
         "_pinned_in retains whole messages again instead of the authenticated "
         "spans (Lean `pinnedIn` = filter then `map pinExtract`). One 3-byte pin "
         "span now carries an unbounded payload over the summary boundary.")
    pex = _body(src, "def _pin_extract(self, message: dict) -> dict:", PY)
    want('"\\n".join(spans)' in pex,
         "_pin_extract no longer rebuilds the message from its verified spans.")
    want('message.get("pinned") is True' in pex,
         "_pin_extract no longer passes the structural `pinned: true` channel "
         "through whole. That channel has no span to scope to, so extracting it "
         "would silently empty every sidecar pin.")

    # -- guard ORDER: every decline that is DECIDABLE before the API call must be
    # taken before it. REVIEW 4 (D-F) strengthened this. The old assertion listed
    # REFUSAL_SUMMARY_TOO_LARGE strictly AFTER _summarize_flattened, which encoded
    # an artefact of the implementation ("summaryTooLarge is only ever decided late")
    # rather than the safety property. There are now TWO summaryTooLarge sites and
    # the order between them is the invariant:
    #   pin saturation            -> pre-call  (no summary can shrink a saturated span)
    #   minimum-overhead floor    -> pre-call  (no summary FITS, whatever its length)
    #   exact overhead comparison -> post-call (needs the real summary's size)
    # Only the third genuinely requires having paid for a summary.
    ce = src[src.find("def compress_ex("):]
    stl = [m.start() for m in re.finditer("REFUSAL_SUMMARY_TOO_LARGE", ce)]
    want(len(stl) == 2,
         f"compress_ex has {len(stl)} summaryTooLarge refusal sites, expected 2 "
         f"(one pre-call minimum-overhead floor, one post-call exact comparison). "
         f"Losing the pre-call one means every hopeless span is paid for.")
    order = [ce.find("REFUSAL_NOTHING"), ce.find("if span_chars <= pin_chars:"),
             ce.find("_overhead_min"), (stl[0] if stl else -1),
             ce.find("_summarize_flattened"),
             ce.find("if span_chars <= pin_chars + overhead:"),
             (stl[1] if len(stl) > 1 else -1)]
    want(all(o > 0 for o in order) and order == sorted(order),
         "compress_ex's guard order changed. Pin saturation MUST be tested "
         "before the summarizer call (Lean `pin_saturation_refuses`): no summary "
         "of any size can shrink a saturated span, so calling the model wastes a "
         "request and a 300s cooldown to learn nothing.")

    # -- the server must not re-derive the cut index (defect D4)
    srv = _executable(read(SERVER))
    want("recent_count" not in srv,
         "vibe-rc-server.py is re-deriving the cut index by subtraction again. "
         "That is defect D4, and with hard memory it is wrong a second way: "
         "pinned messages are in the result but not in the verbatim tail. "
         "Use result.cut_index.")
    want("summarized = messages[sys_head:cut_index]" in srv,
         "the background hash chain no longer spans [sys_head, cut_index).")
    want("compressor.compress_ex(" in srv,
         "the server is back on compress(), which cannot report WHY it declined.")

    for p in problems:
        print(f"  DRIFT  {p}")
    return 1 if problems else 0


# ---------------------------------------------------------------- phase 2

CTOR = {"sys": "sys", "usr": "usr", "usrPin": "usrPin", "ast": "ast",
        "astCall": "astCall", "toolRes": "toolRes", "toolResPin": "toolResPin",
        "sumMsg": "sumMsg", "sumMsgPin": "sumMsgPin",
        # review 5: pins are delimited spans, so a message's size and its
        # AUTHENTICATED size can differ. `usrPinSpan n k` is n chars carrying a
        # k-char span; `astPin` is the self-pin attempt D-O has to refuse.
        "usrPinSpan": "usrPinSpan", "astPin": "astPin"}

BEGIN = "-- CORPUS-BEGIN (generated by check-compressor-drift.py; do not hand-edit)"
END = "-- CORPUS-END"


def emit_lean(data):
    """Render the generated half of Compressor.lean section 8.

    Deterministic: the checker regenerates this and compares byte for byte, so
    any hand edit here is drift by definition.

    `--emit-lean` PRINTS this block; it does NOT write Compressor.lean. Splicing
    it between CORPUS-BEGIN/CORPUS-END is manual.

    ENVIRONMENT HAZARD, third instance tonight across three different tools:
    this text is UTF-8 and carries `∧`, `→`, `≤`. Capturing it with
    `subprocess.run(..., text=True)` on this machine decodes as cp1252 and
    produces mojibake that LOOKS like a valid file and fails only at
    `lake build` with "expected token" (MEASURED: it did exactly that, and the
    same class ate an agent's emoji output and a Lean `→` print earlier the
    same night). Capture BYTES and `.decode("utf-8")`, then assert a glyph
    survived — e.g. `assert "∧" in block` — so a re-encoding fails loudly
    instead of writing a file that builds red an hour later."""
    out = [BEGIN]
    for case in data["cases"]:
        nm = case["name"]
        pol = case["policy"]
        e = case["expect"]
        # A spec entry is [kind, n] or, for the two-number kinds, [kind, n, k].
        items = [" ".join([CTOR[m[0]]] + [str(x) for x in m[1:]])
                 for m in case["msgs"]]
        lines, cur = [], "  ["
        for idx, it in enumerate(items):
            piece = it + ("," if idx < len(items) - 1 else "]")
            if len(cur) + len(piece) + 1 > 96:
                lines.append(cur)
                cur = "   "
            cur += piece + (" " if idx < len(items) - 1 else "")
        lines.append(cur.rstrip())
        out.append(f"def case_{nm} : Conv :=")
        out.extend(lines)
        out.append(f"def pol_{nm} : Policy := mkP {pol['num']} {pol['den']} "
                   f"{pol['summ']} {pol['ack']}")
        conj = [
            f"systemHead case_{nm} = {e['head']}",
            f"startIdx case_{nm} = {e['start']}",
            f"findKeepIndex case_{nm} {pol['num']} {pol['den']} = {e['fki']}",
            f"cutOf pol_{nm} case_{nm} = {e['cut']}",
            f"spanChars case_{nm} {e['cut']} = {e['span']}",
            f"pinChars case_{nm} {e['cut']} = {e['pinch']}",
            f"countChars case_{nm} = {e['inch']}",
            f"(case_{nm}.filter effectivePinned).length = {e['inpin']}",
            f'outcomeCode pol_{nm} case_{nm} = "{e["outcome"]}"',
            f"stepLen pol_{nm} case_{nm} = {e['step_len']}",
            f"stepChars pol_{nm} case_{nm} = {e['step_chars']}",
            f"stepPins pol_{nm} case_{nm} = {e['step_pins']}",
            f"(run pol_{nm} case_{nm}).length = {e['run_len']}",
            f"countChars (run pol_{nm} case_{nm}) = {e['run_chars']}",
            f"((run pol_{nm} case_{nm}).filter effectivePinned).length = {e['run_pins']}",
        ]
        out.append(f"theorem case_{nm}_spec :")
        out.append(f"    {conj[0]}")
        for c in conj[1:]:
            out.append(f"      \u2227 {c}")
        out.append("    := by")
        out.append("  refine \u27e8" + ", ".join(["rfl"] * len(conj)) + "\u27e9")
        out.append("")
    out.append(END)
    return "\n".join(out)


def check_corpus(data):
    lean = read(LEAN)
    if BEGIN not in lean or END not in lean:
        raise Drift("Compressor.lean has no CORPUS-BEGIN/CORPUS-END block. The "
                    "generated cases are the only mechanical binding between the "
                    "proof and the code; without them the proof is decorative.")
    have = lean[lean.index(BEGIN): lean.index(END) + len(END)]
    wantstr = emit_lean(data)
    if have.strip() != wantstr.strip():
        hl, wl = have.strip().split("\n"), wantstr.strip().split("\n")
        for i in range(max(len(hl), len(wl))):
            a = hl[i] if i < len(hl) else "<missing>"
            b = wl[i] if i < len(wl) else "<missing>"
            if a != b:
                raise Drift(f"Compressor.lean CORPUS block differs from "
                            f"compressor-cases.json at line {i + 1}:\n"
                            f"       lean: {a}\n     expect: {b}")
        raise Drift("Compressor.lean CORPUS block differs in trailing whitespace.")
    print(f"  corpus block matches ({len(data['cases'])} cases)")
    return 0


# ---------------------------------------------------------------- phase 3

def _pin_span(C, body, role="user"):
    """The wire shape `POST /pin` returns: `[PIN:<mac>]body[/PIN]`."""
    return f"{C.PIN_OPEN}{C._mint_tag(C.TAG_PIN, role, body)}]{body}{C.PIN_CLOSE}"


def _pin_span_overhead(C):
    """Chars a span costs on top of its body: open marker + tag + close."""
    return len(C.PIN_OPEN) + 16 + 1 + len(C.PIN_CLOSE)


def build_msgs(spec, C):
    """Corpus kinds -> Mistral-shaped dicts whose _count_chars is exactly n."""
    out = []
    for entry in spec:
        kind, n = entry[0], entry[1]
        k = entry[2] if len(entry) > 2 else None
        if kind == "sys":
            out.append({"role": "system", "content": "s" * n})
        elif kind == "usr":
            out.append({"role": "user", "content": "u" * n})
        elif kind == "ast":
            out.append({"role": "assistant", "content": "a" * n})
        elif kind == "usrPin":
            # An AUTHENTIC pin: an HMAC-tagged SPAN, as `POST /pin` mints them. A
            # bare marker is inert since the D-C fix — it is indistinguishable
            # from a model self-pin — so pasting one here made every pin case
            # report `run_pins: 0` and stopped the corpus from testing hard
            # memory at all. The whole message is one span, so Lean's
            # `usrPin n` has `pinChars = chars = n`.
            out.append({"role": "user",
                        "content": _pin_span(C, "u" * (n - _pin_span_overhead(C)))})
        elif kind == "usrPinSpan":
            # n chars total, of which only k are inside the span. The witness for
            # `pinExtract_le_pinChars`: without it the corpus only ever sees
            # messages where authenticated size equals message size, and the
            # theorem that retention is scoped to what was signed is read against
            # a set where the two coincide — vacuous.
            _body_len = k - _pin_span_overhead(C)
            out.append({"role": "user",
                        "content": ("q" * (n - k) + _pin_span(C, "p" * _body_len))})
        elif kind == "astPin":
            # A valid user-minted pin span copied verbatim into an ASSISTANT turn:
            # exactly the self-pin of defect D-O. Must be refused. Note the tag is
            # minted for role "user", which is what the model would have to hand;
            # `_pin_eligible` refuses it before the MAC even matters.
            out.append({"role": "assistant",
                        "content": _pin_span(C, "a" * (n - _pin_span_overhead(C)))})
        elif kind == "astCall":
            out.append({"role": "assistant", "content": "", "tool_calls": [
                {"id": "c1", "type": "function",
                 "function": {"name": "f", "arguments": "x" * (n - 1)}}]})
        elif kind == "toolRes":
            out.append({"role": "tool", "tool_call_id": "c1", "name": "f",
                        "content": "t" * n})
        elif kind == "toolResPin":
            # Authentically tagged AND still ineligible — that is the point of the
            # case (`pin_tool_ineligible`): a valid pin on a tool result must be
            # refused for wire-shape reasons, not because the tag failed. A bare
            # marker here would pass the case for the wrong reason.
            out.append({"role": "tool", "tool_call_id": "c1", "name": "f",
                        "content": _pin_span(C, "t" * (n - _pin_span_overhead(C)))})
        elif kind == "sumMsg":
            # A GENUINE proxy-written summary, i.e. one carrying a valid HMAC tag.
            # This used to paste the bare marker, which after the D-D fix is exactly
            # what a FORGERY looks like — so the fixture stopped representing a real
            # summary and `existing_summary`/`pin_synthetic` reported start=1
            # instead of 3. Minting the tag keeps the case testing what it names.
            _pad = "z" * (n - len(f"{C.SUMMARY_MARKER[:-1]}:{'0'*16}]"))
            out.append({"role": "user",
                        "content": f"{C.SUMMARY_MARKER[:-1]}:"
                                   f"{C._mint_tag(C.TAG_SUMMARY, 'user', _pad)}]" + _pad})
        elif kind == "sumMsgPin":
            # Same, plus a full authenticated PIN SPAN inside the summary text.
            # Two things at once, and both are load-bearing:
            #   * `synthetic_never_pinned` — a summary must not pin ITSELF, even
            #     when the span it quotes is genuinely valid;
            #   * defect D-N — the summary's own MAC must still verify with that
            #     span present. Before review 5 verification canonicalised with
            #     `_strip_tags`, which deleted every tag of BOTH kinds while
            #     minting used the raw body, so a summary quoting a pinned message
            #     failed its own MAC and the proxy stopped recognising its own
            #     work. SUMMARY_RULES orders the summarizer to preserve user
            #     instructions "EXACTLY as written", so this is the normal case,
            #     not a corner one.
            _inner = _pin_span(C, "y" * 8)
            _pad = (_inner + "z" * (n - len(f"{C.SUMMARY_MARKER[:-1]}:{'0'*16}]")
                    - len(_inner)))
            out.append({"role": "user",
                        "content": f"{C.SUMMARY_MARKER[:-1]}:"
                                   f"{C._mint_tag(C.TAG_SUMMARY, 'user', _pad)}]" + _pad})
        else:
            raise Drift(f"unknown corpus message kind {kind!r}")
    return out


def make_rc(C, pol, summ_chars):
    rc = C.RollingCompressor(trigger_tokens=1, target_tokens=pol["num"])
    # Size the stub body so the ASSEMBLED message is exactly `summ_chars`, which
    # is what the Lean policy's `summ` means. This subtracted the length of the
    # BARE `SUMMARY_MARKER` (25). Since the D-D fix the marker emitted carries an
    # HMAC tag and is 42 chars, so every assembled summary came out 17 too long
    # and two corpus cases reported `python = lean + 17`. The corpus was right and
    # the harness was wrong — worth stating, because the tempting "fix" is to add
    # 17 to the expected values until it goes green, which would have silently
    # moved the spec to match a harness bug.
    text_len = summ_chars - (len(f"{C.SUMMARY_MARKER[:-1]}:{C._mint_tag(C.TAG_SUMMARY, 'user', 'probe')}]")
                             + 1 + 1 + len(C.SUMMARY_END_MARKER)
                             + 2 + len(C.SUMMARY_TRAILER))
    if text_len < 0:
        raise Drift(f"case wants a {summ_chars}-char summary message, which is "
                    f"smaller than the fixed overhead")
    rc._summarize_flattened = lambda prompt, hdr: "S" * text_len
    rc._summarize_native = lambda *a, **k: "S" * text_len
    return rc


def run_case(C, case):
    pol, e = case["policy"], case["expect"]
    msgs = build_msgs(case["msgs"], C)
    rc = make_rc(C, pol, pol["summ"])
    rtc = None if (pol["num"], pol["den"]) == (1, 2) else pol["den"]

    got = {}
    got["head"] = rc._system_head(msgs)
    got["start"] = got["head"] + (2 if rc._has_summary(msgs) else 0)
    got["fki"] = rc._find_keep_index(msgs, pol["num"], pol["den"])
    got["cut"] = rc._safe_cut(msgs, got["fki"], got["start"])
    got["span"] = rc._count_chars(msgs[got["head"]:got["cut"]])
    got["pinch"] = rc._count_chars(rc._pinned_in(msgs, got["head"], got["cut"]))
    got["inch"] = rc._count_chars(msgs)
    got["inpin"] = len([m for m in msgs if rc._effective_pinned(m)])

    res = rc.compress_ex(msgs, {}, real_token_count=rtc)
    got["outcome"] = res.refusal or "ok"
    merged = msgs if not res.ok else msgs[:got["head"]] + res.messages
    got["step_len"] = len(merged)
    got["step_chars"] = rc._count_chars(merged)
    got["step_pins"] = len([m for m in merged if rc._effective_pinned(m)])

    # Iterate to a fixpoint, exactly as Lean's `run` does. This is the check that
    # convergence and pin preservation hold UNDER ITERATION in the real code, not
    # merely for one step.
    cur = msgs
    for _ in range(64):
        rc2 = make_rc(C, pol, pol["summ"])
        r = rc2.compress_ex(cur, {}, real_token_count=rtc)
        if not r.ok:
            break
        cur = cur[:rc2._system_head(cur)] + r.messages
    else:
        raise Drift(f"{case['name']}: compression did not converge in 64 rounds. "
                    f"Lean `run_fixpoint` says it must.")
    got["run_len"] = len(cur)
    got["run_chars"] = rc._count_chars(cur)
    got["run_pins"] = len([m for m in cur if rc._effective_pinned(m)])
    return got, rc


def check_behaviour(data):
    sys.path.insert(0, HERE)
    import compressor as C

    # The corpus states the two fixed sizes; recompute them from the real code.
    #
    # The marker EMITTED is not SUMMARY_MARKER. Since the D-D fix it carries an
    # HMAC tag — `[ROLLING_CONTEXT_SUMMARY:<16 hex>]`, 42 chars against the bare
    # constant's 25. Deriving the overhead from `len(C.SUMMARY_MARKER)` alone
    # under-counted every summary message by exactly 17, and this formula could
    # not see it because the constant it reads is still the untagged one. Mint a
    # real tag and measure, so the number tracks the code instead of describing a
    # string the proxy no longer writes.
    _emitted_marker = f"{C.SUMMARY_MARKER[:-1]}:{C._mint_tag(C.TAG_SUMMARY, 'user', 'probe')}]"
    overhead = (len(_emitted_marker) + 1 + 1 + len(C.SUMMARY_END_MARKER) + 2
                + len(C.SUMMARY_TRAILER))
    if overhead != data["summary_msg_overhead"]:
        raise Drift(f"summary message overhead is now {overhead}, corpus says "
                    f"{data['summary_msg_overhead']}. Every `summ` in the corpus "
                    f"and every expected char count in Compressor.lean moved.")
    if len(C.ACK_TEXT) != data["ack_chars"]:
        raise Drift(f"ACK_TEXT is now {len(C.ACK_TEXT)} chars, corpus says "
                    f"{data['ack_chars']}.")

    bad = 0
    for case in data["cases"]:
        got, rc = run_case(C, case)
        exp = case["expect"]
        diffs = [(k, exp[k], got[k]) for k in exp if exp[k] != got[k]]
        if diffs:
            bad += 1
            print(f"  DRIFT  case {case['name']}:")
            for k, want_v, got_v in diffs:
                print(f"           {k}: lean={want_v!r} python={got_v!r}")
        else:
            print(f"  ok     {case['name']:<20} {got['outcome']}")

        # ineligible pins must be REPORTED, not silently dropped
        if case["name"] == "pin_tool_ineligible":
            msgs = build_msgs(case["msgs"], C)
            rej = rc._pin_rejections(msgs)
            if not any(r["role"] == "tool" for r in rej):
                bad += 1
                print("  DRIFT  pin on a tool result was dropped SILENTLY. "
                      "A pin that quietly does nothing is defect D3's signature.")
    return 1 if bad else 0


# ---------------------------------------------------------------- phase 4

def _toml_active_alias(text):
    """The alias vibe will ACTUALLY select, i.e. `active_model`.

    REVIEW-6 DEFECT R6-7. This phase used to resolve `RC_ALIAS`, a hardcoded
    literal, and never read `active_model` at all (0 references). It reported a
    healthy 245,000 because the literal HAPPENED to equal line 7 of config.toml.
    MEASURED: that config also carries `alias = "mistral-medium-3.5"` with
    `auto_compact_threshold = 200000`. Changing one word on line 7 to select it
    would leave this gate GREEN while the real ordering became 200,000 < 220,000
    — inverted, native compaction winning, the proxy silently never firing. The
    one edit most likely to break the invariant was the one edit this check
    could not see.

    LIMIT, stated rather than implied: this reads ~/.vibe/config.toml only. A
    TRUSTED project `.vibe/config.toml` REPLACES the user config wholesale
    (vibe/core/config/default_orchestrator.py:35-38 selects one layer, it does
    not merge), dropping the threshold to vibe's built-in default of 200,000
    (core/config/_defaults.py:12) — below the trigger. That replacement is
    invisible here and CANNOT be detected from this file; it is a property of
    where vibe is launched from. Do not read this phase as covering it.
    """
    m = re.search(r'^active_model\s*=\s*"([^"]+)"\s*$', text, flags=re.M)
    if not m:
        raise Drift(f"no `active_model` in {CONFIG}; cannot tell which model's "
                    f"auto_compact_threshold actually governs.")
    return m.group(1)


def _toml_rc_threshold(text):
    """auto_compact_threshold of the [[models]] block vibe actually selects."""
    alias = _toml_active_alias(text)
    blocks = re.split(r"^\[\[models\]\]\s*$", text, flags=re.M)[1:]
    for b in blocks:
        if re.search(rf'^alias\s*=\s*"{re.escape(alias)}"\s*$', b, flags=re.M):
            m = re.search(r"^auto_compact_threshold\s*=\s*(\d+)\s*$", b, flags=re.M)
            if m:
                return int(m.group(1))
            raise Drift(f"the {alias} model block (active_model) has no "
                        f"auto_compact_threshold. "
                        f"0 or absent means vibe's ContextWarningMiddleware also "
                        f"returns early (middleware.py:121) and the warning is off.")
    raise Drift(f"active_model is {alias!r} but {CONFIG} has no [[models]] "
                f"block with that alias; the governing threshold is unknown.")


def check_ordering():
    """TRIGGER_TOKENS < auto_compact_threshold, from source, Lean AND the live proxy.

    A config invariant with no code defending it. Violating it is silent:
    everything runs, /health says ok, and the first long conversation is replaced
    wholesale by vibe's native compaction - the exact behaviour this proxy exists
    to prevent. Vibe's shipped default (200000) sits BELOW the trigger."""
    problems = []
    srv, lean = read(SERVER), read(LEAN)

    m = re.search(r'TRIGGER_TOKENS = int\(os\.environ\.get\("ROLLING_CONTEXT_VIBE_TRIGGER"\)'
                  r'\s*or\s*"(\d+)"\)', srv)
    if not m:
        raise Drift("cannot find TRIGGER_TOKENS in vibe-rc-server.py")
    trigger = int(m.group(1))
    m = re.search(r'TARGET_TOKENS = int\(os\.environ\.get\("ROLLING_CONTEXT_VIBE_TARGET"\)'
                  r'\s*or\s*"(\d+)"\)', srv)
    target = int(m.group(1))
    native = _toml_rc_threshold(read(CONFIG))

    def leanval(name):
        mm = re.search(rf"^def {name} : Nat := (\d+)$", lean, flags=re.M)
        if not mm:
            raise Drift(f"Compressor.lean has no `def {name}`")
        return int(mm.group(1))

    for nm, code_v, lean_v in [("TRIGGER_TOKENS", trigger, leanval("TRIGGER_TOKENS")),
                               ("TARGET_TOKENS", target, leanval("TARGET_TOKENS")),
                               ("AUTO_COMPACT_THRESHOLD", native,
                                leanval("AUTO_COMPACT_THRESHOLD"))]:
        if code_v != lean_v:
            problems.append(f"{nm}: shipped={code_v:,} but Compressor.lean says "
                            f"{lean_v:,}. The ordering theorems are then about "
                            f"numbers nothing uses.")

    if not trigger < native:
        problems.append(f"ORDERING INVERTED: rolling trigger {trigger:,} is not below "
                        f"auto_compact_threshold {native:,}. Native compaction wins "
                        f"the race and replaces the whole conversation with a lossy "
                        f"summary.")
    if not target < trigger:
        problems.append(f"target {target:,} is not below trigger {trigger:,}: every "
                        f"request would recompress immediately.")

    # live values, so an env override cannot slip past the source read
    try:
        # Empty ProxyHandler: never route a 127.0.0.1 probe through an ambient
        # HTTP_PROXY. On this box that would aim the probe at another proxy.
        opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
        with opener.open(HEALTH, timeout=3) as fh:
            live = json.load(fh)
    except Exception as exc:
        print(f"  note   proxy not reachable on 5590 ({exc.__class__.__name__}); "
              f"source values checked, live values not")
    else:
        if live.get("trigger_tokens") != trigger:
            problems.append(f"LIVE trigger is {live['trigger_tokens']:,} but the source "
                            f"default is {trigger:,} - an env override "
                            f"(ROLLING_CONTEXT_VIBE_TRIGGER) is in play, and it is the "
                            f"live value that races auto_compact_threshold.")
        if live.get("trigger_tokens", 0) >= native:
            problems.append(f"LIVE ORDERING INVERTED: {live.get('trigger_tokens'):,} "
                            f">= {native:,}.")
        print(f"  live   trigger={live.get('trigger_tokens'):,} "
              f"target={live.get('target_tokens'):,} native={native:,} "
              f"headroom={native - live.get('trigger_tokens', 0):,}")

    for p in problems:
        print(f"  DRIFT  {p}")
    return 1 if problems else 0


# ---------------------------------------------------------------- phase 5

def theorem_markers(src):
    """theorem name -> [LOAD-BEARING|DECORATIVE|INFRASTRUCTURE] or None.

    The marker is read from the contiguous doc comment that ENDS on the line
    immediately above the theorem. Requiring adjacency is deliberate: inserting a
    helper lemma between a doc comment and the theorem it describes silently
    re-points the claim at the wrong theorem, which happened once while writing
    this file."""
    lines = src.split("\n")
    out = {}
    for i, ln in enumerate(lines):
        m = re.match(r"^(?:private )?theorem (\w+)\s*[\s:({\[]", ln)
        if not m:
            continue
        name = m.group(1)
        j = i - 1
        if j < 0 or not lines[j].rstrip().endswith("-/"):
            out[name] = None
            continue
        while j >= 0 and not lines[j].lstrip().startswith("/--"):
            j -= 1
        blk = "\n".join(lines[j:i])
        # DEFECT D-G: this required a CLOSING BRACKET immediately after the word,
        # so it silently failed to match the real annotations in Compressor.lean —
        # `[LOAD-BEARING, and the prize]`, `[LOAD-BEARING, and the headline]`,
        # `[LOAD-BEARING via the drift checker]`. Only 18 of 65 theorems carried a
        # readable marker, and an UNMARKED theorem is skipped by both overclaim
        # branches below. The two theorems the file calls the prize —
        # `pinned_never_cut` and `pinned_preserved` — were therefore not audited by
        # the audit phase at all. A word boundary is the correct terminator.
        mk = re.search(r"\[(LOAD-BEARING|DECORATIVE|INFRASTRUCTURE)\b", blk)
        out[name] = mk.group(1) if mk else None
    return out


def check_inventory():
    """Every theorem is audited, and no theorem overclaims.

    A Lean file can say [LOAD-BEARING] in a comment forever; the comment is not
    checked by anything. This phase checks it against measured mutation results.
    The failure it exists to catch: someone adds a theorem, writes
    [LOAD-BEARING] above it, and it is in fact vacuous."""
    problems = []
    path = os.path.join(HERE, "compressor-mutations.json")
    rec = json.loads(read(path))
    killed = rec["killed_by"]
    markers = theorem_markers(read(LEAN))

    # Exemptions are DATA with a stated reason, not a silent skip in the script.
    exempt = rec.get("exempt", {})
    present_all = {n for n in markers if n != "below"}   # doc-prose false positive
    present = present_all - set(exempt)
    new = sorted(present - set(killed))
    if new:
        problems.append(
            f"{len(new)} theorem(s) in Compressor.lean were never mutation-tested: "
            f"{', '.join(new[:6])}. An untested theorem is an unaudited claim. "
            f"Run mutate-lean.py to regenerate compressor-mutations.json.")
    gone = sorted(set(killed) - present_all)
    if gone:
        problems.append(f"mutation record mentions {len(gone)} theorem(s) that no "
                        f"longer exist: {', '.join(gone[:6])}")

    for name in sorted(present & set(killed)):
        mk = markers.get(name)
        survived = not killed[name]
        if mk == "LOAD-BEARING" and survived:
            problems.append(
                f"{name} is marked [LOAD-BEARING] but survived every one of the "
                f"{len(rec['mutations'])} mutations. Either it is vacuous and the "
                f"marker is false, or the mutation set is missing the edit that "
                f"would break it - as happened with rolling_precedes_native, where "
                f"the mutation set only lowered the trigger to a value that still "
                f"satisfied the ordering. Fix one or the other; do not ship it.")
        if mk in ("DECORATIVE", "INFRASTRUCTURE") and not survived:
            problems.append(
                f"{name} is marked [{mk}] but IS load-bearing (killed by "
                f"{','.join(killed[name])}). Understating is safer than "
                f"overstating, but the inventory should be accurate.")

    lb = sum(1 for n in present & set(killed) if killed[n])
    # REVIEW-6: print BOTH counts. `len(present)` is "theorems this audit holds
    # accountable"; the file contains more, because exemptions are subtracted at
    # :676. Two careful readers with the file open spent a round disagreeing over
    # 109 vs 110 — neither wrong, they were different quantities. A counter that
    # is correct but does not say what it counts is the same surface-class this
    # gate exists to catch, one grade down: the next reader will not investigate,
    # they will pick whichever number suits and put it in a record.
    _exempt = sorted(present_all - present)
    _suffix = (f" / {len(present_all)} present "
               f"({len(_exempt)} exempt: {', '.join(_exempt)})") if _exempt else ""
    print(f"  {len(present)} theorems audited{_suffix}, {lb} load-bearing, "
          f"{len(present) - lb} survived all {len(rec['mutations'])} mutations")
    for p in problems:
        print(f"  DRIFT  {p}")
    return 1 if problems else 0


# ---------------------------------------------------------------- main

def check_server():
    """Invariants of vibe-rc-server.py that no theorem can reach.

    DEFECT D-B. Measured: of 45 mutations run against a sandbox copy, this tool
    caught 21/21 in compressor.py and **2/21** in the server. Every one of the
    misses below leaves the checker reporting CLEAN while the proxy is broken —
    including a verbatim reintroduction of defect D1, and the exact mutation that
    `system_prefix_preserved`'s own doc comment names as the thing it prevents.
    I reproduced the D1 miss by hand before writing this.

    The Lean model stops at `rebuild`. The server is what CALLS rebuild, merges
    its output back into the payload, and decides whether to forward the original
    instead — so a proof about rebuild says nothing about any of it. These are
    text assertions, deliberately: they are cheap, they run in ~5s, and a text
    assertion that fires is worth more than a theorem that cannot see the file.
    """
    problems = []
    checks = [0]      # DERIVED. The literal said "17" while 18 want() calls ran.
    src = _executable(read(SERVER))

    def want(cond, msg):
        checks[0] += 1
        if not cond:
            problems.append(msg)

    # -- D1 verbatim: the proactive block and the background twin BOTH need it.
    want(src.count("global _compression_failed_at") >= 2,
         "D1 REGRESSION: fewer than two `global _compression_failed_at`. Without "
         "it the assignment makes the name function-local and the read at the top "
         "of the proactive block raises UnboundLocalError, killing the handler "
         "thread the instant the trigger is crossed — the socket closes with no "
         "response and vibe reports 'Server disconnected without sending a "
         "response.'")

    # -- the compressed payload must actually be forwarded
    want(len(re.findall(r'payload\["messages"\] = merged\s*$', src, re.M)) >= 2,
         "the merged (compressed) message list is never written back into the "
         "payload, so every compression is computed, paid for, and discarded.")
    want("body = json.dumps(payload).encode()" in src,
         "the forwarded body is no longer re-serialized from the mutated payload; "
         "forwarding raw_body ignores compression entirely while /health still "
         "reports compression_count climbing.")

    # -- system prefix: the mutation `system_prefix_preserved`'s comment names
    want(src.count("messages[:sys_head]") + src.count("current_messages[:sys_head]") >= 2,
         "a merge no longer re-attaches the system prefix. Vibe carries `system` "
         "as an IN-ARRAY message at index 0, so this DELETES the system prompt — "
         "and the model keeps answering, so nothing looks broken.")
    want("def _system_prefix_len" in src and "return 0" not in
         _body(src, "def _system_prefix_len(messages: list) -> int:", SERVER),
         "_system_prefix_len is stubbed to 0; every cut floor collapses to index 0 "
         "and the system prompt becomes compressible.")

    # -- proactive compression (the race against native compaction)
    want("[PROACTIVE]" in src,
         "the proactive synchronous compression block is gone. Reactive-only "
         "compression loses the race to vibe's auto_compact_threshold, which "
         "replaces the whole conversation with a lossy summary.")
    want(src.count("merged_chars < msg_chars") >= 2,
         "the 'only forward the merge if it actually shrank' guard is gone.")

    # -- hashing must cover tool_calls (assistant content is routinely "")
    hm = _body(src, "def _hash_message(msg: dict) -> str:", SERVER)
    want("tool_calls" in hm,
         "_hash_message no longer hashes tool_calls. Two assistant turns with "
         "identical ('') content and different calls then collide, and find_match "
         "can splice a summary over the wrong messages.")
    want("tool_call_id" not in hm,
         "_hash_message now includes tool_call_id, which is volatile per request; "
         "hashes will never stabilise and every match will miss.")

    # -- volatile tags: unported, hashes never stabilise
    want('"user_cancellation"' in src or "user_cancellation" in src,
         "the volatile-tag list is empty. Tags from vibe/core/utils/tags.py must "
         "be stripped before hashing or no two requests ever hash alike.")

    # -- tool-pair validation must run, and must not eat the summary/pins (D-E)
    want("_validate_tool_pairs(" in src and src.count("_validate_tool_pairs(") >= 2,
         "_validate_tool_pairs is defined but never called; an orphaned tool "
         "message reaches Mistral and returns a hard 400.")
    vtp = _body(src, "def _validate_tool_pairs(messages: list) -> list:", SERVER)
    want("_effective_pinned" in vtp and "_is_synthetic" in vtp,
         "D-E REGRESSION: _validate_tool_pairs drops the whole leading run again, "
         "which deletes the [summary, ack] pair and every pinned message. "
         "`pinned_never_cut` is a theorem about rebuild; this function runs after "
         "it, so hard memory that survives compression is destroyed here instead.")

    # -- D-A: the key chain must skip the pinned block, not just [summary, ack]
    want(src.count("_effective_pinned(summarized[start])") >= 2,
         "D-A REGRESSION: a bare `start = 2` is back. With hard memory the prefix "
         "is [summary, ack] + pinned, so the key chain begins on a pinned message "
         "and can NEVER match: measured 46 paid summarizer calls vs 7, 45 dead "
         "stored entries, and a 4.1x context blowup with /health green throughout.")

    # -- pins are authenticated (D-C / D-D)
    csrc = _executable(read(PY))
    want("hmac.compare_digest" in csrc,
         "D-C REGRESSION: pin verification no longer uses a constant-time compare, "
         "or HMAC verification is gone entirely — a bare marker in model output "
         "would pin itself permanently.")
    want("_verified_pin_spans(self._msg_text(message)," in csrc,
         "D-C REGRESSION: _is_pinned is back to substring-matching PIN_MARKER, so "
         "any assistant reply or pasted document containing it pins itself.")
    want("_verify_summary_tag(content," in csrc,
         "D-D REGRESSION: _has_summary substring-matches SUMMARY_MARKER again. "
         "Forging it deletes two real messages unsummarized and feeds attacker "
         "text to every later summarizer call as an authoritative prior summary.")
    # -- D-P: the pin must be a DELIMITED SPAN, or the MAC covers the whole
    # message again and an inline pin is rejected `unauthenticated`.
    want("PIN_CLOSE" in csrc and "_PIN_SPAN_RE" in csrc,
         "D-P REGRESSION: the pin is no longer a delimited [PIN:…]…[/PIN] span, "
         "so it authenticates only when the pinned text is the ENTIRE message. "
         "Measured: that makes pins unusable under `vibe -p`, where the prompt is "
         "one message.")
    # -- D-N: the summary's canonical body must be recovered by removing ONLY the
    # summary's own tag, once. Anything broader disagrees with what minting signed.
    vst = _body(csrc, "def _verify_summary_tag(text: str, role: str) -> bool:", PY)
    want("count=1" in vst,
         "D-N REGRESSION: _verify_summary_tag no longer removes exactly one "
         "occurrence of its own tag. Minting signs the raw body, so any broader "
         "canonicalisation disagrees the moment the summary text contains "
         "anything tag-shaped — and SUMMARY_RULES orders the summarizer to quote "
         "user instructions EXACTLY, so a summary of a pinned message does. "
         "MEASURED live: _is_synthetic and _has_summary both went False, the "
         "summary chain was silently lost and the summary became pin-eligible.")
    want("_PIN_SPAN_RE" not in vst and "_PIN_TAG_RE" not in vst,
         "D-N REGRESSION: summary verification is canonicalising away PIN tags "
         "again. That is the mint/verify asymmetry that broke the summary chain.")
    # -- D-O: pins inside vibe's injected regions are model-controlled
    want("_VIBE_INJECT_RE" in csrc and "_pin_scan_text" in csrc,
         "the vibe-injection filter is gone. vibe puts MODEL-WRITTEN text into "
         "role='user' messages (the plan file, _loop.py:1499/:2413, wrapped in "
         "<vibe_warning>), and `injected=True` does not cross the wire, so "
         "without this a model can route a pin span into a user turn.")
    from_srv = _executable(read(SERVER))
    want("_VIBE_TAGS = (\"user_cancellation\", \"tool_error\", "
         "\"vibe_stop_event\", \"vibe_warning\")" in from_srv
         and '_VIBE_INJECT_TAGS = ("user_cancellation", "tool_error", '
             '"vibe_stop_event", "vibe_warning")' in csrc,
         "the injected-tag lists in compressor.py and vibe-rc-server.py no longer "
         "agree. They are duplicated so compressor.py imports standalone; a tag in "
         "one and not the other is a hole in whichever is missing it.")

    # -- background machinery
    want("threading.Thread" in src,
         "the background compression thread is never started; compression only "
         "ever happens on the synchronous path.")
    want("FAILURE_COOLDOWN" in src,
         "the post-failure cooldown is gone; a failing summarizer is re-hammered "
         "on every single request.")

    # -- S06: an EMPTY key chain must never match. Without the guard a stored
    # compression becomes a WILDCARD that splices a stale summary into an unrelated
    # conversation. There was no assertion for this at all.
    want("if not oh:" in src or "if not stored_hashes:" in src,
         "the empty-key-chain guard is gone. An empty chain matches everything, so "
         "a stored summary can splice into an arbitrary conversation.")

    # -- S09: hash a PREFIX of the content and collisions become a silent splice.
    # NOTE `hexdigest()[:16]` is the DIGEST length and is fine; what must never
    # appear is slicing of the message content itself.
    want("content[:" not in hm and 'raw = f"{role}:{content}{extra}"' in hm,
         "_hash_message hashes only a prefix of the content. Two long messages "
         "sharing an opening then collide and find_match splices over the wrong span.")

    # -- S15: `compare_digest` being present says nothing about how many characters
    # reach it. The MAC must be compared whole, and pinned at 16 hex chars.
    want("m.group(1), _mint_tag(" in csrc,
         "the tag comparison no longer feeds the WHOLE captured tag to "
         "compare_digest — truncating it to 4 chars reduces the MAC to 16 bits "
         "while every other assertion here still passes.")
    want("{16}" in csrc, "the tag regex no longer pins the tag at 16 hex characters.")

    # -- S16: the secret must PERSIST; rotating it on start silently unpins
    # everything already tagged — this file's recurring silent-no-op class.
    want("_PIN_SECRET_PATH" in csrc and "os.path.exists(_PIN_SECRET_PATH)" in csrc,
         "the pin secret is no longer loaded from disk, so it rotates on every "
         "restart and every existing pin silently stops being honoured.")

    # -- S24: /pin must mint over the CALLER'S text, not a constant
    want('_mint_tag(TAG_PIN, "user", text)' in src,
         "POST /pin no longer mints over the request text under role 'user'; a "
         "constant body would authenticate the wrong text, and any other role "
         "would mint a tag that verifies against nothing — a silent no-op, which "
         "is defect D3's failure class.")
    mp = _body(src, "    def _handle_mint_pin(self):", SERVER)
    want('if role != "user":' in mp,
         "POST /pin will mint tags for roles other than 'user'. `_pin_eligible` "
         "refuses those structurally, so the route would hand back a tag that can "
         "never work and say nothing about it.")

    # -- DOMAIN SEPARATION + ROLE BINDING. Measured on the live proxy before each
    # existed: a /pin tag verified under the SUMMARY marker, making the route a
    # forgery oracle; and a valid pin copied into an assistant turn authenticated,
    # so the model self-pinned (82.4% -> 13.5% compressed, 110,928 chars retained).
    want("_frame(kind, role, body)" in csrc,
         "DOMAIN SEPARATION / ROLE BINDING GONE: _mint_tag no longer commits to "
         "the tag KIND and the carrying message's ROLE. Without kind, one tag "
         "authenticates under BOTH markers and POST /pin becomes a summary-forgery "
         "oracle. Without role, a valid pin copied into an assistant turn "
         "authenticates and the model pins its own output (D-O).")
    fr = _body(csrc, "def _frame(*parts: str) -> bytes:", PY)
    want('str(len(b)).encode("ascii")' in fr,
         "_frame no longer length-prefixes its parts. A separator byte is "
         "injective only while no part can contain it, and `role` comes straight "
         "out of request JSON where a NUL is legal — so one byte string could "
         "decode as two different (kind, role, body) triples.")

    # -- D-E: the rescue must be STRUCTURAL, and the sweep must exist
    want("def _rescue_eligible(" in src and "_rescue_eligible(m)" in src
         and src.count("_drop_broken_tool_groups(") >= 2,   # def AND call
         "the tool-pair sanitizer lost its structural rescue test or its final "
         "sweep. Content-only rescue lifts a tool result whose text equals ACK_TEXT "
         "out of a dropped run and emits a STABLE orphan — re-running the sanitizer "
         "does not repair it, so the session wedges on a Mistral 400.")

    # -- D-A gates must be authenticated, BOTH of them
    want("SUMMARY_MARKER in summarized[0]" not in src,
         "a D-A key-chain gate is back to a bare marker substring test while "
         "_is_synthetic is authenticated — forged text can steer the key chain.")

    # ------------------------------------------------------------------
    # REVIEW 4: text assertions the mutation sweep proved blind.
    # 30 semantic mutations were run against a sandbox copy; 18 survived the 27
    # assertions above. The ones below close the survivors that a text test can
    # actually see; the rest are closed behaviourally in check_server_behaviour().
    # ------------------------------------------------------------------

    # M14: every assertion above passes if _mint_tag stops using HMAC entirely.
    # `hmac.compare_digest` being present says nothing about how the tag is MADE.
    mt = _body(csrc, "def _mint_tag(kind: str, role: str, body: str) -> str:", PY)
    want("hmac.new(PIN_SECRET" in mt,
         "M14: _mint_tag no longer computes an HMAC keyed by PIN_SECRET. A plain "
         "digest is offline-forgeable — anyone who can read this file can mint a "
         "tag for any body, and every other pin assertion still passes.")
    want('"surrogatepass"' in fr or '"strict"' in fr,
         "M-D-M: _frame encodes with a lossy error handler. errors='replace' maps "
         "every unencodable code point onto '?', so two different bodies share one "
         "valid MAC (measured with a lone surrogate).")

    # M24: the /pin route must mint PIN-kind tags. Asserting the call text is not
    # enough — aliasing TAG_SUMMARY to the name TAG_PIN at the import keeps the
    # call site byte-identical and turns the route back into a forgery oracle.
    want("TAG_SUMMARY" not in _body(src, "    def _handle_mint_pin(self):", SERVER),
         "M24: the /pin handler references TAG_SUMMARY. Minting summary-kind tags "
         "on an unauthenticated route re-opens the forgery oracle domain "
         "separation exists to close.")
    want(re.search(r"from compressor import [^\n]*\bTAG_PIN\b(?![^\n]*as TAG_PIN)",
                   src) is not None
         and "as TAG_PIN" not in src,
         "M24: TAG_PIN is bound by an alias at the import, so the constant the "
         "/pin route mints under is not the one it appears to mint under.")

    # M27: this asserted only the ABSENCE of the old bad form. Replacing the whole
    # gate with a constant adds no forbidden string and sailed through.
    want(src.count("compressor._is_synthetic(summarized[0])") >= 2,
         "M27: a D-A summary gate is no longer an authenticated _is_synthetic call "
         "on summarized[0] (both sites must be). Replaced by a constant, the key "
         "chain starts in the wrong place and every later request misses.")

    # M22: single-site presence. The forwarded body is re-serialized in more than
    # one place; asserting the string exists somewhere does not prove the POST
    # path uses it.
    want(len(re.findall(r"^\s*body = json\.dumps\(payload\)\.encode\(\)\s*$",
                        src, re.M)) >= 2,
         "M22: a request path no longer re-serializes the mutated payload, so the "
         "compression is computed and then the ORIGINAL body is forwarded.")

    # M17/M18: pin eligibility is the whole of `pinEligible`; nothing asserted it.
    pe = _body(csrc, "    def _pin_eligible(self, message: dict) -> bool:", PY)
    want('message.get("role") != "user"' in pe,
         "M18: _pin_eligible no longer gates on role. System, tool and ASSISTANT "
         "messages become pinnable; hoisting a tool result orphans its call "
         "(Mistral 400), and an assistant pin is defect D-O — the model making "
         "its own output unshrinkable.")
    want("_has_tool_use(message)" in pe,
         "M17: _pin_eligible no longer rejects tool-carrying messages, so pinning "
         "an assistant tool call hoists it over the boundary and orphans its "
         "results.")
    want("not self._is_synthetic(message)" in pe,
         "M16: _pin_eligible no longer excludes the proxy's own summary/ack, so a "
         "summary can pin ITSELF and stack without bound (synthetic_never_pinned).")

    # M07/M08. With the review-4 sweep in place these two are no longer detectable
    # from the OUTPUT: a wrongly rescued tool result is dropped again by the final
    # sweep, so wire-legality is identical either way. They are asserted as text
    # because they are defence in depth, and saying which of the two it is matters:
    # after D-K/D-L, `_rescue_eligible`'s structural gates are NOT load-bearing for
    # legality. They stop the rescue lifting half a tool group out of a dropped run.
    re_ = _body(src, "def _rescue_eligible(msg: dict) -> bool:", SERVER)
    want('msg.get("role") not in ("user", "assistant")' in re_,
         "M07: _rescue_eligible lost its role gate. Content-only rescue lifts a "
         "tool result whose text happens to equal ACK_TEXT out of a dropped run.")
    want('msg.get("tool_calls") or msg.get("tool_call_id")' in re_,
         "M08: _rescue_eligible lost its tool-field gate, so it can rescue one "
         "half of a tool group and leave the other behind.")

    # M26: a zero-length secret from disk was accepted.
    want("len(secret) >= 32" in csrc,
         "M26: the persisted pin secret is accepted at any length, including "
         "empty, which makes every tag forgeable by anyone who can create the file.")

    for p in problems:
        print(f"  DRIFT  {p}")
    if not problems:
        print(f"  ok     {checks[0]} server invariants hold")
    return 1 if problems else 0


def check_server_behaviour():
    """RUN the sanitizer and the tag algebra, rather than reading them.

    REVIEW 4. Of 30 semantic mutations, 18 survived the text assertions in
    check_server(). Nine of those gutted `_validate_tool_pairs` /
    `_drop_broken_tool_groups` while leaving every name, call count and anchored
    literal intact — a text assertion cannot see the difference between a sanitizer
    and `return messages`. These checks import the module and execute it.

    Post-conditions asserted, which are exactly what Mistral enforces:
      P1  no tool result without its call EARLIER   ("Unexpected role 'tool'")
      P2  no tool call without a result LATER       ("Not the same number of
                                                     function calls and responses")
      P3  idempotence  P4  system prefix survives at index 0
    """
    problems = []
    checks = [0]

    def want(cond, msg):
        checks[0] += 1
        if not cond:
            problems.append(msg)

    import importlib.util
    spec = importlib.util.spec_from_file_location("_rc_server_beh", SERVER)
    srv = importlib.util.module_from_spec(spec)
    sys.modules["_rc_server_beh"] = srv
    if HERE not in sys.path:
        sys.path.insert(0, HERE)
    import logging
    _prev = logging.root.manager.disable
    logging.disable(logging.CRITICAL)
    try:
        spec.loader.exec_module(srv)
        comp = __import__("compressor")

        def A(ids):
            return {"role": "assistant", "content": "c",
                    "tool_calls": [{"id": i, "function": {"name": "f"}} for i in ids]}
        def T(t):
            return {"role": "tool", "content": "r", "tool_call_id": t}
        U = {"role": "user", "content": "u"}
        S = {"role": "system", "content": "SYS"}

        def legal(out):
            known, ok = set(), True
            res = {}
            for i, m in enumerate(out):
                if m.get("role") == "tool":
                    res.setdefault(m.get("tool_call_id"), []).append(i)
            for i, m in enumerate(out):
                if m.get("role") == "assistant":
                    for tc in m.get("tool_calls") or []:
                        if isinstance(tc, dict) and tc.get("id"):
                            known.add(tc["id"])
                elif m.get("role") == "tool":
                    if m.get("tool_call_id") not in known:
                        ok = False
            for i, m in enumerate(out):
                if m.get("role") == "assistant" and m.get("tool_calls"):
                    ids = [tc.get("id") for tc in m["tool_calls"] if isinstance(tc, dict)]
                    if not ids or not all(
                            t and any(j > i for j in res.get(t, ())) for t in ids):
                        ok = False
            return ok

        # Each case names the mutation it exists to kill.
        cases = [
            ("dangling call, no orphan anywhere (M01/M04: the vf==0 early return)",
             [S, A(["a"]), U]),
            ("sanitizer is identity (M02)", [S, T("ghost"), A(["k"]), T("k"), U]),
            ("orphan result at head (M03)", [S, T("ghost"), A(["k"]), T("k"), U]),
            ("result BEFORE its call (M06: set-based, order-blind sweep)",
             [S, T("z"), A(["z"]), U]),
            ("duplicate id, one group incomplete (M05: single-pass sweep)",
             [S, A(["x"]), T("x"), A(["x", "y"]), U]),
            ("assistant tool_calls with no usable id",
             [S, {"role": "assistant", "content": "c",
                  "tool_calls": [{"function": {"name": "f"}}]}, U]),
            ("ack-texted tool result must NOT be rescued (M07/M08: D-E)",
             [S, A(["A"]), {"role": "tool", "content": comp.ACK_TEXT,
                            "tool_call_id": "A"},
              T("GHOST"), U]),
            # CASCADE. The prefix walk sees nothing wrong (every tool_call_id is
            # known), so the sweep is the only defence, and one pass is not enough:
            # dropping the assistant for its unanswered "b" ORPHANS the "a" result
            # that was legal a moment earlier. Kills "pass 1 removed" (M03) and
            # "fixpoint reduced to one pass" (M05) together.
            ("assistant with one answered and one unanswered call (M03/M05 cascade)",
             [S, A(["a", "b"]), T("a"), U]),
            # A second call re-using a live id, whose only result lies BEFORE it.
            # Set-membership says satisfied; position says dangling (M06).
            ("second call satisfied only by an EARLIER result (M06)",
             [S, A(["a"]), T("a"), A(["a"])]),
        ]
        for name, msgs in cases:
            out = srv._validate_tool_pairs([dict(m) for m in msgs])
            want(legal(out), f"BEHAVIOUR: _validate_tool_pairs emits an illegal "
                             f"payload for [{name}]. Mistral rejects this with a "
                             f"hard 400 and the session wedges.")
            out2 = srv._validate_tool_pairs([dict(m) for m in out])
            want(out2 == out, f"BEHAVIOUR: _validate_tool_pairs is not idempotent "
                              f"for [{name}] — re-running it does not reach a fixed "
                              f"point, so the payload is never repaired.")
            want(bool(out) and out[0].get("role") == "system",
                 f"BEHAVIOUR: the system prefix is not at index 0 after "
                 f"sanitizing [{name}] (M10) — vibe carries the system prompt as "
                 f"an in-array message, so this deletes it.")

        # -- tag algebra, executed (M13/M14/M15/M30)
        b = "remember: the port is 5590"
        pin_tag = comp._mint_tag(comp.TAG_PIN, 'user', b)
        sum_tag = comp._mint_tag(comp.TAG_SUMMARY, 'user', b)
        want(pin_tag != sum_tag,
             "BEHAVIOUR: _mint_tag returns the SAME tag for both kinds over one "
             "body — domain separation is gone, so /pin is a summary-forgery "
             "oracle and the summary tag can be lifted onto [PIN:] (M13/M15).")
        rc_ = comp.RollingCompressor()

        def _span(body, role="user"):
            return (f"{comp.PIN_OPEN}{comp._mint_tag(comp.TAG_PIN, role, body)}]"
                    f"{body}{comp.PIN_CLOSE}")

        pinned = _span(b)
        want(rc_._is_pinned({"role": "user", "content": pinned}),
             "BEHAVIOUR: a span this proxy just minted does not verify — pins are "
             "inert and every pin silently does nothing.")
        want(not comp._verify_summary_tag(
                 f"{comp.SUMMARY_MARKER[:-1]}:{pin_tag}]\n{b}", "user"),
             "BEHAVIOUR: a PIN tag authenticates under the SUMMARY marker (M13).")
        want(not rc_._is_pinned({"role": "user",
                                 "content": f"{comp.PIN_OPEN}{sum_tag}]{b}{comp.PIN_CLOSE}"}),
             "BEHAVIOUR: a SUMMARY tag authenticates inside a [PIN:] span (M13).")

        # -- D-O, executed. The single highest-value check in this file: the same
        # bytes that pin a user turn must do nothing in an assistant turn.
        want(not rc_._is_pinned({"role": "assistant", "content": pinned}),
             "D-O REGRESSION (executed): a valid pin copied verbatim into an "
             "ASSISTANT turn still authenticates. The model can make its own "
             "output permanently unforgettable and unshrinkable — measured at "
             "82.4% -> 13.5% compression with 110,928 chars of model output "
             "retained.")
        want(not rc_._effective_pinned({"role": "assistant", "content": _span(b, "assistant")}),
             "D-O REGRESSION (executed): an assistant turn is pin-ELIGIBLE again. "
             "Role binding in the MAC does not cover this — anyone who can read "
             "state/pin-secret mints an assistant-role tag — so the structural "
             "refusal is what has to hold.")

        # -- D-P, executed: a pin must work INLINE, not only as a whole message.
        want(rc_._effective_pinned({"role": "user",
                                    "content": "please remember " + pinned + " thanks"}),
             "D-P REGRESSION (executed): an inline pin is rejected. The MAC is "
             "covering the whole message again, which makes pins unusable in any "
             "session where the prompt is a single message (`vibe -p`).")

        # -- retention == authentication, executed
        big = {"role": "user", "content": "J" * 40000 + pinned + "K" * 40000}
        ext = rc_._pin_extract(big)
        want(ext["content"] == pinned,
             "BEHAVIOUR: _pin_extract does not reduce a message to its "
             "authenticated spans. One small span now drags an unbounded payload "
             "over the summary boundary (Lean `pinExtract_le_pinChars`).")
        want(rc_._pin_extract(ext) == ext,
             "BEHAVIOUR: _pin_extract is not idempotent, so a pin shrinks a little "
             "on every round until it is gone (Lean `pinExtract_idem`).")
        want(rc_._effective_pinned(ext),
             "BEHAVIOUR: an extracted pin no longer verifies, so it survives one "
             "round and then silently stops being a pin.")

        # -- D-N, executed. A summary that QUOTES a pin must still be its own.
        # SUMMARY_RULES orders the summarizer to preserve user instructions
        # "EXACTLY as written", so this is the ordinary case.
        for label, text in (("plain", "1. did a thing"),
                            ("quoting a pin span", "1. user pinned: " + pinned),
                            ("quoting a summary tag",
                             "1. saw [ROLLING_CONTEXT_SUMMARY:0123456789abcdef]")):
            sb = f"{text}\n{comp.SUMMARY_END_MARKER}\n\n{comp.SUMMARY_TRAILER}"
            sm = {"role": "user",
                  "content": f"{comp.SUMMARY_MARKER[:-1]}:"
                             f"{comp._mint_tag(comp.TAG_SUMMARY, 'user', sb.strip())}]\n{sb}"}
            want(rc_._is_synthetic(sm),
                 f"D-N REGRESSION (executed): the proxy's OWN summary [{label}] "
                 f"fails its own MAC, so it is not recognised as synthetic. The "
                 f"summary chain is silently lost (every round re-summarizes from "
                 f"scratch) and the summary message becomes pin-eligible.")
            want(rc_._has_summary([{"role": "system", "content": "s"}, sm]),
                 f"D-N REGRESSION (executed): _has_summary is False for a real "
                 f"summary [{label}], so start_idx stops skipping the "
                 f"[summary, ack] pair and re-summarizes it as conversation.")

        # -- vibe-injected regions, executed
        inj = {"role": "user",
               "content": f"<vibe_warning>plan updated:\n{pinned}</vibe_warning>"}
        want(not rc_._effective_pinned(inj),
             "BEHAVIOUR: a pin span inside <vibe_warning> is honoured. vibe puts "
             "MODEL-WRITTEN plan-file text there (_loop.py:1499), so this is a "
             "route by which model output pins itself through a user-role message.")
        want(any(r.get("code") == "injected" for r in rc_._pin_rejections([inj])),
             "BEHAVIOUR: a pin refused for sitting in an injected region is "
             "dropped SILENTLY. That is defect D3's signature.")

        # -- collisions and offline forgery
        want(comp._mint_tag(comp.TAG_PIN, "user", "\ud800")
             != comp._mint_tag(comp.TAG_PIN, "user", "?"),
             "BEHAVIOUR: two distinct bodies collide under _mint_tag (lossy "
             "encode). One MAC authenticates more than one message.")
        want(comp._mint_tag(comp.TAG_PIN, "user\x00x", "y")
             != comp._mint_tag(comp.TAG_PIN, "user", "\x00xy"),
             "BEHAVIOUR: (kind, role, body) does not have a unique encoding — a "
             "NUL in `role`, which arrives straight from request JSON, re-frames "
             "the MAC input so one tag covers two different triples.")
        # the secret must matter: a tag must not be reproducible without it
        want(comp._mint_tag(comp.TAG_PIN, 'user', b) !=
             __import__("hashlib").sha256(
                 comp._frame(comp.TAG_PIN, "user", b)).hexdigest()[:16],
             "BEHAVIOUR: the tag equals an unkeyed digest of (kind, role, body) — "
             "the MAC is forgeable offline by anyone (M14).")

        # -- M15: the two channels must stay crossed-off in _is_synthetic too.
        # Verifying under the wrong KIND makes a user's own pinned message count as
        # proxy-written, which both exempts it from pinning and lets it steer the
        # D-A key chain. Asserting _mint_tag's separation does not cover this.
        want(not rc_._is_synthetic({"role": "user", "content": pinned}),
             "BEHAVIOUR: a PIN-tagged user message is reported as SYNTHETIC (M15). "
             "_is_synthetic is verifying under the wrong tag kind, so the proxy "
             "mistakes the user's hard memory for its own summary.")

        # -- R6-1: the REPORTED summarizer model must equal the model the send
        # path actually puts on the wire.
        #
        # This is the assertion whose absence let the defect live. `/health`
        # advertised `summarizer_model: "(session model)"` while
        # _summarize_flattened ignored the payload entirely and sent
        # LEGACY_DEFAULT_MODEL. Four audits read that field and believed it.
        # Review 5 fixed the CONSTANT and left the REPORT lying; measured live on
        # both 5590 and 5591 afterwards, /health still answered "(session model)".
        #
        # The check does NOT re-implement the model choice — re-implementing it is
        # how the docstring drifted in the first place. It CAPTURES the real
        # request by standing in for the socket, so whatever _summarize_flattened
        # decides to send is what gets compared.
        _sent = {}

        class _FakeResp:
            status = 200
            def read(self):
                return json.dumps({
                    "choices": [{"message": {"content": "SUMMARY"}}],
                    "content": [{"type": "text", "text": "SUMMARY"}],
                }).encode()

        class _FakeConn:
            def request(self, method, path, body=None, headers=None):
                _sent["body"] = body
            def getresponse(self):
                return _FakeResp()
            def close(self):
                pass

        _real_conn = comp._summarizer_conn
        try:
            comp._summarizer_conn = lambda *a, **k: _FakeConn()
            rc_wire = comp.RollingCompressor(trigger_tokens=100, target_tokens=50)
            out = rc_wire._summarize_flattened("PROMPT", {})
            wire_model = json.loads(_sent["body"])["model"]
            want(out == "SUMMARY",
                 "R6-1 harness: the captured summarizer round-trip did not return "
                 "the canned summary, so the capture below proves nothing.")
            want(wire_model == rc_wire.effective_summarizer_model(),
                 f"R6-1 REGRESSION: /health reports summarizer model "
                 f"{rc_wire.effective_summarizer_model()!r} but the send path put "
                 f"{wire_model!r} on the wire. The status surface is describing an "
                 f"intention the code does not carry out — the exact shape that hid "
                 f"the devstral default through four audits.")
            # and with an explicit model configured, BOTH must follow it
            rc_wire2 = comp.RollingCompressor(trigger_tokens=100, target_tokens=50,
                                              summarizer_model="explicit-probe-model")
            rc_wire2._summarize_flattened("PROMPT", {})
            wire_model2 = json.loads(_sent["body"])["model"]
            want(wire_model2 == "explicit-probe-model"
                 and rc_wire2.effective_summarizer_model() == "explicit-probe-model",
                 f"R6-1 REGRESSION: with ROLLING_CONTEXT_VIBE_MODEL set, the wire "
                 f"model is {wire_model2!r} and the reported model is "
                 f"{rc_wire2.effective_summarizer_model()!r}; both must be the "
                 f"configured value.")
        finally:
            comp._summarizer_conn = _real_conn

        # -- R6-4: `hsan`, the hypothesis of Compressor.lean's `forwarded_shrinks`,
        # bound to the code it is about.
        #
        # That theorem says a successful step shrinks the FORWARDED payload
        # provided the post-rebuild sanitizer only ever drops messages. Lean
        # cannot prove that of Python, so the hypothesis is discharged HERE, by
        # execution: `_validate_tool_pairs` must return a SUBSEQUENCE of its
        # input. If a future repair makes it synthesise a placeholder tool result
        # — a natural fix for an orphaned call — the hypothesis fails, and with it
        # the only proof that compression shrinks anything on the wire.
        #
        # Exhaustive over every message sequence up to length 4 across 8 shapes.
        # The same check to length 5 (37,449 inputs) also passes; 4 keeps the gate
        # fast. This makes the Lean hypothesis MEASURED, never PROVED.
        import itertools as _it
        _S = {"role": "system", "content": "SYS"}
        _U = {"role": "user", "content": "u"}
        _AP = {"role": "assistant", "content": "plain"}
        _alpha = [_S, _U, _AP, A(["a"]), A(["b"]), T("a"), T("b"), T("ghost")]

        def _is_subseq(out, inp):
            it = iter(inp)
            return all(any(o == i for i in it) for o in out)

        _viol = _grew = _n = 0
        for _k in range(0, 5):
            for _combo in _it.product(_alpha, repeat=_k):
                _inp = [dict(m) for m in _combo]
                _n += 1
                _out = srv._validate_tool_pairs([dict(m) for m in _inp])
                if not _is_subseq(_out, _inp):
                    _viol += 1
                if comp.RollingCompressor()._count_chars(_out) > \
                        comp.RollingCompressor()._count_chars(_inp):
                    _grew += 1
        want(_viol == 0,
             f"R6-4 REGRESSION: _validate_tool_pairs returned a NON-subsequence of "
             f"its input on {_viol} of {_n} exhaustive inputs. Compressor.lean's "
             f"`forwarded_shrinks` assumes `(san x).Sublist x`; with that false, "
             f"nothing proves the forwarded payload is smaller than what it "
             f"replaced, and `forwarded_shrink_needs_drops_only` shows the "
             f"conclusion genuinely fails without it.")
        want(_grew == 0,
             f"R6-4 REGRESSION: _validate_tool_pairs GREW the payload on {_grew} of "
             f"{_n} exhaustive inputs. A sanitizer that manufactures content turns "
             f"a logged compression into a measured expansion.")

        # The health handler must be WIRED to that function, not to a copy of its
        # answer. A literal here is what regressed last time.
        _health = _body(read(SERVER), "def _handle_health", SERVER)
        want("effective_summarizer_model()" in _health,
             "R6-1 REGRESSION: _handle_health no longer derives the summarizer "
             "model from compressor.effective_summarizer_model(); a hand-written "
             "value here drifts from the send path silently.")
        want("(session model)" not in _health,
             "R6-1 REGRESSION: the literal '(session model)' is back in "
             "_handle_health. It is FALSE for the flattened path, which is the "
             "path production takes.")

        # -- R6-6: /health's `pin_auth` must be DERIVED from the shipped verifier,
        # not asserted. It was the literal "hmac" through six reviews: true by
        # inspection every time, and bound to nothing, so a degraded verifier
        # would keep reporting "hmac". Lock both halves — the text (no literal)
        # and the behaviour (the derivation actually discriminates).
        want("pin_auth_scheme()" in _health,
             "R6-6 REGRESSION: _handle_health no longer derives pin_auth from "
             "compressor.pin_auth_scheme(); a literal there makes /health assert "
             "a SECURITY property it is not bound to.")
        want('"pin_auth": "hmac"' not in _health,
             "R6-6 REGRESSION: the bare literal '\"pin_auth\": \"hmac\"' is back "
             "in _handle_health.")
        import compressor as _cmod
        _pa = _cmod.RollingCompressor()
        want(_pa.pin_auth_scheme() == "hmac",
             f"R6-6: pin_auth_scheme() reports {_pa.pin_auth_scheme()!r} on the "
             f"shipped verifier — pin authentication is not intact.")
        # And prove the report is not a constant wearing a function's clothes: a
        # verifier that accepts forgeries must change the answer.
        _orig_spans = _cmod._verified_pin_spans
        try:
            _cmod._verified_pin_spans = lambda text, role: re.findall(
                r"\[PIN:[0-9a-f]+\].*?\[/PIN\]", text)
            want(_pa.pin_auth_scheme().startswith("DEGRADED"),
                 "R6-6: pin_auth_scheme() still answered 'hmac' while the verifier "
                 "accepted forged tags — the derivation is decorative.")
        finally:
            _cmod._verified_pin_spans = _orig_spans

        # Second vector, at the PRIMITIVE rather than the wrapper: break the
        # comparison `_mint_tag`'s callers rely on. Stronger than patching
        # `_verified_pin_spans`, because it stays a real mutation even if the
        # scheme check is later rewritten to inline its own scanning.
        _orig_cd = _cmod.hmac.compare_digest
        try:
            _cmod.hmac.compare_digest = lambda a, b: True
            want(_pa.pin_auth_scheme().startswith("DEGRADED"),
                 "R6-6: with compare_digest forced True (every MAC 'valid'), "
                 "pin_auth_scheme() did not report DEGRADED.")
            _cmod.hmac.compare_digest = lambda a, b: False
            want(_pa.pin_auth_scheme().startswith("BROKEN"),
                 "R6-6: with compare_digest forced False (no MAC ever valid), "
                 "pin_auth_scheme() did not report BROKEN.")
        finally:
            _cmod.hmac.compare_digest = _orig_cd
        want(_pa.pin_auth_scheme() == "hmac",
             "R6-6: pin_auth_scheme() did not return to 'hmac' after the probe "
             "restored compare_digest — the mutation leaked.")
    except Exception as exc:  # a sanitizer that raises is also a defect
        problems.append(f"BEHAVIOUR: executing the server module raised {exc!r}")
    finally:
        logging.disable(_prev)

    for p in problems:
        print(f"  DRIFT  {p}")
    if not problems:
        print(f"  ok     {checks[0]} behavioural invariants hold")
    return 1 if problems else 0


def main():
    # The emitted Lean uses U+2227; the Windows console is cp1252 by default and
    # would raise UnicodeEncodeError on the way out.
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass
    data = json.loads(read(CASES))

    if "--emit-lean" in sys.argv:
        print(emit_lean(data))
        return 0

    rc = 0
    print("[1/7] structure")
    try:
        rc |= check_structure()
    except Drift as exc:
        print(f"  DRIFT  {exc}")
        rc = 1
    except FileNotFoundError as exc:
        print(f"  SKIP   {exc}")

    print("[2/7] corpus block")
    try:
        rc |= check_corpus(data)
    except Drift as exc:
        print(f"  DRIFT  {exc}")
        rc = 1
    except FileNotFoundError as exc:
        print(f"  SKIP   {exc}")

    print("[3/7] behaviour")
    try:
        rc |= check_behaviour(data)
    except Drift as exc:
        print(f"  DRIFT  {exc}")
        rc = 1

    print("[4/7] threshold ordering")
    try:
        rc |= check_ordering()
    except Drift as exc:
        print(f"  DRIFT  {exc}")
        rc = 1

    print("[5/7] server invariants")
    try:
        rc |= check_server()
    except Drift as exc:
        print(f"  DRIFT  {exc}")
        rc = 1
    except FileNotFoundError as exc:
        print(f"  SKIP   {exc}")

    print("[6/7] server behaviour (executed, not read)")
    try:
        rc |= check_server_behaviour()
    except Drift as exc:
        print(f"  DRIFT  {exc}")
        rc = 1
    except FileNotFoundError as exc:
        print(f"  SKIP   {exc}")

    print("[7/7] theorem inventory vs measured mutations")
    try:
        rc |= check_inventory()
    except Drift as exc:
        print(f"  DRIFT  {exc}")
        rc = 1
    except FileNotFoundError as exc:
        print(f"  SKIP   {exc}")

    print("DRIFT" if rc else "CLEAN")
    return rc


if __name__ == "__main__":
    sys.exit(main())
