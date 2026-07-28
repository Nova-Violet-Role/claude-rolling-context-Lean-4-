# Review 6 — rolling-context proxy

*2026-07-28.*

Two agents, one adversarial pass. Every claim that **could** be re-derived was re-derived from the
tree by the agent who did *not* write it; the exceptions are marked inline where they appear.
Anything that could not be re-derived at all was struck — see **Retractions**, which is not an
appendix but the most important section here, and **Scope**, which says what was never examined.

Counts in this document are *as-of*. Both gates print live values; regenerate rather than trust the
page. File hashes are deliberately **not** recorded: they went stale twice within an hour while this
was being written, which is itself the argument.

---

## Running the gates

Neither gate was referenced anywhere in this plugin tree before this review (`grep -c` over `README.md`: 0). Both must pass before any change ships.

There is **no bare `python`, `python3`, or `py` on PATH** on this machine, in
either shell — `python check-compressor-drift.py` exits **127**. Go through `uv`.
(`lake` *is* on PATH, via elan.) Both commands below were run verbatim and pass.

```bash
# Behavioural + structural gate. Read the exit code directly — never through a pipe.
cd ~/.vibe/nestor-plugins/rolling-context/proxy
PYTHONIOENCODING=utf-8 uv run --no-project python check-compressor-drift.py
#   expect: CLEAN, exit 0

# Kernel-checked gate. The Python corpus is compiled into Lean `rfl` specs, so a
# Python/Lean disagreement fails the BUILD, not merely the checker.
cd /d/Lean/proofs && lake build Proofs.Compressor
#   expect: exit 0, 0 sorry
```

`PYTHONIOENCODING=utf-8` is not decoration: this toolchain emits `∧ → ≤`, and a
cp1252 default mangles them.

If `uv` is ever absent, the interpreter can be called directly — this depends on
nothing but the filesystem, but it pins a version in the path, so check what is
installed with `ls ~/AppData/Roaming/uv/python/` before trusting it:

```bash
PY="$HOME/AppData/Roaming/uv/python/cpython-3.14.2-windows-x86_64-none/python.exe"
PYTHONIOENCODING=utf-8 "$PY" check-compressor-drift.py
```

### Adding a corpus case

Not obvious from the code, and the gate will stop you halfway if you guess:

1. append to `compressor-cases.json` (expectations come from the checker's own
   `run_case`, never hand-computed)
2. `uv run --no-project python check-compressor-drift.py --emit-lean` — this **prints**; it does not
   write `Compressor.lean`. Splice it between `CORPUS-BEGIN`/`CORPUS-END`
   yourself, capturing **bytes** and decoding UTF-8. Capturing with
   `subprocess.run(..., text=True)` silently produces mojibake that fails only
   later at `lake build`.
3. `lake build Proofs.Compressor` — each case becomes an `rfl`-proved spec
4. `uv run --no-project python mutate-lean.py` — otherwise phase 7 fails with *"never mutation-tested:
   an untested theorem is an unaudited claim"*
5. `uv run --no-project python check-compressor-drift.py` — all seven phases

As-of state:

| gate | result |
|---|---|
| drift | `CLEAN`, exit 0 — 18 corpus cases, 46 server invariants, 63 behavioural invariants |
| inventory | 115 theorems audited / 116 present (1 exempt: `strongRec`), 102 load-bearing, 13 survived all 66 mutations |
| lake | exit 0, 0 `sorry`, 0 `sorryAx` |

The behavioural invariants are **executed**, not read. That distinction is the subject of this review.

---

## Five defects and one unbound assumption

Five were the same class — a *surface asserting a property it was not bound to* — and each fix
makes the surface **execute** what it claims and report the outcome. **R6-4 is a different kind**
and is marked as such: nothing there asserted anything false; a Lean hypothesis was simply relied on
without ever being measured. It is listed here for traceability, not to borrow severity from R6-3
and R6-7.

| id | surface | what it asserted | what was true | fix |
|---|---|---|---|---|
| **R6-1** | `/health` `summarizer_model` | the model doing the summarising | a stale literal; the wire sent `mistral-large-2512` | `effective_summarizer_model()` derives it from the send path |
| **R6-2** | generator's port rule | agents point at the configured proxy | port hardcoded; scratch runs silently hit the **live** proxy | `PROXY_PORT = os.environ.get("CAVEMAN_PROXY_PORT") or "5590"` |
| **R6-3** | `_pin_eligible` role check | (deleted as "redundant" by a reviewer subagent mid-audit) | the sole control preventing model self-pinning | restored, with a `DO-NOT-SIMPLIFY` rationale |
| **R6-4** *(not a defect — unbound assumption)* | Lean hypothesis on the sanitizer | assumed drops-only | never measured either way | subsequence gate, executed over a sweep |
| **R6-6** | `/health` `pin_auth` | `"hmac"` — a hardcoded string | true only by coincidence | `pin_auth_scheme()` mints a tag and forges one; reports `DEGRADED`/`BROKEN` on either failure |
| **R6-7** | threshold ordering check | trigger < native compaction threshold | resolved a hardcoded alias; **0** references to `active_model` | `_toml_active_alias()` reads `config.toml:7` |

### R6-3 — the reviewer edited the file it was auditing

A reviewer subagent deleted the role check in `_pin_eligible` as redundant. It is not redundant.
Measured counterfactually in an isolated process, by re-implementing `_pin_eligible` with the role
test removed and restoring it in a `finally`:

```
with the restored role check : BLOCKED
with the role check DELETED  : SELF-PIN POSSIBLE   ← defect D-O restored
```

D-O is not theoretical. Review 5 reproduced it end-to-end: a 24-turn conversation went from 82.4% to
13.5% compressed, with 110,928 chars of model output pinned permanently and unshrinkably. *(Those
two figures are review 5's; they were not re-derivable in this pass.)* The check is also the sole
reason the anomaly-(b) mitigation below is safe to use.

### R6-4 — what the sanitizer must actually guarantee

The obligation is **not** "the sanitizer is drops-only on every conceivable conversation". It is
drops-only on **the conversations `rebuild` actually produces**. The empirical sweep therefore
*over-satisfies* the real obligation, which is the correct direction for an empirical hypothesis to
err. The gate enforces an exhaustive length-4 sweep (4,681 inputs); a wider one-off probe covered
37,449 inputs, with 0 non-subsequences in both.

If you add a case to that corpus, the gate will stop you halfway unless you also regenerate the
mutation record — see **Adding a corpus case** above, step 4 (`mutate-lean.py`). Phase 7 refuses a
theorem it has never mutated, on the grounds that an untested theorem is an unaudited claim.

### R6-7 — reachable by following this repo's own documentation

The demonstration was "change one word on `config.toml:7`". That is not a hypothetical edit:

- `README.md`, § **Wiring** — *"the stock `mistral-medium-3.5` entry is left in place — reverting is
  one word"*. The one-word switch is not incidental; it is documented design intent, deliberately
  kept available as the revert mechanism.
- `README.md`, § **Uninstall**, step 1 — *"Set `active_model = "mistral-medium-3.5"`"*

*(Those two are cited by section and quoted string rather than by line. Both were originally line
citations, and both were dead within the hour — see the note at the end of* **Retractions** *.)*

That alias carries `auto_compact_threshold = 200000`, below the proxy's 220,000 trigger. **Killing
the proxy is step 2.** So performing step 1 alone leaves the proxy running with the ordering
inverted and the proxy silently never firing — and before this fix the gate reported 25,000 headroom
and went green on exactly that state. This is a property of the documented procedure's ordering, not
a claim about how anyone behaves.

---

## Retractions

Both were confidently reported and both were wrong. They sit at the same prominence as the findings,
because a review that publishes only its successes is the same unbound surface it set out to fix.

**R6-5 never existed.** Reported as: the streaming token-count fallback estimates from the *response*
buffer — a ~31,000× undercount. Measured: it reads `_count_chars(messages)`, the **request**
(`vibe-rc-server.py:1020`; assignment at `:1339`). Re-derived independently:

```
4-char request      →      1 token
10,000-char request →  2,500 tokens
40,000-char request → 10,000 tokens
```

Proportionate. The original code comment — *"degrades accuracy, not correctness"* — was correct, as
was the README paragraph saying the same. The finding was an artifact of a test fixture that planted
`prompt_tokens: 31337` in the reply to a 4-character probe; the executable check faithfully reported
a contradiction that existed only in the fixture. The false severity had already been written into
the audited file as a code comment before it was caught.

**The threshold inversion was misreported.** Reported as: vibe compacts at 200,000 before the proxy
fires at 220,000, so the proxy never runs. That 200,000 belongs to the **non-active** alias. The
shipped ordering is correct — 245,000 native above a 220,000 trigger. The inversion is real only as
a *consequence* of config replacement or of the revert/uninstall step above.

---

**A line-number citation into a file that the same change-set edits is a surface asserting a
location it is not bound to.** This document originally cited `README.md:39-40` and `README.md:120`.
Both were correct when written and dead by the time they shipped: two insertions into that README —
made *by this review* — pushed the quoted text to `:65` and `:156`. The R6-7 section, whose entire
purpose is to show that a documented procedure is dangerous, pointed at a **blank line**. Nobody saw
it until every citation was *resolved* rather than read; five of seven held, and the two that rotted
were exactly the two pointing into the file this session edited.

The fix is not "be careful with line numbers". It is to anchor prose citations to content that moves
*with* the text — a section name plus a quoted string. Line numbers are kept for **code**, where a
symbol name makes them recoverable: `compressor.py:774 _is_pinned` is still findable at 780 next
month; `README.md:120` is not findable at all.

---

## The transferable result

All five defects were one class: **a surface asserting a property it was not bound to** — true when
written, or true for a reason nobody checked. (R6-4, the sixth item, was never a defect: it was an
assumption nobody had bound in either direction. The remedy was the same one, which is why it sits
here.) The fix that worked every time was identical: make the
surface *execute* what it claims and report the outcome. `effective_summarizer_model()`,
`pin_auth_scheme()` minting and forging, `_toml_active_alias()` reading line 7, the sanitizer
sweep, and proxy-side `[PIN] retaining` in place of an agent reciting a word.

**That discipline has a failure mode, and it produced the worst error of the review:** a probe whose
*fixture* asserts something the system cannot corroborate. R6-5's probe was executable and bound to
the real send path, and was confidently wrong, because nobody asked whether the fixture's own numbers
were consistent with the input fed to it.

It then propagated. The second agent "independently verified" R6-5 by reading the log the first
agent's proxy had written from that same fixture. **Convergence on a shared artifact is
amplification, not corroboration.** Only re-derivation from an independent fixture caught it —
neither an unbound assertion nor an executable one would have.

The sharpest evidence that the verification had to be **cross-agent rather than self-administered**
came while this document was being written. Within the same ten minutes: one agent documented a gate
command it had never typed (`python …`, which exits 127 on this machine — no `python`, `python3` or
`py` on PATH in either shell), inside the document cataloguing that exact class; the other then
"fixed" that command from a **stale read**, contradicting a file the first agent had already
corrected. Same defect, opposite directions, neither self-caught, each caught by the other
immediately. Self-review would have shipped both.

**The dominant error shape was not a wrong measurement — it was a true measurement standing in for a
larger claim.** It recurred three times, and every instance survived because the underlying numbers
were correct: 8/8 agents reciting a canary (real recitations, but they cannot distinguish retention
from compression never firing); a fleet regression built on 4 of 7 subagents (four real transcripts,
proving delegation, not coverage); and a six-defect count in which one item was an unbound assumption
rather than a defect (a real hardening, borrowing severity from its neighbours in the same table).
Checking arithmetic never catches this. The question that does is *what is the smallest claim these
numbers actually support* — and in all three cases it was asked by the agent who had not produced
them.

Two related lessons, earned the same way:

- An earlier "8/8 pins survived" result came from agents *reciting* a canary word, which cannot
  distinguish retention from *compression never having fired*. Struck, then re-measured proxy-side.
- **Mutation testing cannot detect an unnecessary hypothesis** — breaking the model kills the
  theorem either way. Each review-6 theorem was therefore restated with a hypothesis removed and
  rebuilt. `forwarded_shrinks` assumed a universal `∀ x : Conv, (san x).Sublist x` where the proof
  applies it at exactly one point; the pointwise version builds, and remains load-bearing.
  `decline_chain_unbounded`'s `hstuck` is genuinely required — dropping it fails to build.

---

## Scope — what was NOT examined

This section exists because its absence is what turns a review into a false assurance. Everything
below is untested, not tested-and-passing.

**Fleet coverage — complete, but only after the gap was caught.** The tree holds 8 agent TOMLs:
`caveman-ultra` (the only `agent_type = "agent"`) and **7 subagents**, six `cavecrew-*` plus
`explore`. Final coverage is **7 of 7 subagents plus the router, across two router runs**, delegation
verified by child transcripts on disk rather than by the router's stdout, which never names the crew.

The first run exercised only 4 of the 7 and was reported as the fleet regression. `cavecrew-builder`,
`cavecrew-prover` and `explore` had never been invoked. Every number in that report was true; the
claim they supported was larger than they were — four separate session transcripts proved
*delegation*, and that was allowed to stand in for *coverage of the fleet*, the same shape as the
struck 8/8 canary. Closing the gap does not unmake the reasoning error, which is why this paragraph
stays. The second run closed it: all three returned
substantive work (`explore` → `_pin_eligible`/`_pin_extract`/`findKeepCore` sites; `builder` → a
guard clause, stated not applied, as instructed; `prover` → `safeCut_ge_floor` for the floor clamp,
independently naming a theorem already measured surviving [M05,M22,M29]).

The crew is reachable **only through the router**: `--agent` refuses 7 of the 8, because
`agent_type = "subagent"` cannot be a primary agent. "Eight invocable agents" was never the shape of
this system.

**Run shape.** Two router runs, one prompt shape each, `--max-turns 40`, headless `-p` only. No
interactive TUI. Windows only. Nothing was run on another OS or another shell.

**Streaming.** The SSE usage parser was exercised **only against a fake upstream** serving canned
`chat.completion.chunk` objects. It has never run against a live key, and vibe's own headless mode
sends `stream:false`, so live traffic has never reached that branch.

**NATIVE summarizer mode.** Unported and untested. `SUMMARIZER_FORMAT` defaults to `openai`, which
disables NATIVE; nothing in this review touched it.

**`upstream/`.** The frozen canonical 1.8.0 tree was read for diffing and **never executed**.

**The trust finding.** Measured through vibe's own `TrustedFoldersManager` and a layer-resolution
probe. Vibe was **never launched from a hijacked repository** to observe the replacement end to end,
so the consequence chain is inferred from vibe's own resolution code rather than observed on a
running agent.

**Refusal branches.** `summaryTooLarge` is now exercised **in the wild** — the second run produced
`refusal_counts = {'summaryTooLarge': 4}`, with 27 `summaryTooLarge` and 30 `declining` log events:
the compressor refusing to ship a summary that would not fit under the span it replaces. Correct
defensive behaviour, first observed on real fan-out traffic rather than in the corpus. `pinBudget`
remains **corpus-only** and has never been observed live.

**Pin retention — the two channels differ, and the record said this backwards until the last hour.**

*Authenticated SPAN channel — LIVE-VERIFIED.* The fleet runs compressed real transcripts with the
real `mistral-large-2512` against the real API: **25 `[PIN] retaining` events** between 20:50:56 and
00:21:34, and **7 of 7** compressions answered `Upstream response: 200 OK` (both figures re-derived
independently by each agent, on the same log with different instruments).

That status line is emitted by `vibe-rc-server.py:1207`
(`log.info(f"[MSG] Upstream response: {resp.status} {resp.reason}")`), and it is the most load-bearing
citation in this section: finding it is what turned criterion 3 from a behavioural inference — *"the
runs completed, so the payload must have been accepted"* — into a read status. It also made a
recording forward-proxy unnecessary, which would have added a network hop production does not have to
the very thing being measured. Both agents had previously scanned this log for `HTTP 400` and
`Bad Request` and found nothing, because the substring is `Upstream response:`; one of those scans
also returned a 1,786-count fiction from `status.*400` matching header values.

*Structural `pinned: true` channel — STUB-ONLY, and cannot be otherwise today.* Every observation of
it, on either rig, came from a hand-built POST against a stub. It has never appeared in live traffic
and **cannot** until something emits the flag: vibe emits `"pinned"` **0 times**.

The initial version of this paragraph asserted the inverse. It survived because both agents had
written it and neither re-read it against the evidence — the same shape as everything else here, one
level up, in the document about that shape.

*How the channel attribution is established, and its limit.* The log records retention **counts and
character lengths, never content**, so the retained text cannot be read back. The attribution rests
on three measurements: no `"pinned"` producer exists in vibe; the traffic was vibe's own router and
subagents; and the modal retained length is **84 chars ×11 of 25**, which is byte-for-byte the length
of the canary span `[PIN:6f45e3dd3243e1cb]…OBSIDIAN-LYNX-3390[/PIN]` (56-char body + 22 open + 6
close). A structural pin retains the **whole message**, whose length has no reason to coincide with a
span's. Strong, but an inference: if a `"pinned"` emitter is ever found, it moves.

*Stub-only for both channels* is the deliberate **two-round idempotence** test — feeding a forwarded
conversation back to confirm the proxy re-verifies its own summary rather than stacking one, and that
pins survive a second pass. Run on **two independently built rigs** whose thresholds happened to
differ, which mattered: on one, round two did not re-cross the trigger, demonstrating survival across
a **pass-through**; on the other it did, demonstrating survival across an **actual second
compression**, with the stored summary reused under an identical tag. Matched rigs would have shown
one case and called it the general one.

**Tokenizer accuracy.** `chars // 4` was confirmed *proportionate*, never calibrated against real
tokenization. The residual error is unmeasured and needs a live key.

---

## Open items

**1. Drive-wide trust + whole-config replacement — highest severity, unresolved, requires an operator
decision.** Trust covers `C:\`, `D:\`, `R:\`. `default_orchestrator.py:35-38` selects a single config
layer rather than merging, so any repo's `.vibe/config.toml` **wholly replaces** the user config —
dropping the proxy, switching models, and taking `auto_compact_threshold` to vibe's built-in default
of 200,000 (`_defaults.py:12`), below the trigger. **No gate that reads only `~/.vibe/config.toml` from the proxy directory can detect this** — the
launch directory is not knowable from there. Detection is *possible*: resolving the layer stack the
way vibe does for a given directory is exactly what `probe_layer.py` did when it measured
`winner=project trusted=True` from a planted repo. That is a fix nobody has built, not an
impossibility. Stated as a limit in
`_toml_active_alias`'s docstring rather than papered over.

**2. Anomaly (b) — tool-borne pins.** Tool results are unretainable **by construction**: retention
preserves role (`_pin_extract`) and role is inside the MAC (`_mint_tag`, D-O), so carrying tool text
across the boundary requires either orphaning a tool call or re-signing tool output under user
authority. In observed crew traffic tool results ran near 1:1 with assistant turns (`assistant=87 /
tool=89` across 6 transcripts / 182 messages), so fan-out-heavy conversations lose pins.

*A mitigation exists.* A **user-role mirror message carrying structural `pinned: true`**
(`compressor.py:774`) is effectively pinned, weakens no MAC, and round-trips — `_pin_extract`
preserves the flag. Measured:

| message | `_is_pinned` | `_pin_eligible` | effective |
|---|---|---|---|
| `role:tool` + `pinned:true` | True | False | **False** |
| `role:user` mirror + `pinned:true` | True | True | **True** |
| `role:assistant` + `pinned:true` | True | False | **False** |
| `role:user` + `pinned:true` + `tool_calls` | True | False | **False** |

Injected, the mirror message is ordinary JSON in the request body — no marker, no MAC, no `/pin`
call, because the authority is the API caller rather than anything lifted out of conversation text:

```json
{ "role": "user",
  "content": "[mirror] tool result worth keeping: OBSIDIAN-LYNX-3390",
  "pinned": true }
```

Place it immediately after the tool result it mirrors. `_pin_extract` keeps the whole message,
flag included, so it re-verifies on every subsequent round without re-signing.

Both channels are verified at wire level on two independently built rigs: the structural flag
retains the **whole message**, while an authenticated `[PIN:…]…[/PIN]` span retains **only the
verified span**, discarding surrounding prose — different code paths, both observed. Only the SPAN
channel has run on live traffic (see **Scope**); the structural channel is stub-only for want of a
producer. Mint
spans with `POST /pin`, which fixes `role="user"` and supplies the MAC's `kind` internally; minting
by hand is how a review-4 domain separation was tripped during this review, and it failed closed.

Vibe emits `"pinned"` **0 times**, so there is no producer today — the channel is available to a
sidecar, or by hand: **keep anything that must survive in a user-role message.** Residual risk,
stated rather than left to be discovered: `pinned: true` bypasses the MAC by design, so anything able
to shape the request body can pin arbitrarily, and every agent here has shell access. Bounded to the
attacker's own conversation, and self-pinning is still blocked — **by the R6-3 role check**.

**3. Corpus coverage of `_safe_cut` — now proved, not merely covered.** The `badCut` disjuncts went
from **1 of 4** to **4 of 4**
mutation-detectable. The two added cases (`dangling_call`, `sys_boundary_tail`) do **not** appear in
observed traffic — 0 occurrences across 6 transcripts / 182 messages. They are mutation detectors
over the code, not distribution samples. That is not an argument against them: a dangling call is
what an *interrupted* turn produces, and the sample contained only clean completions. Measuring clean
traffic to judge a guard that exists for the non-clean case is the wrong instrument.

**Both of those results were subsequently PROVED rather than measured** (`Compressor.lean`, section
12). Independence of all four disjuncts had been empirical over an 18-case corpus; the masking
explanation — *"in a well-formed transcript an `astCall` is always followed by its `toolRes`, so D4
fires at that boundary first"* — had been reasoning. Both are now kernel-checked over the walk
semantics, so neither depends on the corpus containing the right examples.

The section is **three faithfulness lemmas guarding three results**, and the lemmas are the load-bearing
part:

| | theorem | what it secures |
|---|---|---|
| faithfulness (predicate) | `badCutNo_zero` | `badCutNo 0 = badCut` — the mutant family really is the original with one disjunct removed |
| faithfulness (walk) | `safeCutAuxG_badCut`, `safeCutG_badCut` | the parameterised walk **at `badCut` IS `safeCut`** |
| result | `disjuncts_predicate_independent` | each `Di` fires where `badCutNo i` does not |
| result | `disjuncts_walk_independent` | deleting any `Di` changes the cut `_safe_cut` **returns** |
| result | `d1_masked_by_d4_on_wellformed` | on well-formed traffic, deleting D1 changes nothing |

Without the bridges, `decide` would have proved the independence results just as happily over a
generalised lookalike that no line of `compressor.py` implements, and every number would have looked
identical. `d1_masked_by_d4_on_wellformed` **survived all 66 mutations** and is labelled
`[INFRASTRUCTURE]` in the source for that reason: it asserts an equality between two walks that any
mutation perturbs on both sides at once, so it explains rather than guards.
