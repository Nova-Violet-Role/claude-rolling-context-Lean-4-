/-
Copyright (c) 2026 Saimono. All rights reserved.
SPDX-FileCopyrightText: 2026 Saimono / Nova-Violet Role
SPDX-License-Identifier: AGPL-3.0-or-later OR EUPL-1.2
See NOTICE.md at the repository root for the full licence map.
Authors: Saimono
-/

/-! # Cavecrew router, formalized

A model of `C:\Users\Saimono\.vibe\caveman\hooks\cavecrew-router.ps1`.

Two layers, because the hook has two:

* `route` (`ps1:63-77`) — the intent chain. The PowerShell classifies the task
  text into booleans with regexes, then walks an `if/elseif` to pick a target.
* `dispatch` (`ps1:40-77`) — the whole hook, including the depth-cap early return
  at `:41-51` and the already-crew passthrough at `:54`, both of which run
  *before* the chain and are keyed on the requested agent, not on intent.

The first version of this file modelled only `route`. That left the hook's
headline guarantee unproved at exactly the point where it is weakest: the two
paths that skip the chain entirely.

Scope, stated honestly: this proves the branch structure is total, correctly
ordered, and depth-safe. It does **not** prove the regexes classify intent
correctly — that is an empirical question the test cases cover. If the chain in
the .ps1 changes, this file must change with it or the proof means nothing.
-/

namespace Cavecrew

/-- The agents the router may dispatch to. -/
inductive Target where
  | prover
  | pragmaticReviewer
  | reviewer
  | architect
  | builder
  | investigator
deriving DecidableEq, Repr

/-- Every `Target` is a cavecrew member.

An earlier version of this comment claimed that adding a non-crew constructor
would make `route_always_crew` stop compiling. That was **false**, and was
disproved by experiment: adding `| explorer` with `isCrew .explorer => false`,
leaving `route` untouched, still builds exit 0 — the theorem quantifies over
inputs to `route`, and `route` never returns the new constructor. Kept as a
reminder that a comment asserting falsifiability is worth nothing until someone
runs the mutation. -/
def isCrew : Target → Bool
  | .prover            => true
  | .pragmaticReviewer => true
  | .reviewer          => true
  | .architect         => true
  | .builder           => true
  | .investigator      => true

/-- The regex verdicts. `leanish` `:64`, `reviewish` `:65`, `deep` `:66`; the
`breadthy` and `edity` tests are inline `elseif` regexes at `:73` and `:75` and
exist as named variables only here. `insideSubagent` is the `parent_session_id`
check at `:40`. -/
structure Flags where
  leanish        : Bool
  reviewish      : Bool
  deep           : Bool
  breadthy       : Bool
  edity          : Bool
  insideSubagent : Bool
deriving Repr

/-- The `if/elseif` chain, in source order. -/
def route (f : Flags) : Target :=
  if f.leanish then
    .prover
  else if f.reviewish && f.deep && !f.insideSubagent then
    .pragmaticReviewer
  else if f.reviewish then
    .reviewer
  else if f.breadthy then
    .architect
  else if f.edity then
    .builder
  else
    .investigator

/-- **Totality — and it is vacuous.** Kept only as documentation of a trap.

It holds for *every* total `Flags → Target`, because `isCrew` is constantly
`true`. Verified by mutation, not assumed: replacing the whole body of `route`
with the constant `.investigator` still compiles. The theorem never looks at
`route` at all.

The real totality guarantee is `dispatch_never_foreign` at the bottom of this
file, which quantifies over the requested agent as well and can actually fail. -/
theorem route_always_crew (f : Flags) : isCrew (route f) = true := by
  obtain ⟨l, r, d, b, e, s⟩ := f
  cases l <;> cases r <;> cases d <;> cases b <;> cases e <;> cases s <;> rfl

/-- **Lean lane wins.** A Lean task never leaks to another member, whatever else
the text also matches. -/
theorem lean_takes_priority (f : Flags) (h : f.leanish = true) :
    route f = .prover := by
  simp [route, h]

/-- **Depth cap, chain only.** Inside a subagent the *intent chain* never selects
the one member that can spawn further subagents.

This is a strict corollary of `pragmatic_iff` below — it adds no content, and it
covers only one of the hook's two cap mechanisms. The path that actually fires in
the common case (the model names `cavecrew-pragmatic-reviewer` outright, handled
at `ps1:41-51`) is not visible to it. `dispatch_depth_cap` at the bottom of this
file covers both. Kept because it is the statement a reader looks for first. -/
theorem depth_cap (f : Flags) (h : f.insideSubagent = true) :
    route f ≠ .pragmaticReviewer := by
  obtain ⟨l, r, d, b, e, s⟩ := f
  simp at h
  subst h
  cases l <;> cases r <;> cases d <;> cases b <;> cases e <;> simp [route]

/-- **Review work stays with a reviewer.** A review task that is not Lean-shaped
goes to one of the two reviewers, never to a builder or architect. -/
theorem review_stays_review (f : Flags)
    (hl : f.leanish = false) (hr : f.reviewish = true) :
    route f = .reviewer ∨ route f = .pragmaticReviewer := by
  obtain ⟨l, r, d, b, e, s⟩ := f
  simp at hl hr
  subst hl; subst hr
  cases d <;> cases b <;> cases e <;> cases s <;> simp [route]

/-- **Exact characterisation of the delegating lane — within the chain.** Not a
restatement of the definition: it pins down in both directions which inputs reach
the delegating member *via `route`*.

Scope correction: an earlier version of this comment claimed it pinned down
"precisely which inputs reach" that member, full stop. False at the system level.
`ps1:54` passes an already-crew request straight through, so a caller naming
`cavecrew-pragmatic-reviewer` with every flag false reaches it without the chain
running at all. True of `route`, false of the hook. `dispatch_pragmatic_iff`
below states the system-level version.

This is the theorem that breaks under a bad edit. Reorder the chain so the
`breadthy` or `edity` branch precedes the pragmatic branch, drop `!insideSubagent`
from the guard, or let the Lean lane fall through, and the `↔` fails — whereas
`route_always_crew` would happily keep compiling. -/
theorem pragmatic_iff (f : Flags) :
    route f = .pragmaticReviewer ↔
      (f.leanish = false ∧ f.reviewish = true ∧ f.deep = true ∧
        f.insideSubagent = false) := by
  obtain ⟨l, r, d, b, e, s⟩ := f
  cases l <;> cases r <;> cases d <;> cases b <;> cases e <;> cases s <;>
    simp [route]

/-- **The tail lanes, pinned.** The five theorems above constrain only `.prover`,
`.reviewer` and `.pragmaticReviewer`. Not one of them mentions `.architect`,
`.builder` or `.investigator`, so the whole tail of the chain
(`cavecrew-router.ps1:73-77`) is currently unproved: it can be rewritten freely
and all five still compile. This closes that hole, characterising each remaining
lane in both directions once the two review lanes are excluded.

Three plausible bad edits it catches that nothing above does:
* **Reordering the tail** — put the `edity` branch before `breadthy` and the
  input `breadthy = true, edity = true` lands on `.builder`, so the first `↔`
  fails. `route_always_crew` and `pragmatic_iff` both survive that edit.
* **Changing the final `else`** — make the fallthrough any other member and the
  third `↔` fails on the all-false input. Totality cannot see this: every
  constructor is crew, so any fallthrough satisfies `route_always_crew`.
* **Leaking the depth cap into the tail** — no right-hand side mentions
  `insideSubagent`, so the tail is proved indifferent to it. Adding
  `&& !f.insideSubagent` to the `breadthy` or `edity` guard, as a
  copy-paste of the pragmatic guard, breaks the corresponding `↔`. That
  indifference is the intent: the cap exists because
  `cavecrew-pragmatic-reviewer` is the only member holding the `task` tool, and
  the architect and builder cannot spawn anything. -/
theorem tail_lanes_exact (f : Flags)
    (hl : f.leanish = false) (hr : f.reviewish = false) :
    (route f = .architect ↔ f.breadthy = true) ∧
      (route f = .builder ↔ (f.breadthy = false ∧ f.edity = true)) ∧
      (route f = .investigator ↔ (f.breadthy = false ∧ f.edity = false)) := by
  obtain ⟨l, r, d, b, e, s⟩ := f
  simp at hl hr
  subst hl; subst hr
  cases d <;> cases b <;> cases e <;> cases s <;> simp [route]

/-! ## Layer 2 — the whole hook

`route` is only reached when the two guards above it both fall through. Modelling
those guards is what makes the hook's headline guarantee ("every spawned subagent
is a cavecrew member") a theorem rather than a comment.
-/

/-- The requested agent, as `ps1:41` and `:54` discriminate it.

`ps1:54` tests `-like 'cavecrew-*'`, a **prefix match** — so a hallucinated
`cavecrew-bogus` satisfies it. `crewBogus` is a separate constructor precisely so
that hole is visible in the proofs instead of being assumed away. -/
inductive Requested where
  /-- Exactly `cavecrew-pragmatic-reviewer` — the only name `ps1:41` tests for. -/
  | pragmatic
  /-- A real crew member other than the pragmatic reviewer, or `explore`
  (`~/.vibe/agents/explore.toml` shadows the builtin onto the crew locator). -/
  | crewOther
  /-- Crew-*shaped* but not a real agent: `cavecrew-bogus`. Passes `:54`. -/
  | crewBogus
  /-- Anything else — `""`, `default`, `general-purpose`. Only these reach the chain. -/
  | foreign
deriving DecidableEq, Repr

/-- What the hook does with the call. -/
inductive Outcome where
  /-- `ps1:41-51` — rewritten to `cavecrew-reviewer` and returned early. -/
  | capped
  /-- `ps1:54` — allowed unchanged, whatever was requested. -/
  | passedThrough (r : Requested)
  /-- `ps1:63-77` — rewritten to the intent-chain target. -/
  | rewritten (t : Target)
deriving DecidableEq, Repr

/-- The hook, top to bottom: depth cap, then passthrough, then the chain. -/
def dispatch (r : Requested) (f : Flags) : Outcome :=
  if r = .pragmatic && f.insideSubagent then
    .capped
  else if r ≠ .foreign then
    .passedThrough r
  else
    .rewritten (route f)

/-- Can this outcome put a non-crew agent on the wire? -/
def escapesCrew : Outcome → Bool
  | .capped              => false
  | .passedThrough .foreign => true
  | .passedThrough _     => false
  | .rewritten _         => false

/-- **The real totality guarantee.** No input escapes the crew.

Unlike `route_always_crew` this can fail: it quantifies over the requested agent,
and `escapesCrew` is not constantly `false`. Delete the `r ≠ .foreign` guard from
`dispatch` and a foreign request passes straight through — the theorem breaks. -/
theorem dispatch_never_foreign (r : Requested) (f : Flags) :
    escapesCrew (dispatch r f) = false := by
  obtain ⟨l, rv, d, b, e, s⟩ := f
  cases r <;> cases s <;> simp [dispatch, escapesCrew]

/-- **Depth cap, both mechanisms.** Inside a subagent, no path reaches the
delegating member: not the early return, not the passthrough, not the chain.

This is the statement the cap actually needs, and the one the chain-only
`depth_cap` could not make. Together with "no other member holds `task`" — true
on disk: only `cavecrew-pragmatic-reviewer.toml` lists it in `enabled_tools` — it
bounds nesting at two levels. -/
theorem dispatch_depth_cap (r : Requested) (f : Flags) (h : f.insideSubagent = true) :
    dispatch r f ≠ .passedThrough .pragmatic ∧
      dispatch r f ≠ .rewritten .pragmaticReviewer := by
  obtain ⟨l, rv, d, b, e, s⟩ := f
  simp at h
  subst h
  cases r <;> cases l <;> cases rv <;> cases d <;> cases b <;> cases e <;>
    simp [dispatch, route]

/-- **System-level characterisation of the delegating lane.** The honest version
of `pragmatic_iff`: the delegating member is reached either by naming it from a
top-level call, or through the chain. Naming it is the path that the chain-only
version of this theorem could not see.

(Reflowed deliberately: this line used to begin with the word `theorem` at column
zero, so `grep -c '^theorem '` counted 25 declarations where there were 24. No
checker depended on that number, but the trap was live for the next person who
tried to count them from a shell.) -/
theorem dispatch_pragmatic_iff (r : Requested) (f : Flags) :
    (dispatch r f = .passedThrough .pragmatic ∨
        dispatch r f = .rewritten .pragmaticReviewer) ↔
      ((r = .pragmatic ∧ f.insideSubagent = false) ∨
        (r = .foreign ∧ f.leanish = false ∧ f.reviewish = true ∧
          f.deep = true ∧ f.insideSubagent = false)) := by
  obtain ⟨l, rv, d, b, e, s⟩ := f
  cases r <;> cases l <;> cases rv <;> cases d <;> cases b <;> cases e <;>
    cases s <;> simp [dispatch, route]

/-- **The prefix-match hole, stated as a theorem rather than a caveat.**

`ps1:54` checks the *shape* of the name, never that the agent exists. A
hallucinated `cavecrew-bogus` is passed through unrouted. The guarantee proved by
`dispatch_never_foreign` is therefore "no foreign agent", not "a real agent" —
existence is enforced downstream by vibe, which rejects the unknown name at
`core/tools/builtins/task.py:108-111` (`agent_manager.get_agent` raising
`ValueError` → `ToolError("Unknown agent: …")`) rather than silently misrouting.
An earlier version of this comment cited `:112-117`; that range is the *next*
guard, the `agent_type != SUBAGENT` check, and line 112 is blank. Measured
2026-07-27 against the installed `vibe` package.

If `ps1:54` is ever tightened to an explicit member list, this theorem is the one
that should stop compiling.

Stated without an `insideSubagent` hypothesis, which the linter showed to be
unused: the depth cap at `:41` tests one exact name, so a bogus crew-shaped name
slips past it whether or not the caller is a subagent. -/
theorem bogus_passes_through (f : Flags) :
    dispatch .crewBogus f = .passedThrough .crewBogus := by
  simp [dispatch]

/-! ## Layer 3 — the Claude Code cap is a *different* function

`~/.claude/tools/cavecrew/guard-agent-depth.ps1` is presented as the Claude-side
analogue of the vibe cap at `ps1:41-51`. It is not the same function, and it does
not carry the same conclusion. Two differences, both measured 2026-07-27:

* **The discriminator.** vibe reads `parent_session_id`. The Claude guard reads
  the *presence* of the top-level `agent_id`/`agent_type` fields
  (`guard-agent-depth.ps1:70-79`), because a subagent's `session_id` is identical
  to its parent's.
* **The side condition is false here.** `dispatch_depth_cap` bounds nesting only
  together with "no other member holds the spawning tool". That is true on disk
  for vibe: of `~/.vibe/agents/*.toml`, only `cavecrew-pragmatic-reviewer.toml`
  lists `task` in `enabled_tools`. The Claude-side counterpart is false — a
  `general-purpose` subagent emitted an `Agent` tool call, recorded in
  `~/.claude/tools/cavecrew/agent-spawns.jsonl` and in that subagent's own
  transcript. The guard stopped it only because of the *name* it asked for.

So the cap below is name-scoped, not depth-scoped. This section states exactly
that much and no more: it is deliberately *not* a `dispatch_depth_cap` analogue.
-/

/-- The requested `subagent_type`, as the guard discriminated it *before*
2026-07-27: strip one leading `namespace:` segment, then test for **equality**
with `cavecrew-pragmatic-reviewer`. Four shapes separate the three plausible bad
edits.

Citation corrected TWICE, and the second correction was also wrong. It said
`:90-91`, then `:94-97`; the normalisation is at **`:111-114`** (measured
2026-07-27). Every `:9x` citation in this layer was stale by ~17 lines. See
Layer 4, which models the current code; this layer is kept because Layer 4
subsumes it (`layer3_is_a_special_case`) and because the four shapes are still
the ones a reader reaches for.

Line numbers in this file are now checked mechanically rather than by eye:
`~/.claude/tools/check-guard-drift.py` anchors on file CONTENT, not on line
numbers, precisely because these citations have drifted at every revision. -/
inductive ClaudeName where
  /-- `cavecrew-pragmatic-reviewer`. -/
  | bare
  /-- `caveman:cavecrew-pragmatic-reviewer` — one namespace segment. -/
  | namespaced
  /-- `my-cavecrew-pragmatic-reviewer-v2` — *contains* the capped name. The
  earlier `-notlike "*$Capped*"` test blocked this; the equality test (now at
  `:114`) deliberately does not, so that a future agent whose name merely embeds
  this one is not silently capped. -/
  | containing
  /-- Anything else: `general-purpose`, `cavecrew-architect`, `lean4-prover`. -/
  | unrelated
deriving DecidableEq, Repr

/-- `$bare = ($requested -replace '^[^:]+:', '')` — the guard's normalisation as
it stood when this layer was written. **That line is gone.** The current file
trims, loops the strip, and trims again (`guard-agent-depth.ps1:111-113`), which
this single-shot map cannot express; `stripNs` in Layer 4 does. -/
def stripNamespace : ClaudeName → ClaudeName
  | .namespaced => .bare
  | n           => n

/-- The guard, whole: deny only when the call comes from inside a subagent *and*
the namespace-stripped name is exactly the capped one (`guard-agent-depth.ps1:96`
for the `inside` test, `:111-114` for the name test; this citation read `:86-91`,
then `:86` + `:94-97`, and both were wrong). Every other path falls through to
`Write-Allow`, and silence is allow under the PreToolUse contract. -/
def claudeDenies (inside : Bool) (n : ClaudeName) : Bool :=
  if inside then
    match stripNamespace n with
    | .bare => true
    | _     => false
  else
    false

/-- **The Claude-side cap, characterised exactly — including what it lets past.**

The `↔` fails under each of the three plausible bad edits, verified by mutation
rather than asserted:

* **Drop the namespace strip** (`| .namespaced => .bare` removed): a
  `caveman:`-qualified request stops being denied and the `←` direction fails.
* **Go back to substring matching** (`| .containing => true`): a name that merely
  embeds the capped one starts being denied and the `→` direction fails.
* **Drop the `inside` test**: a top-level spawn is denied and `→` fails.

Read the right-hand side for what is *absent* from it. Nothing constrains
`.unrelated`, so `claudeDenies true .unrelated = false` — from inside a subagent
the guard allows every other `subagent_type`, including `general-purpose`, which
was measured holding the `Agent` tool. That is the honest gap between this and
`dispatch_depth_cap`: one bounds nesting, this one blocks a name. -/
theorem claude_cap_exact (inside : Bool) (n : ClaudeName) :
    claudeDenies inside n = true ↔ (inside = true ∧ (n = .bare ∨ n = .namespaced)) := by
  cases inside <;> cases n <;> simp [claudeDenies, stripNamespace]

/-! ## Layer 4 — the normalisation the guard actually performs

Layer 3 above has **drifted from the file it models**, and this section exists to
say so precisely rather than to quietly patch the old definitions.

`stripNamespace` strips *one* `namespace:` segment. That was faithful to the
guard as written when Layer 3 was authored. The guard is now
(`guard-agent-depth.ps1:111-114`, measured 2026-07-27):

```powershell
$bare = ([string]$requested).Trim()
while ($bare -match '^[^:]*:') { $bare = $bare -replace '^[^:]*:', '' }
$bare = $bare.Trim()
if ($bare -ne $Capped) { Write-Allow }
```

Two consequences Layer 3 cannot express, so `claude_cap_exact` is now exactly
as true of the *pre-change* guard as of the current one — it can no longer tell
the fixed code from the code it was written to fix:

1. the strip is a **loop**, so `a:b:cavecrew-pragmatic-reviewer` is capped;
2. the name is **trimmed at both ends**, so a leading space or a trailing
   newline no longer slips past.

**This section was itself wrong for one revision, and the record is kept.** It
previously modelled `^[^:]+:` and carried two theorems asserting that
`"   :cavecrew-pragmatic-reviewer"` and `caveman::cavecrew-pragmatic-reviewer`
are **allowed** — with a docstring calling the first one "the hole the round-two
fix opened". Under `+`, an empty segment halts the loop, and the leading
`.Trim()` can manufacture one, so both really did escape. The guard was then
changed to `*`, which consumes an empty segment and strips through it; the two
theorems became the exact negation of the code while still compiling and still
being true *of the model*. A Lean file cannot notice that its subject moved.
Both are now `_denied`, proved, and re-measured.

**The hole that let this happen is now closed.** The reason the inversion survived
is that no checker read this file against the guard: `check-router-drift.py` reads
`cavecrew-router.ps1` and this file's `route`/`dispatch` sections only, and Layers
3/4 model a different program. `~/.claude/tools/check-guard-drift.py` now covers
it, in three phases — it hashes the guard's normalisation block and this layer's
definitions, asserts every theorem named by its corpus still exists here, and
feeds 15 adversarial shapes to the **real guard** as PreToolUse JSON, comparing
each verdict to the theorem that claims it. The `+` → `*` inversion would have
failed phase 3 on the day it was made. Layer 4 changes should be made together
with a run of that checker; a green `lake build` alone cannot see this class of
drift and never could.

This layer models the request as its colon-separated fields, which is the only
shape in which the loop's stopping condition is visible. Nothing above is
modified; `layer3_is_a_special_case` below shows Layer 3 is the restriction of
this one to single-strip inputs, so the older theorem stays meaningful.
-/

/-- One colon-delimited field of the requested `subagent_type`, classified by the
only two things the guard can do to it: test it for emptiness, and (for the
surviving field) compare it to the capped name after `.Trim()`. -/
inductive CField where
  /-- The empty string. Under `^[^:]*:` this does **not** stop the loop — `*`
  matches zero non-colon characters, so the colon alone is consumed and the strip
  advances. It is kept as a separate constructor precisely so the theorems below
  can state that, since under the previous `+` it *did* halt the loop. -/
  | empty
  /-- Non-empty but whitespace only, e.g. `" "`. Kept distinct from `empty`
  because `trimF` collapses it to `empty` — but **that collapse is not observable
  in any verdict.** An earlier version of this comment said the distinction is
  "what makes the leading `.Trim()` observable at all"; mutation testing refuted
  it (see `leading_trim_is_inert`). The two constructors are kept because they are
  genuinely different strings, `""` and `" "`, and a future regex could tell them
  apart again — not because any theorem below distinguishes them. -/
  | spaces
  /-- Exactly `cavecrew-pragmatic-reviewer`. -/
  | cappedBare
  /-- The capped name with surrounding whitespace, e.g.
  `"  cavecrew-pragmatic-reviewer\n"`. Equal to the capped name only after a
  `.Trim()`, which is what makes the two `.Trim()` calls load-bearing. -/
  | cappedPadded
  /-- Contains the capped name but is not it, e.g. `my-cavecrew-pragmatic-reviewer-v2`. -/
  | embedding
  /-- Any other non-empty field: `caveman`, `general-purpose`, `a`. -/
  | otherField
deriving DecidableEq, Repr

/-- `.Trim()` on a single field. Only two classes move: whitespace-only collapses
to empty, and a padded capped name becomes the bare one. -/
def trimF : CField → CField
  | .spaces       => .empty
  | .cappedPadded => .cappedBare
  | f             => f

/-- `.Trim()` reaches the last field of the whole string — this is
`guard-agent-depth.ps1:113`, the trim applied *after* the loop. This one is
load-bearing: removing it flips `padded_after_namespace_denied`. -/
def trimLast : List CField → List CField
  | []      => []
  | [f]     => [trimF f]
  | f :: fs => f :: trimLast fs

/-- The two `.Trim()` calls together (`:111` and `:113`). They touch the first and
last fields of the request and nothing in between; a one-field request is touched
once, which is sound because `trimF` is idempotent.

**Only one of the two is load-bearing.** `leading_trim_is_inert` below proves that
the first `.Trim()` cannot change any verdict, and the claim is not model-only: all
20 adversarial shapes measured through the real PowerShell with and without
`:111` gave identical results, 20/20. The reason is that `^[^:]*:` consumes a
leading segment whether or not it is whitespace, and whatever survives the loop is
trimmed again at `:113`.

That does **not** make `:111` dead weight worth deleting — it is what keeps the
guard correct if the regex is ever narrowed back to `^[^:]+:`. It makes it *defence
in depth*, which is a different claim from *load-bearing*, and the file previously
made the wrong one. -/
def trimEnds : List CField → List CField
  | []      => []
  | [f]     => [trimF f]
  | f :: fs => trimF f :: trimLast fs

/-- The `while` loop at `guard-agent-depth.ps1:112`. Drops the leading field while
there is a colon left to consume — unconditionally, because `^[^:]*:` matches an
empty leading segment. It terminates because every iteration removes one field.

The `if f = .empty then` guard that stood here modelled `^[^:]+:` and is gone; it
was the whole content of the two escape theorems below, which are now denials. -/
def stripNs : List CField → List CField
  | []             => []
  | [f]            => [f]
  | _ :: g :: rest => stripNs (g :: rest)

/-- The guard, whole (`:96` and `:111-114`): deny only from inside a subagent, and
only when normalisation lands exactly on the capped name. -/
def guardDenies (inside : Bool) (fs : List CField) : Bool :=
  if inside then
    (if stripNs (trimEnds fs) = [CField.cappedBare] then true else false)
  else
    false

/-- An independent reading of the same condition: *the last field is the capped
name*, full stop. Every earlier field is irrelevant under `*`, which is exactly
the change from the `+` era — the old closed form read "…and no earlier field is
empty", and that clause is what the two escape theorems exploited.
`strip_iff_capsTo` proves the two agree. -/
def capsTo : List CField → Bool
  | []              => false
  | [f]             => if f = .cappedBare then true else false
  | _ :: g :: rest  => capsTo (g :: rest)

/-- **The loop, characterised in closed form.** Stripping lands on the capped name
exactly when the final field is the capped name — no condition on the fields
before it. -/
theorem strip_iff_capsTo (fs : List CField) :
    stripNs fs = [CField.cappedBare] ↔ capsTo fs = true := by
  induction fs with
  | nil => simp [stripNs, capsTo]
  | cons f rest ih =>
    cases rest with
    | nil => cases f <;> simp [stripNs, capsTo]
    | cons g rest' => simp [stripNs, capsTo, ih]

/-- **`capsTo` is not an independent reading any more, and here is the honest
anchor.**

Under the old `^[^:]+:` the two definitions really were different arguments:
`stripNs` had a stopping condition and `capsTo`'s closed form had to say "…and no
earlier field is empty". Simplifying the guard collapsed both into the same
recursion — drop every field but the last — so `strip_iff_capsTo` above is now
close to `x = x`, and a reader is entitled to suspect it of being vacuous.

It is not *fully* vacuous: mutating either side alone breaks it (measured — a
`stripNs` that drops two fields per step, and a `capsTo` that reads the first field
instead of the last, both CAUGHT). But "mutating one side breaks it" is a weak
property, so this theorem supplies a genuinely foreign witness: the **stdlib's**
`List.getLast?`, which nobody here wrote and which no local edit can quietly
redefine. Chained with `strip_iff_capsTo`, the loop's behaviour is now pinned to a
definition outside this file. -/
theorem capsTo_iff_getLast (fs : List CField) :
    capsTo fs = true ↔ fs.getLast? = some CField.cappedBare := by
  induction fs with
  | nil => simp [capsTo]
  | cons f rest ih =>
    cases rest with
    | nil => cases f <;> simp [capsTo]
    | cons g rest' => simp [capsTo, ih]

/-- `trimLast` never empties a non-empty request. Needed below because the
one-field case of `trimEnds` really is different from the many-field case. -/
theorem trimLast_cons (g : CField) (rest : List CField) :
    ∃ x xs, trimLast (g :: rest) = x :: xs := by
  cases rest with
  | nil => exact ⟨trimF g, [], rfl⟩
  | cons h t => exact ⟨g, trimLast (h :: t), rfl⟩

/-- **The leading `.Trim()` cannot change a verdict.**

`guard-agent-depth.ps1:111` trims before the strip loop and `:113` trims after it.
Only `:113` is load-bearing. This says so mechanically: replacing `trimEnds` (both
trims) with `trimLast` (the trailing trim alone) leaves every verdict identical.

Why: `^[^:]*:` consumes a leading segment whether or not it is whitespace, so
whatever the leading trim would have tidied is either discarded by the loop or
tidied again at `:113`.

**Not a model artefact.** All 20 adversarial shapes — `" :name"`, `"   :name"`,
`"\t:name"`, `"caveman::name"`, `":::name"`, `" a : b : name "`, `"\n\ncaveman:name\n\n"`
and the rest — were run through the real PowerShell twice, once with `:111` and
once without: 20/20 identical. This theorem is the record of that measurement, and
it is what makes the two surviving mutants in `guard_cap_exact`'s table *equivalent
mutants* rather than gaps in the proof.

Deleting `:111` from the guard would therefore be safe today and unsafe the moment
anyone narrows the regex back to `^[^:]+:`. Keep it; just do not call it
load-bearing. -/
theorem leading_trim_is_inert (fs : List CField) :
    capsTo (trimEnds fs) = capsTo (trimLast fs) := by
  match fs with
  | [] => rfl
  | [f] => rfl
  | f :: g :: rest =>
    obtain ⟨x, xs, hx⟩ := trimLast_cons g rest
    simp [trimEnds, trimLast, hx, capsTo]

/-- **The Claude-side cap, characterised against the guard as it is now.**

This is the Layer 3 statement re-proved over a model that can see the loop and
the trims. Mutation-verified 2026-07-27, each mutant built on its own:

| mutation | result |
|---|---|
| `stripNs` shrunk to a single strip | CAUGHT |
| `stripNs` dropping two fields per step | CAUGHT |
| final comparison loosened to a substring test | CAUGHT |
| `capsTo` reading the first field instead of the last | CAUGHT |
| **trailing** `.Trim()` removed (`trimLast`) | CAUGHT |
| **leading** `.Trim()` removed (`trimEnds`) | **SURVIVED** |
| `trimF` no longer collapsing whitespace-only fields | **SURVIVED** |

An earlier version of this comment claimed it fails when you "drop either
`.Trim()`". The last two rows are why that was false. Both survivors are
*equivalent mutants* — they change no verdict in the real guard either, measured
20/20 — so the theorem is not weak here; the comment was wrong. See
`leading_trim_is_inert`. -/
theorem guard_cap_exact (inside : Bool) (fs : List CField) :
    guardDenies inside fs = true ↔ (inside = true ∧ capsTo (trimEnds fs) = true) := by
  cases inside <;> simp [guardDenies, strip_iff_capsTo]

/-- Layer 3's four shapes, as field lists. -/
def asFields : ClaudeName → List CField
  | .bare       => [.cappedBare]
  | .namespaced => [.otherField, .cappedBare]
  | .containing => [.embedding]
  | .unrelated  => [.otherField]

/-- **Layer 3 is the restriction of Layer 4 to its four shapes.** `claude_cap_exact`
is therefore still true — it is simply blind outside this image, which is where
every behaviour change of 2026-07-27 lives. -/
theorem layer3_is_a_special_case (inside : Bool) (n : ClaudeName) :
    guardDenies inside (asFields n) = claudeDenies inside n := by
  cases inside <;> cases n <;> rfl

/-- `layer3_is_a_special_case` compares **verdicts only**, so on its own it does
not pin the translation down: mutation-testing found that re-defining
`asFields .namespaced` to the bare single-field list leaves it compiling, because
both shapes deny. The two theorems here close that — they say the translation
preserves *shape*, not just outcome.

`.namespaced` must be an input the strip loop actually has to work on. -/
theorem namespaced_needs_the_loop :
    stripNs (trimEnds (asFields .namespaced)) ≠ asFields .namespaced := by decide

/-- …and `.bare` must be one it does not, or the two Layer 3 shapes are the same
shape wearing different names. -/
theorem bare_needs_no_loop :
    stripNs (trimEnds (asFields .bare)) = asFields .bare := by decide

/-! ### The measured shapes, one theorem each

Every fact below was run through the real normalisation first
(`scratchpad/r2_norm.ps1`, `r2_norm2.ps1`, 2026-07-27); the Lean records the
measurement rather than predicting it. -/

/-- `a:b:cavecrew-pragmatic-reviewer` → denied. Dies if `stripNs` goes back to a
single strip; this is the bypass the loop was written to close. -/
theorem two_segments_denied :
    guardDenies true [.otherField, .otherField, .cappedBare] = true := by decide

/-- `"  cavecrew-pragmatic-reviewer\n"` → denied. Dies if either `.Trim()` goes. -/
theorem padded_denied : guardDenies true [.cappedPadded] = true := by decide

/-- `"caveman:  cavecrew-pragmatic-reviewer  "` → denied. Dies specifically if the
*trailing* `.Trim()` at `:113` goes: the leading one cannot reach this field. -/
theorem padded_after_namespace_denied :
    guardDenies true [.otherField, .cappedPadded] = true := by decide

/-- `my-cavecrew-pragmatic-reviewer-v2` → allowed. Dies if the equality test at
`:114` is ever loosened back to a substring match. -/
theorem embedding_still_allowed : guardDenies true [.embedding] = false := by decide

/-- A top-level spawn is never denied, whatever the name (`:96`). -/
theorem top_level_never_denied (fs : List CField) : guardDenies false fs = false := by
  simp [guardDenies]

/-- **The hole the round-two fix opened, now closed.**
`"   :cavecrew-pragmatic-reviewer"` → *denied*. `.Trim()` at `:111` still empties
the first field, but `^[^:]*:` consumes an empty segment, so the loop advances
instead of halting. Under the previous `^[^:]+:` this input was **allowed**, and
this theorem asserted `= false`. Measured on both regexes, 2026-07-27. -/
theorem blank_first_segment_denied :
    guardDenies true [.spaces, .cappedBare] = true := by decide

/-- `caveman::cavecrew-pragmatic-reviewer` → denied. An empty interior segment no
longer halts the loop; it is consumed like any other. Also asserted `= false`
under `+`. -/
theorem empty_segment_denied :
    guardDenies true [.otherField, .empty, .cappedBare] = true := by decide

/-- `"a: :cavecrew-pragmatic-reviewer"` → denied. A whitespace-only interior
segment is *not* empty, so the loop strips straight through it.

This docstring used to say the contrast with `empty_segment_escapes` is "the whole
reason `spaces` and `empty` are separate constructors". Two things were wrong with
that: the theorem was renamed to `empty_segment_denied` when its verdict inverted,
so the reference dangled; and there is no contrast left to point at — under
`^[^:]*:` both shapes are denied, and `trimF`'s collapse of `spaces` into `empty`
changes no verdict at all (`leading_trim_is_inert`). -/
theorem whitespace_segment_does_not_escape :
    guardDenies true [.otherField, .spaces, .cappedBare] = true := by decide

end Cavecrew
