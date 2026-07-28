/-
Copyright (c) 2026 Saimono. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saimono
-/

/-! # Rolling-context compressor, formalized

A model of the *selection policy* in
`C:\Users\Saimono\.vibe\nestor-plugins\rolling-context\proxy\compressor.py`
and of the merge in `proxy/vibe-rc-server.py`.

## What this file can and cannot prove

**Provable, and proved here:** the shape of the cut, the arithmetic of the keep
ratio, termination of the backward walk, the invariants of the pin mechanism,
monotone shrink, and convergence under iteration.

**Not provable, not attempted:** whether the summary the model writes preserves
the meaning of what it replaced. That is empirical. It enters this file as
`Policy.summaryChars : Conv → Nat` — an *arbitrary* function about which nothing
is assumed. Every theorem below is universally quantified over it, so no theorem
can be read as a claim about summary quality. There is deliberately no
`summary_preserves_meaning`.

## Why it exists

Three defects shipped, each of which alone made compression a silent no-op:

* **D3** `_find_keep_index` budgeted the keep ratio over a total that was mostly
  the system prompt, so the backward walk always ran to index 0 and `compress()`
  always returned `None`.
* **D4** `_do_background_compression` hashed from index 0, storing a chain that
  began with the system message and, on cycle 2, with the proxy's own synthetic
  messages — permanently unmatchable.
* **D1** an `UnboundLocalError` killed the handler thread at the trigger.

D3 and D4 are propositions about a pure function over a message list.
`findKeepIndex_ge_systemHead` and `cut_in_range` below are those propositions.

## Load-bearing or decorative

Every theorem carries one of two markers:

* **[LOAD-BEARING]** — a mutation of the modelled code breaks the proof. The
  mutation that breaks it is named in the doc comment, and was *run*.
* **[DECORATIVE]** — survives mutations of the code it appears to describe.
  Kept only when it documents a trap. Saying so is the point: an unmarked
  vacuous theorem is worse than no theorem.

## Zero imports, deliberately

Like `Router.lean`, this file imports nothing — it builds in ~1s against core
Lean, which keeps the edit/verify loop tight. The cost was three core-only
workarounds, all measured rather than guessed: `Nat.strongRecOn` exists in core
(`by_contra` and `conv_lhs` do not, they are Mathlib), so strong induction is
spelled with the core recursor and contradiction is spelled as `cases` on the
`Bool`. Nothing here needs Mathlib.

The model is kept honest from the outside by `check-compressor-drift.py`, which
regenerates the CORPUS section at the bottom of this file from
`compressor-cases.json`, runs the same cases through the real Python, and fails
on any disagreement.
-/

namespace Compressor

/-! ## 0. Core-only strong induction

`Nat.strongRecOn` is available, but stating the eliminator explicitly makes the
two `safeCut` proofs read as ordinary induction and removes any doubt about
which recursor is in play. -/

private theorem strongRec {motive : Nat → Prop}
    (ind : ∀ n, (∀ m, m < n → motive m) → motive n) (n : Nat) : motive n := by
  have key : ∀ b m, m ≤ b → motive m := by
    intro b
    induction b with
    | zero => intro m hm; exact ind m (fun k hk => absurd (by omega : k < 0) (by omega))
    | succ b ih => intro m hm; exact ind m (fun k hk => ih k (by omega))
  exact key n n (Nat.le_refl n)

/-! ## 1. The message model -/

/-- Roles as vibe sends them. Note `tool` is a *role*, not a content block: in
Mistral shape a tool result is its own message. -/
inductive Role where
  | system
  | user
  | assistant
  | tool
deriving DecidableEq, Repr

/-- A message, abstracted to exactly the fields the selection policy reads.

`chars` is `_count_chars([msg])`: content plus, for an assistant turn, the
`tool_calls` name and arguments. `hasToolCalls` is `_has_tool_use`. `synthetic`
is "this message carries an authenticated `SUMMARY_MARKER`", i.e. the proxy wrote
it, not vibe.

`pinChars` is how much of `chars` was actually AUTHENTICATED as pinned, and so
how much survives being hoisted over the summary boundary. The two channels in
`compressor.py` set it differently, and the difference is the whole point:

* a marker pin is a delimited span `[PIN:<mac>]…[/PIN]` whose MAC covers only the
  enclosed text, so `pinChars` is the size of the spans, which may be far less
  than `chars` — `_pin_extract` rebuilds the message from the spans alone;
* the structural `pinned: true` sidecar has no span to scope to, so `pinChars`
  is `chars`.

Before review 5 there was no such field because the MAC covered the whole message
body, making retention and authentication trivially equal. Delimiting the span to
fix inline usage broke that equality, and keeping the two in step is what stops
one small authenticated span from dragging an arbitrarily large payload across
the boundary. -/
structure Msg where
  role : Role
  chars : Nat
  hasToolCalls : Bool := false
  pinned : Bool := false
  synthetic : Bool := false
  pinChars : Nat := 0
deriving DecidableEq, Repr

abbrev Conv := List Msg

/-- `_count_chars`. -/
def countChars (c : Conv) : Nat := (c.map (·.chars)).sum

@[simp] theorem countChars_nil : countChars [] = 0 := rfl

@[simp] theorem countChars_cons (m : Msg) (c : Conv) :
    countChars (m :: c) = m.chars + countChars c := rfl

@[simp] theorem countChars_append (a b : Conv) :
    countChars (a ++ b) = countChars a + countChars b := by
  induction a with
  | nil => simp
  | cons m ms ih => simp only [List.cons_append, countChars_cons, ih]; omega

/-! ## 2. The system prefix -/

/-- `_system_head` / `server._system_prefix_len`: the length of the leading run
of `system` messages. Index 0 is the system prompt in vibe traffic; upstream's
Anthropic shape carried it out-of-band, which is the whole reason this exists. -/
def systemHead : Conv → Nat
  | [] => 0
  | m :: ms => if m.role = .system then systemHead ms + 1 else 0

theorem systemHead_le_length (c : Conv) : systemHead c ≤ c.length := by
  induction c with
  | nil => simp [systemHead]
  | cons m ms ih => simp only [systemHead, List.length_cons]; split <;> omega

/-- Everything in the system prefix really is a system message. Used to show the
prefix contributes nothing to the pinned set. -/
theorem mem_take_systemHead (c : Conv) :
    ∀ m ∈ c.take (systemHead c), m.role = Role.system := by
  induction c with
  | nil => simp
  | cons a as ih =>
    simp only [systemHead]
    split
    · next ha =>
      intro m hm
      rw [List.take_succ_cons] at hm
      rcases List.mem_cons.mp hm with h | h
      · exact h ▸ ha
      · exact ih m h
    · simp

/-! ## 3. Selection: `_find_keep_index`

The Python walks the conversation backwards accumulating characters until the
budget is exceeded, then moves the cut forward to the next `user` message. Two
pins bound the result: the system head below, and `max_idx = len - 4` above.

Each intermediate quantity is a named top-level definition rather than a `let`.
That is not style: a `let` in a definition body elaborates to an opaque `have`,
and `split` cannot see an `if` through it, so the bounds below would be
unprovable as stated. It also gives `check-compressor-drift.py` a separate
handle on each quantity. -/

/-- The backward walk, over the reversed body: how many messages from the end fit
inside `target`. Mirrors `if accumulated + msg_chars > target_chars: break`. -/
def fitCount : Conv → Nat → Nat → Nat
  | [], _, _ => 0
  | m :: ms, acc, target =>
      if acc + m.chars > target then 0 else fitCount ms (acc + m.chars) target + 1

theorem fitCount_le_length (c : Conv) (acc target : Nat) :
    fitCount c acc target ≤ c.length := by
  induction c generalizing acc with
  | nil => simp [fitCount]
  | cons m ms ih =>
    simp only [fitCount, List.length_cons]
    split
    · omega
    · have := ih (acc + m.chars); omega

/-- The forward rescan `for j in range(i+1, len)`: index of the first `user`
message at or after the start of the given suffix. -/
def firstUserIdx : Conv → Nat → Option Nat
  | [], _ => none
  | m :: ms, i => if m.role = .user then some i else firstUserIdx ms (i + 1)

theorem firstUserIdx_ge (c : Conv) (i j : Nat) (h : firstUserIdx c i = some j) :
    i ≤ j := by
  induction c generalizing i with
  | nil => simp [firstUserIdx] at h
  | cons m ms ih =>
    simp only [firstUserIdx] at h
    split at h
    · injection h with h; omega
    · have := ih (i + 1) h; omega

/-- `max_idx = len(messages) - 4`. -/
def maxIdx (c : Conv) : Nat := c.length - 4

/-- The compressible body: everything after the system prefix.

**This is D3.** Upstream took the budget over the whole array. Here index 0 is
the system prompt and vibe's is large — measured 31,107 of 31,357 chars, 99.2% —
so the budget was a fraction of the one thing that can never be compressed. -/
def body (c : Conv) : Conv := c.drop (systemHead c)

/-- `target_chars = int(total_chars * keep_ratio)`.

**The keep ratio is integer arithmetic here and in the Python.** Upstream passed
a float and computed `int(total_chars * keep_ratio)`; the port now passes
numerator and denominator and computes `total * num // den`, which is this
expression exactly. Floats were not modelled, they were removed: an IEEE754
product is not `Nat` division, and the difference would be an unprovable gap
rather than an untidy one. -/
def keepTarget (c : Conv) (keepNum keepDen : Nat) : Nat :=
  countChars (body c) * keepNum / keepDen

/-- How many trailing messages fit in the budget. -/
def fitFromEnd (c : Conv) (keepNum keepDen : Nat) : Nat :=
  fitCount (body c).reverse 0 (keepTarget c keepNum keepDen)

/-- The tail of `_find_keep_index`: move the cut forward to the next `user`
message, then clamp into `[systemHead, maxIdx]`. -/
def findKeepCore (c : Conv) (i1 : Nat) : Nat :=
  match firstUserIdx (c.drop i1) i1 with
  | some j => max (systemHead c) (min j (maxIdx c))
  | none => max (systemHead c) (min i1 (maxIdx c))

/-- `_find_keep_index`. -/
def findKeepIndex (c : Conv) (keepNum keepDen : Nat) : Nat :=
  if c.length - systemHead c ≤ 4 then
    systemHead c
  else if fitFromEnd c keepNum keepDen = (body c).length then
    systemHead c
  else
    findKeepCore c (c.length - fitFromEnd c keepNum keepDen)

theorem findKeepCore_ge (c : Conv) (i1 : Nat) : systemHead c ≤ findKeepCore c i1 := by
  unfold findKeepCore; split <;> exact Nat.le_max_left _ _

theorem findKeepCore_le (c : Conv) (i1 : Nat) :
    findKeepCore c i1 ≤ max (systemHead c) (maxIdx c) := by
  unfold findKeepCore
  split <;> omega

/-- **[LOAD-BEARING] D3, half one.** The cut never lands inside the system
prefix, whatever the ratio and whatever the content.

Mutation that breaks it: drop the `max(head, ...)` from either return in
`_find_keep_index` — the audit had to add exactly this floor, in two places. -/
theorem findKeepIndex_ge_systemHead (c : Conv) (n d : Nat) :
    systemHead c ≤ findKeepIndex c n d := by
  unfold findKeepIndex
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · exact findKeepCore_ge _ _

/-- **[LOAD-BEARING] the `max_idx = len - 4` pin.** The cut never crosses the
last four messages unless the whole body is shorter than that, in which case the
function returns the system head and `compress`'s guard refuses.

Mutation that breaks it: remove `min(j, max_idx)`. -/
theorem findKeepIndex_le (c : Conv) (n d : Nat) :
    findKeepIndex c n d ≤ max (systemHead c) (maxIdx c) := by
  unfold findKeepIndex
  split
  · exact Nat.le_max_left _ _
  · split
    · exact Nat.le_max_left _ _
    · exact findKeepCore_le _ _

/-- **[DECORATIVE], deliberately.** `_find_keep_index`'s inner rescan tests
`messages[j].get("role") == "user" and not self._has_tool_result(messages[j])`.
In Mistral shape `_has_tool_result` is `role == "tool"`, so the second conjunct
is implied by the first and can never fire. This theorem is the proof that the
conjunct is dead code — it is not a property of the compressor, it is a note
about a line ported from Anthropic shape, where it *did* have content (there a
`user` message could carry `tool_result` blocks).

The code keeps the conjunct: removing it is a behaviour-preserving edit that the
drift checker would then have to be taught about, for no gain. -/
theorem user_is_never_tool_result (m : Msg) (h : m.role = Role.user) :
    m.role ≠ Role.tool := by
  rw [h]; intro hc; cases hc

/-! ## 4. `_safe_cut` — the backward walk to a legal boundary -/

/-- `messages[cut-1]` must not carry `tool_calls` (its results would be
summarized away, splitting a tool-call group) and must not be a `system` message
(the appended compact prompt, a user turn, would land after it).

The `messages[cut-1]` access has no bounds guard in the Python and needs none:
`cut > floor` is evaluated first and short-circuits, so `cut >= 1` whenever it is
reached. -/
def prefixEndsBad (c : Conv) (cut : Nat) : Bool :=
  match c[cut - 1]? with
  | some m => m.hasToolCalls || m.role == Role.system
  | none => false

/-- `messages[cut]` must not be a `system` message (the ack, an assistant turn,
would land before it) and must not be a `tool` message (its call would have been
summarized away — Mistral rejects that outright, a hard 400 that wedges the
session rather than degrading it).

The `cut < len(messages)` guard in the Python is the `none` case here. -/
def tailStartsBad (c : Conv) (cut : Nat) : Bool :=
  match c[cut]? with
  | some m => m.role == Role.system || m.role == Role.tool
  | none => false

/-- The loop condition of `_safe_cut`, as one predicate. -/
def badCut (c : Conv) (cut : Nat) : Bool := prefixEndsBad c cut || tailStartsBad c cut

/-- `_safe_cut`.

**The clamp is new.** Upstream, and the port until now, returned `cut` unchanged
when it started below `floor`, so the postcondition `result >= floor` was false
for `_safe_cut(msgs, 0, 1) -> 0` — the audit's open nit. It was unreachable only
because `compress` guards it afterwards. `max cut floor` makes the postcondition
unconditional; `clamp_preserves_guard` below shows the guard's verdict is
unchanged, so the fix cannot regress anything.

The loop is expressed with an explicit iteration budget rather than by
well-founded recursion, and the budget is `cut` itself. That is not a
concession: it is a *stronger* termination statement (the loop needs at most
`cut` iterations, `safeCutAux_enough`), and it is the only version the kernel can
evaluate — a well-founded `safeCut` is opaque to `rfl`, which would have made
every corpus case in §8 unprovable and the whole binding to Python decorative.
Measured, not assumed: with the well-founded definition,
`example : cutOf pP cP = 5 := by rfl` fails with "not definitionally equal". -/
def safeCutAux (c : Conv) (floor : Nat) : Nat → Nat → Nat
  | 0, cut => max cut floor
  | fuel + 1, cut =>
      if floor < cut ∧ badCut c cut = true then
        safeCutAux c floor fuel (cut - 1)
      else
        max cut floor

def safeCut (c : Conv) (cut floor : Nat) : Nat := safeCutAux c floor cut cut

/-- **[LOAD-BEARING] the loop recurrence.** `safeCut` satisfies exactly the
`while` loop in `_safe_cut`: one step down when the boundary is illegal, stop
otherwise. Every proof below is written against this equation, so they are
proofs about the Python loop and not about the budget bookkeeping.

Mutation that breaks it: change the loop body to `cut -= 2`. -/
theorem safeCut_eq (c : Conv) (cut floor : Nat) :
    safeCut c cut floor
      = if floor < cut ∧ badCut c cut = true then safeCut c (cut - 1) floor
        else max cut floor := by
  cases cut with
  | zero => simp [safeCut, safeCutAux]
  | succ n => rfl

/-- **[LOAD-BEARING] termination, with the bound.** `cut` iterations always
suffice: any larger budget computes the same answer. This is the quantitative
form of "the `while cut > floor` loop halts" — it halts, and it halts within
`cut` steps.

Mutation that breaks it: change the loop body to `cut += 1`; no budget then
suffices and the two sides disagree. -/
theorem safeCutAux_enough (c : Conv) (floor : Nat) :
    ∀ fuel cut, cut ≤ fuel → safeCutAux c floor fuel cut = safeCut c cut floor := by
  intro fuel
  induction fuel with
  | zero => intro cut h; have : cut = 0 := by omega
            subst this; rfl
  | succ k ih =>
    intro cut h
    cases cut with
    | zero => simp [safeCut, safeCutAux]
    | succ m =>
      show (if floor < m + 1 ∧ badCut c (m + 1) = true then safeCutAux c floor k m
            else max (m + 1) floor) = _
      rw [safeCut_eq]
      split
      · exact ih m (by omega)
      · rfl

/-- **[LOAD-BEARING] termination, with its postcondition.** Lean accepted
`safeCut` by `termination_by cut`: `cut` strictly decreases and is bounded below,
which is the proof that the `while cut > floor` loop halts. This lemma is the
postcondition that makes halting useful.

Mutation that breaks it: change the body to `cut + 1`, or drop the `cut > floor`
conjunct — Lean then rejects the definition outright, before any theorem. -/
theorem safeCut_ge_floor (c : Conv) (floor : Nat) :
    ∀ cut, floor ≤ safeCut c cut floor := by
  refine strongRec (motive := fun n => floor ≤ safeCut c n floor) ?_
  intro n ih
  rw [safeCut_eq]
  split
  · next h => exact ih (n - 1) (by omega)
  · omega

/-- **[LOAD-BEARING]** the walk only ever moves the cut *down*, so it can never
manufacture a cut past `max_idx`. -/
theorem safeCut_le (c : Conv) (floor : Nat) :
    ∀ cut, safeCut c cut floor ≤ max cut floor := by
  refine strongRec (motive := fun n => safeCut c n floor ≤ max n floor) ?_
  intro n ih
  rw [safeCut_eq]
  split
  · next h =>
    have := ih (n - 1) (by omega)
    omega
  · omega

/-- **[LOAD-BEARING] no orphan tool, no split tool-call group, no system
adjacency.** If the walk stopped above the floor, the boundary it stopped on is
legal.

Mutation that breaks it: delete any of the four disjuncts in `_safe_cut`'s
condition. The audit fuzzed 4,000 cases for this property; the theorem covers
all of them and every case the fuzzer did not generate. -/
theorem safeCut_clean (c : Conv) (floor : Nat) :
    ∀ cut, floor < safeCut c cut floor → badCut c (safeCut c cut floor) = false := by
  refine strongRec
    (motive := fun n => floor < safeCut c n floor → badCut c (safeCut c n floor) = false) ?_
  intro n ih h
  rw [safeCut_eq] at h ⊢
  split at h
  · next hc =>
    rw [if_pos hc]
    exact ih (n - 1) (by omega) h
  · next hc =>
    rw [if_neg hc]
    have hmax : max n floor = n := by omega
    rw [hmax] at h ⊢
    cases hb : badCut c n with
    | false => rfl
    | true => exact absurd ⟨h, hb⟩ hc

/-- Corollary in the form the server needs: the retained tail never starts with a
`tool` message whose call was summarized away. -/
theorem no_orphan_tool (c : Conv) (cut floor : Nat)
    (h : floor < safeCut c cut floor) (m : Msg)
    (hm : c[safeCut c cut floor]? = some m) : m.role ≠ Role.tool := by
  have hb := safeCut_clean c floor cut h
  unfold badCut at hb
  have ht : tailStartsBad c (safeCut c cut floor) = false := by
    cases hx : tailStartsBad c (safeCut c cut floor) with
    | false => rfl
    | true => rw [hx, Bool.or_true] at hb; exact absurd hb (by simp)
  unfold tailStartsBad at ht
  rw [hm] at ht
  intro hr
  simp [hr] at ht

/-- Corollary: the summarized prefix never ends on a message carrying
`tool_calls`, so no tool-call group is split by the cut. -/
theorem no_split_tool_group (c : Conv) (cut floor : Nat)
    (h : floor < safeCut c cut floor) (m : Msg)
    (hm : c[safeCut c cut floor - 1]? = some m) : m.hasToolCalls = false := by
  have hb := safeCut_clean c floor cut h
  unfold badCut at hb
  have hp : prefixEndsBad c (safeCut c cut floor) = false := by
    cases hx : prefixEndsBad c (safeCut c cut floor) with
    | false => rfl
    | true => rw [hx, Bool.true_or] at hb; exact absurd hb (by simp)
  unfold prefixEndsBad at hp
  rw [hm] at hp
  cases hy : m.hasToolCalls with
  | false => rfl
  | true => simp [hy] at hp

/-! ## 5. Hard memory — structural pins

The weakness the pin mechanism removes: today everything outside the system
prefix is erodable, and what survives a round depends on the summarizer prompt,
i.e. on a model choosing well. A pinned message must survive *by construction*.

The mechanism is the one the server already uses for the system prompt: the
retained content is carried **over** the summary boundary rather than protected
by an index. `messages[:sys_head] + prefix + tail` becomes
`messages[:sys_head] + [summary, ack] + pinned + tail`.

Eligibility is structural and narrow on purpose:

* `system` — already in the head, and hoisting one would break the API's
  "system follows user, precedes assistant" rule;
* `tool`, and any assistant carrying `tool_calls` — hoisting either would orphan
  the other half of a tool-call group, the hard 400 above.

An ineligible pin is **not silently dropped**: `compressor.py` reports it
(`_pin_rejections`), because a pin that quietly does nothing is the same failure
class as D3 — healthy logs, no effect. -/

/-- A message may be pinned only if hoisting it can never break the wire format,
and only if vibe wrote it. `synthetic` excludes the proxy's own summary: a
summary quoting a `[PIN]` marker would otherwise pin itself, be retained
verbatim *and* regenerated every round — an unbounded stack of summaries. -/
def pinEligible (m : Msg) : Bool :=
  m.role == Role.user && !m.hasToolCalls && !m.synthetic

/-- The pin predicate the policy actually uses. -/
def effectivePinned (m : Msg) : Bool := m.pinned && pinEligible m

/-- **[LOAD-BEARING]** no pinned message can orphan a tool call, in either
direction. This is what buys `no_orphan_tool` for the hoisted block, and it is
why eligibility is a structural test rather than a repair pass.

Mutation that breaks it: allow `role == "tool"` in `_pin_eligible`. -/
theorem pinned_never_tool (m : Msg) (h : effectivePinned m = true) :
    m.role ≠ Role.tool ∧ m.hasToolCalls = false := by
  unfold effectivePinned pinEligible at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨-, ⟨hr, ht⟩, -⟩ := h
  refine ⟨?_, ht⟩
  rw [hr]; intro hc; cases hc

/-- **[LOAD-BEARING] defect D-O.** Only a `user` turn is ever pinnable, so the
model cannot make its own output permanently unforgettable and unshrinkable.

This is the STRUCTURAL half of the D-O fix and the half that matters. The MAC in
`_mint_tag` also commits to the role, but that only stops an attacker who cannot
read `state/pin-secret` — and that file is mode 0644 under the user profile,
which every agent with a shell can read (MEASURED, review 5). This check survives
such an attacker; the MAC does not.

MEASURED against the shipped code before the fix: a valid pin copied verbatim
into an assistant turn authenticated, and a 24-turn conversation went from 82.4%
compressed to 13.5%, retaining 110,928 chars of model output.

Mutation that breaks it: restore `|| m.role == Role.assistant`. -/
theorem pinned_is_user (m : Msg) (h : effectivePinned m = true) :
    m.role = Role.user := by
  unfold effectivePinned pinEligible at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2.1.1

/-- **[LOAD-BEARING]** the proxy's own summary and ack are never pinnable, so a
summary that happens to contain the pin marker cannot pin itself.

Mutation that breaks it: drop `!m.synthetic` here / drop the `SUMMARY_MARKER not
in content` test in `_is_pinned`. -/
theorem synthetic_never_pinned (m : Msg) (h : m.synthetic = true) :
    effectivePinned m = false := by
  unfold effectivePinned pinEligible; simp [h]

/-- `_pin_extract`: what a pinned message becomes when it is carried across the
summary boundary — only the part of it that was authenticated.

`min` rather than plain `pinChars` so the bound holds unconditionally, with no
well-formedness hypothesis to forget at a call site. -/
def pinExtract (m : Msg) : Msg := { m with chars := min m.pinChars m.chars }

/-- **[LOAD-BEARING] retention never exceeds authentication.** A pinned message
gives back at most the characters its MAC actually covered.

This is the property that stopped the review-5 fix from trading one defect for a
worse one. Delimiting the pin to `[PIN:<mac>]…[/PIN]` made inline pins work, but
a span-scoped MAC with whole-message retention would let a 3-byte authenticated
span drag an arbitrarily large payload over the boundary verbatim — mint over
nothing, keep everything. The old whole-message MAC had no such gap, and losing
it silently would have been the real regression.

Mutation that breaks it: `_pinned_in` returning `m` instead of
`self._pin_extract(m)`. -/
theorem pinExtract_le_pinChars (m : Msg) : (pinExtract m).chars ≤ m.pinChars :=
  Nat.min_le_left _ _

/-- **[LOAD-BEARING]** and it never grows a message either. -/
theorem pinExtract_le_chars (m : Msg) : (pinExtract m).chars ≤ m.chars :=
  Nat.min_le_right _ _

/-- **[LOAD-BEARING]** extraction is idempotent, which is what makes retention
stable across rounds: the extracted message is re-scanned on the next request and
must extract to itself, or a pin would shrink a little every round until it was
gone. The Python keeps the `[PIN:…]…[/PIN]` delimiters in the extracted content
for exactly this reason, and `check-compressor-drift.py` executes it. -/
theorem pinExtract_idem (m : Msg) : pinExtract (pinExtract m) = pinExtract m := by
  unfold pinExtract; simp

/-- Extraction touches only `chars`, so it cannot change whether something is
pinned. Without this, hoisting a pin could un-pin it. -/
@[simp] theorem effectivePinned_pinExtract (m : Msg) :
    effectivePinned (pinExtract m) = effectivePinned m := rfl

/-- The pinned messages inside the half-open span `[lo, hi)`, each reduced to the
span its MAC covered. -/
def pinnedIn (c : Conv) (lo hi : Nat) : Conv :=
  (((c.drop lo).take (hi - lo)).filter effectivePinned).map pinExtract

/-! ## 6. The compression step -/

/-- Everything the policy needs that is not the conversation.

`summaryChars` is **the model**. It is an arbitrary `Conv → Nat`, which is the
formal statement of "Lean cannot prove anything about model behaviour": no
theorem below may assume it is small, faithful, or even sensible — only that
whatever it returns is some number of characters. -/
structure Policy where
  keepNum : Nat
  keepDen : Nat
  summaryChars : Conv → Nat
  ackChars : Nat

/-- `_has_summary`: the message at index `systemHead` carries the marker. -/
def hasSummary (c : Conv) : Bool :=
  match c[systemHead c]? with
  | some m => m.synthetic
  | none => false

/-- `compress`'s `start_idx = sys_head + (2 if has_existing_summary else 0)`. -/
def startIdx (c : Conv) : Nat :=
  systemHead c + (if hasSummary c then 2 else 0)

/-- The cut `compress` actually uses: the ratio walk, then the legality walk,
floored at `start_idx`. -/
def cutOf (p : Policy) (c : Conv) : Nat :=
  safeCut c (findKeepIndex c p.keepNum p.keepDen) (startIdx c)

def summaryMsg (p : Policy) (c : Conv) : Msg :=
  { role := Role.user, chars := p.summaryChars c, synthetic := true }

def ackMsg (p : Policy) : Msg :=
  { role := Role.assistant, chars := p.ackChars, synthetic := true }

/-- The replacement conversation.

Note the pin scan starts at `systemHead`, not `start_idx`. Scanning from
`start_idx` would leave the previous `[summary, ack]` pair outside the scan and
make `pinned_preserved` conditional on those two never being pinned. Starting at
the system head makes it unconditional, and costs nothing: the pair is synthetic
and so never eligible anyway (`synthetic_never_pinned`). -/
def rebuild (p : Policy) (c : Conv) (cut : Nat) : Conv :=
  c.take (systemHead c) ++ [summaryMsg p c, ackMsg p]
    ++ pinnedIn c (systemHead c) cut ++ c.drop cut

/-- Characters in the span the step would replace. -/
def spanChars (c : Conv) (cut : Nat) : Nat :=
  countChars ((c.drop (systemHead c)).take (cut - systemHead c))

/-- Characters the pins hold inside that span — the part of it that cannot be
given back. -/
def pinChars (c : Conv) (cut : Nat) : Nat :=
  countChars (pinnedIn c (systemHead c) cut)

/-- Why a step declined. `compress` used to return a bare `None` for the first of
these and had no concept of the others; a bare `None` is what made D3 invisible
for weeks. -/
inductive Refusal where
  /-- `keep_from_idx <= start_idx`: there is no compressible span. -/
  | nothingToCompress
  /-- The pins inside the span already account for all of it. **No summary of any
  size can shrink this conversation**, so the step must not spend an API call to
  discover that. Decidable before the request. -/
  | pinBudget
  /-- Pins plus the summary the model actually returned do not fit under the
  span. Only decidable after the request. -/
  | summaryTooLarge
deriving DecidableEq, Repr

/-- One compression step. The three guards are in the order the Python evaluates
them, and the middle one is the point of the whole exercise: it is checked
*before* `summaryChars` is consulted. -/
def stepE (p : Policy) (c : Conv) : Except Refusal Conv :=
  if cutOf p c ≤ startIdx c then
    .error .nothingToCompress
  else if spanChars c (cutOf p c) ≤ pinChars c (cutOf p c) then
    .error .pinBudget
  else if spanChars c (cutOf p c)
      ≤ pinChars c (cutOf p c) + p.summaryChars c + p.ackChars then
    .error .summaryTooLarge
  else
    .ok (rebuild p c (cutOf p c))

/-! ### Range facts about the cut -/

theorem cutOf_ge_startIdx (p : Policy) (c : Conv) : startIdx c ≤ cutOf p c :=
  safeCut_ge_floor _ _ _

theorem systemHead_le_startIdx (c : Conv) : systemHead c ≤ startIdx c := by
  unfold startIdx; omega

/-- Everything a successful step tells us, extracted once. -/
theorem stepE_ok (p : Policy) (c c' : Conv) (h : stepE p c = .ok c') :
    c' = rebuild p c (cutOf p c)
      ∧ startIdx c < cutOf p c
      ∧ pinChars c (cutOf p c) + p.summaryChars c + p.ackChars
          < spanChars c (cutOf p c) := by
  unfold stepE at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · exact ⟨by simpa using h.symm, by omega, by omega⟩

/-- **[LOAD-BEARING] D3, half two, and D4.** Whenever a step is taken, the cut
sits strictly inside `(start_idx, len - 4]`. The lower bound stops the summarizer
eating the system prompt; the upper bound is the `len - 4` pin.

`_do_background_compression` derived its hash chain from an index it recomputed
by subtraction, and got this range wrong (D4). The port now takes the cut from
the compressor's own reported result instead of re-deriving it.

Mutation that breaks it: replace `max(head, ...)` with `min(...)` in
`_find_keep_index`, or set `start_idx = 0`. -/
theorem cut_in_range (p : Policy) (c c' : Conv) (h : stepE p c = .ok c') :
    startIdx c < cutOf p c ∧ cutOf p c ≤ c.length - 4 := by
  have hok := stepE_ok p c c' h
  refine ⟨hok.2.1, ?_⟩
  have hle := safeCut_le c (startIdx c) (findKeepIndex c p.keepNum p.keepDen)
  have hfk := findKeepIndex_le c p.keepNum p.keepDen
  have hsh := systemHead_le_startIdx c
  have h1 := hok.2.1
  unfold cutOf at h1 ⊢
  unfold maxIdx at hfk
  omega

theorem cut_le_length (p : Policy) (c c' : Conv) (h : stepE p c = .ok c') :
    cutOf p c ≤ c.length := by
  have := (cut_in_range p c c' h).2; omega

/-! ### The decomposition every character argument rests on -/

theorem split_conv (c : Conv) (lo hi : Nat) (h1 : lo ≤ hi) :
    c.take lo ++ (c.drop lo).take (hi - lo) ++ c.drop hi = c := by
  have hd : (c.drop lo).drop (hi - lo) = c.drop hi := by
    rw [List.drop_drop]; congr 1; omega
  calc c.take lo ++ (c.drop lo).take (hi - lo) ++ c.drop hi
      = c.take lo ++ ((c.drop lo).take (hi - lo) ++ (c.drop lo).drop (hi - lo)) := by
        rw [hd, List.append_assoc]
    _ = c.take lo ++ c.drop lo := by rw [List.take_append_drop]
    _ = c := List.take_append_drop _ _

theorem countChars_split (c : Conv) (cut : Nat) (h : systemHead c ≤ cut) :
    countChars c
      = countChars (c.take (systemHead c)) + spanChars c cut
        + countChars (c.drop cut) := by
  have hs := split_conv c (systemHead c) cut h
  calc countChars c
      = countChars (c.take (systemHead c)
          ++ (c.drop (systemHead c)).take (cut - systemHead c) ++ c.drop cut) := by
        rw [hs]
    _ = _ := by unfold spanChars; simp only [countChars_append]

/-! ### Monotone shrink -/

theorem countChars_rebuild (p : Policy) (c : Conv) (cut : Nat) :
    countChars (rebuild p c cut)
      = countChars (c.take (systemHead c)) + p.summaryChars c + p.ackChars
        + pinChars c cut + countChars (c.drop cut) := by
  unfold rebuild pinChars
  simp only [countChars_append, countChars_cons, countChars_nil, summaryMsg, ackMsg]
  omega

/-- **[LOAD-BEARING] monotone_shrink, stated exactly.** A step strictly reduces
the character count, and the amount is `span - (pins + summary + ack)`, nothing
else.

This is the theorem behind the measured decline `merged=77,288 >=
current=76,115`: that was not a missed opportunity, it was the correct verdict of
this inequality. The fix is to *report* it, not to compress anyway.

Mutation that breaks it: drop the `merged_chars < msg_chars` guard in the server,
or the `summaryTooLarge` branch in `stepE`. -/
theorem monotone_shrink (p : Policy) (c c' : Conv) (h : stepE p c = .ok c') :
    countChars c' < countChars c := by
  have hok := stepE_ok p c c' h
  have hsh := systemHead_le_startIdx c
  have hle : systemHead c ≤ cutOf p c := by have := hok.2.1; omega
  rw [hok.1, countChars_rebuild, countChars_split c (cutOf p c) hle]
  have := hok.2.2
  omega

/-- **[LOAD-BEARING] the pin-saturation condition, decidable before the API
call.** If the pins inside the span already account for the whole span, then *no
summary of any length* makes the conversation shorter. The step must therefore
refuse without contacting the model — and say which condition fired.

This is the precise condition the brief asked to be proven or bounded. It is not
a heuristic: `summaryChars` is arbitrary, so this quantifies over every possible
summarizer, including one that returns the empty string.

Mutation that breaks it: reorder `stepE` to test `summaryTooLarge` first, or
delete the `pinBudget` branch. -/
theorem pin_saturation_refuses (p : Policy) (c : Conv)
    (hgt : startIdx c < cutOf p c)
    (h : spanChars c (cutOf p c) ≤ pinChars c (cutOf p c)) :
    stepE p c = .error .pinBudget := by
  unfold stepE
  rw [if_neg (by omega), if_pos h]

/-- The other half: saturation really does make shrinking impossible, for every
summarizer. Stated over `rebuild` directly so it cannot be read as a fact about
`stepE`'s guards. -/
theorem pin_saturation_cannot_shrink (p : Policy) (c : Conv) (cut : Nat)
    (hle : systemHead c ≤ cut)
    (h : spanChars c cut ≤ pinChars c cut) :
    countChars c ≤ countChars (rebuild p c cut) := by
  rw [countChars_rebuild, countChars_split c cut hle]
  omega

/-! ### Hard memory under iteration -/

theorem filter_eq_nil_of_all_system (l : Conv) (h : ∀ m ∈ l, m.role = Role.system) :
    l.filter effectivePinned = [] := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have ha : effectivePinned a = false := by
      have h1 : a.role = Role.system := h a (by simp)
      unfold effectivePinned pinEligible
      simp [h1]
    rw [List.filter_cons, ha]
    simpa using ih (fun m hm => h m (by simp [hm]))

theorem filter_take_systemHead (c : Conv) :
    (c.take (systemHead c)).filter effectivePinned = [] :=
  filter_eq_nil_of_all_system _ (mem_take_systemHead c)

theorem filter_idem (l : Conv) :
    (l.filter effectivePinned).filter effectivePinned = l.filter effectivePinned := by
  induction l with
  | nil => rfl
  | cons a as ih => cases ha : effectivePinned a <;> simp [ha, ih]

theorem filter_map_pinExtract (l : Conv) :
    (l.map pinExtract).filter effectivePinned
      = (l.filter effectivePinned).map pinExtract := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    cases ha : effectivePinned a <;>
      simp [effectivePinned_pinExtract, ha, ih]

theorem map_pinExtract_idem (l : Conv) :
    (l.map pinExtract).map pinExtract = l.map pinExtract := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [pinExtract_idem, ih]

theorem filter_pinnedIn (c : Conv) (lo hi : Nat) :
    (pinnedIn c lo hi).filter effectivePinned = pinnedIn c lo hi := by
  unfold pinnedIn
  rw [filter_map_pinExtract, filter_idem]

/-- **[LOAD-BEARING]** the list-level form of `pinExtract_le_chars`: hoisting a
block of pins over the boundary never carries more characters than those messages
held. This is what makes `pinChars` a genuine lower bound on what compression
cannot give back, rather than a number that could exceed the span it is measured
against. -/
theorem countChars_map_pinExtract_le (l : Conv) :
    countChars (l.map pinExtract) ≤ countChars l := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, countChars_cons]
    exact Nat.add_le_add (pinExtract_le_chars a) ih

/-- **[LOAD-BEARING, and the headline] `pinned_never_cut`, one step.** The pinned
messages of the output are *exactly* the pinned messages of the input, in order —
not merely "at least".

Equality is the stronger statement and the right one: `⊇` would also be satisfied
by a step that duplicated pins every round, which is a real failure mode (an
unbounded stack of retained copies), not a safe one.

STATED UNDER `map pinExtract` since review 5, and the qualifier is the honest
part of the statement rather than a weakening of it. What the proxy authenticates
is the pinned SPAN, not the message that carries it, so what it promises to
preserve is the span. `pinExtract` is idempotent, so applying it to both sides
compares like with like: every pin that went in comes out, in order, exactly
once, with exactly its authenticated content. Comparing the raw messages instead
would assert that the surrounding prose survives too — which is false by design,
and asserting it would be the overclaim this file exists to avoid.

Mutation that breaks it: delete `++ pinnedIn c (systemHead c) cut` from
`rebuild`, i.e. `pinned_kept` from `compress()`'s return. -/
theorem pinned_preserved (p : Policy) (c : Conv) (cut : Nat)
    (hle : systemHead c ≤ cut) :
    ((rebuild p c cut).filter effectivePinned).map pinExtract
      = (c.filter effectivePinned).map pinExtract := by
  have hsa : ([summaryMsg p c, ackMsg p] : Conv).filter effectivePinned = [] := by
    unfold effectivePinned pinEligible summaryMsg ackMsg; simp
  have hsplit := split_conv c (systemHead c) cut hle
  unfold rebuild
  rw [List.filter_append, List.filter_append, List.filter_append,
    filter_take_systemHead, hsa, filter_pinnedIn]
  have hR : ((c.take (systemHead c)
              ++ (c.drop (systemHead c)).take (cut - systemHead c)
              ++ c.drop cut).filter effectivePinned).map pinExtract
      = ((((c.drop (systemHead c)).take (cut - systemHead c)).filter
            effectivePinned).map pinExtract)
        ++ ((c.drop cut).filter effectivePinned).map pinExtract := by
    rw [List.filter_append, List.filter_append, filter_take_systemHead]
    simp
  rw [hsplit] at hR
  rw [hR]
  simp [pinnedIn, pinExtract_idem]

/-- **[INFRASTRUCTURE]** A pure `List` fact, with no compressor content: no
mutation of the model can falsify it. Stated separately because core Lean's
`List.take_left` is phrased with `l₁.length` and the goal below is phrased with
`systemHead c`. -/
theorem take_append_of_length_eq (A B : Conv) (n : Nat) (h : A.length = n) :
    (A ++ B).take n = A := by
  subst h; simp

/-- **[LOAD-BEARING] `system_prefix_preserved`.** The leading run of `system`
messages comes out of a step byte-identical. The summarizer can never be handed
the system prompt and can never replace it.

This is not the same statement as `findKeepIndex_ge_systemHead`: that one says
the *cut* respects the prefix, this one says the *output* does. Both are needed,
because the output is assembled by `rebuild`, not by the cut alone — the server
re-attaches `messages[:sys_head]` and a mistake there would not touch the cut.

Mutation that breaks it: drop `c.take (systemHead c) ++` from `rebuild`, i.e.
drop `messages[:sys_head] +` from the server's merge. -/
theorem system_prefix_preserved (p : Policy) (c : Conv) (cut : Nat) :
    (rebuild p c cut).take (systemHead c) = c.take (systemHead c) := by
  have hlen : (c.take (systemHead c)).length = systemHead c := by
    rw [List.length_take]
    have := systemHead_le_length c
    omega
  unfold rebuild
  rw [List.append_assoc, List.append_assoc]
  exact take_append_of_length_eq _ _ _ hlen

/-- Each step strictly decreases `countChars`; this is what makes the iteration
below well-founded. -/
theorem step_decreases (p : Policy) (c c' : Conv) (h : stepE p c = .ok c') :
    countChars c' < countChars c := monotone_shrink p c c' h

/-- Compression run to a fixpoint, with an explicit round budget.

The budget is `countChars c`, and `runAux_enough` shows any larger budget gives
the same answer — so this is convergence *with a stated bound*: at most
`countChars c` rounds, which is a stronger claim than "it terminates". In
practice the bound is never approached; one round per request is the norm and
`run_fixpoint` says the second round declines.

Same reason as `safeCut`: a well-founded definition here is opaque to the kernel,
and every `run` case in the §8 corpus would be unprovable. -/
def runAux : Nat → Policy → Conv → Conv
  | 0, _, c => c
  | fuel + 1, p, c =>
      match stepE p c with
      | .error _ => c
      | .ok c' => runAux fuel p c'

def run (p : Policy) (c : Conv) : Conv := runAux (countChars c) p c

/-- A refused step is a fixpoint: `run` stops exactly where `stepE` declines. -/
theorem run_error (p : Policy) (c : Conv) (r : Refusal) (h : stepE p c = .error r) :
    run p c = c := by
  unfold run
  cases hn : countChars c with
  | zero => rfl
  | succ k => simp only [runAux, h]

/-- Any surplus budget is inert — the loop has already stopped. -/
theorem runAux_enough (p : Policy) :
    ∀ f g c, countChars c ≤ f → f ≤ g → runAux f p c = runAux g p c := by
  intro f
  induction f with
  | zero =>
    intro g c hc _
    cases hs : stepE p c with
    | error r =>
      cases g with
      | zero => rfl
      | succ m => simp only [runAux, hs]
    | ok c' =>
      have := step_decreases p c c' hs
      omega
  | succ n ih =>
    intro g c hc hg
    cases g with
    | zero => omega
    | succ m =>
      simp only [runAux]
      cases hs : stepE p c with
      | error r => rfl
      | ok c' =>
        have hd := step_decreases p c c' hs
        exact ih m c' (by omega) (by omega)

/-- An accepted step is one round of the loop. -/
theorem run_ok (p : Policy) (c c' : Conv) (h : stepE p c = .ok c') :
    run p c = run p c' := by
  have hd := step_decreases p c c' h
  unfold run
  cases hn : countChars c with
  | zero => omega
  | succ k =>
    simp only [runAux, h]
    exact (runAux_enough p (countChars c') k c' (Nat.le_refl _) (by omega)).symm

/-- **[LOAD-BEARING] converges.** Iterating compression reaches a state where the
policy declines. With `run_shrinks`, that is convergence: strictly decreasing in
`countChars`, and it stops.

Mutation that breaks it: make `stepE` return `.ok` unconditionally — Lean then
rejects `run` for failing to terminate, before this theorem is reached. -/
theorem run_fixpoint (p : Policy) (c : Conv) :
    ∃ r, stepE p (run p c) = .error r := by
  refine strongRec
    (motive := fun n => ∀ c, countChars c ≤ n → ∃ r, stepE p (run p c) = .error r)
    ?_ (countChars c) c (Nat.le_refl _)
  intro n ih c hc
  cases h : stepE p c with
  | error r => rw [run_error p c r h]; exact ⟨r, h⟩
  | ok c' =>
    rw [run_ok p c c' h]
    have hd := step_decreases p c c' h
    exact ih (countChars c') (by omega) c' (Nat.le_refl _)

/-- **[LOAD-BEARING]** the fixpoint is never bigger than what you started with. -/
theorem run_shrinks (p : Policy) (c : Conv) :
    countChars (run p c) ≤ countChars c := by
  refine strongRec
    (motive := fun n => ∀ c, countChars c ≤ n → countChars (run p c) ≤ countChars c)
    ?_ (countChars c) c (Nat.le_refl _)
  intro n ih c hc
  cases h : stepE p c with
  | error r => rw [run_error p c r h]; exact Nat.le_refl _
  | ok c' =>
    rw [run_ok p c c' h]
    have hd := step_decreases p c c' h
    have := ih (countChars c') (by omega) c' (Nat.le_refl _)
    omega

/-- **[LOAD-BEARING, and the prize] `pinned_never_cut` under iteration.** For any
conversation, any policy — hence any summarizer, any keep ratio, any trigger —
and any number of compression rounds, the pinned messages that come out are
exactly the pinned messages that went in.

No threshold, no summarizer prompt and no number of rounds can erode them,
because retention is not a request made of the model: pinned messages are carried
across the summary boundary by `rebuild`, the same way the system prefix already
is, and are never inside the replaced span.

Mutation that breaks it: any listed on `pinned_preserved`, plus "retain pins only
on the first round". -/
theorem pinned_never_cut (p : Policy) (c : Conv) :
    ((run p c).filter effectivePinned).map pinExtract
      = (c.filter effectivePinned).map pinExtract := by
  refine strongRec
    (motive := fun n => ∀ c, countChars c ≤ n →
      ((run p c).filter effectivePinned).map pinExtract
        = (c.filter effectivePinned).map pinExtract)
    ?_ (countChars c) c (Nat.le_refl _)
  intro n ih c hc
  cases h : stepE p c with
  | error r => rw [run_error p c r h]
  | ok c' =>
    rw [run_ok p c c' h]
    have hd := step_decreases p c c' h
    have hrec := ih (countChars c') (by omega) c' (Nat.le_refl _)
    have hok := stepE_ok p c c' h
    have hsh := systemHead_le_startIdx c
    have hle : systemHead c ≤ cutOf p c := by have := hok.2.1; omega
    rw [hrec, hok.1]
    exact pinned_preserved p c (cutOf p c) hle

/-! ### Retention floor -/

/-- **[LOAD-BEARING] retention_floor — "not too aggressive", stated checkably.**
Whenever a step is taken it keeps, verbatim and unsummarized, **at least the last
four messages** of the conversation. That is the `max_idx = len - 4` pin, and it
is the reason the compressor sometimes correctly declines: in Mistral shape a
single tool result is its own message, so "the last four" can be most of a
payload.

Mutation that breaks it: change `max_idx = len(messages) - 4` to `len(messages)`,
or drop `min(j, max_idx)`. -/
theorem retention_floor (p : Policy) (c c' : Conv) (h : stepE p c = .ok c') :
    4 ≤ (c.drop (cutOf p c)).length := by
  have hr := cut_in_range p c c' h
  have hsh := systemHead_le_startIdx c
  simp only [List.length_drop]
  omega

/-- The same floor at the level of the emitted conversation: the output contains
the system prefix, the summary pair, every pin, and the last four messages. -/
theorem retention_floor_length (p : Policy) (c c' : Conv) (h : stepE p c = .ok c') :
    systemHead c + 2 + (pinnedIn c (systemHead c) (cutOf p c)).length + 4 ≤ c'.length := by
  have hok := stepE_ok p c c' h
  have h4 := retention_floor p c c' h
  have hsh := systemHead_le_length c
  rw [hok.1]
  unfold rebuild
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_take,
    List.length_drop] at h4 ⊢
  omega

/-! ### The guard, and the clamp that does not change it -/

/-- `_safe_cut` exactly as it was BEFORE the audit fix: no clamp. Kept so that
"adding the clamp changed nothing" can be stated about the two real functions
rather than about two arbitrary naturals. -/
def safeCutRawAux (c : Conv) (floor : Nat) : Nat → Nat → Nat
  | 0, cut => cut
  | fuel + 1, cut =>
      if floor < cut ∧ badCut c cut = true then
        safeCutRawAux c floor fuel (cut - 1)
      else
        cut

def safeCutRaw (c : Conv) (cut floor : Nat) : Nat := safeCutRawAux c floor cut cut

/-- **[LOAD-BEARING]** The clamped walk is the unclamped walk, clamped. This is
the bridge `clamp_preserves_guard` stands on, so the clamp mutations (M05, M22,
M29) break it too. -/
theorem safeCutAux_eq_max (c : Conv) (floor : Nat) : ∀ fuel cut,
    safeCutAux c floor fuel cut = max (safeCutRawAux c floor fuel cut) floor := by
  intro fuel
  induction fuel with
  | zero => intro cut; rfl
  | succ n ih =>
    intro cut
    simp only [safeCutAux, safeCutRawAux]
    split
    · exact ih (cut - 1)
    · rfl

/-- **[LOAD-BEARING] `safe_cut_clamps`, and the proof that adding the clamp was
behaviour-preserving.** The audit's open nit was `_safe_cut(msgs, 0, 1) -> 0`,
below its own floor. The clamp fixes the postcondition; this shows `compress`'s
verdict is bit-identical either way, so the fix cannot regress anything.

Both sides read "the step refuses": below the floor the unclamped walk returns
something `<= start_idx`, the clamped walk returns exactly `start_idx`, and the
guard is `<=`.

AN EARLIER VERSION OF THIS THEOREM WAS AN OVERCLAIM, and mutation testing caught
it. It read `raw ≤ floor ↔ max raw floor ≤ floor` — a fact about two arbitrary
naturals that never mentioned `safeCut`, so no mutation of the compressor could
falsify it, while its doc comment asserted that changing the guard to `<` would.
Mutation M11 did exactly that and the theorem survived. It is now stated about
the two real functions.

Mutation that breaks it: clamp to `max cut (floor + 1)` (M29). Then below the
floor the clamped walk returns `floor + 1`, the guard `≤ start_idx` flips from
true to false, and a conversation that used to be refused is silently
compressed at a cut inside the system prefix. -/
theorem clamp_preserves_guard (c : Conv) (cut floor : Nat) :
    safeCutRaw c cut floor ≤ floor ↔ safeCut c cut floor ≤ floor := by
  unfold safeCut safeCutRaw
  rw [safeCutAux_eq_max]
  omega

/-! ## 7. Threshold ordering

Not a property of the compressor — a property of the *configuration* it runs
inside, enforced today by nothing but a comment in two files. Violating it is
silent: everything still runs, `/health` still reports `ok`, and the first long
conversation gets replaced wholesale by vibe's own compaction. Same signature as
D3.

The numbers are the live ones, measured 2026-07-27: `/health` on
127.0.0.1:5590 reports `trigger_tokens=220000, target_tokens=120000`, and
`~/.vibe/config.toml` sets `auto_compact_threshold = 245000` on the
`mistral-medium-3.5-rc` model. `check-compressor-drift.py` re-reads all three
from their real sources — including the live `/health`, so an env-var override
cannot slip past — so these literals cannot drift unnoticed. -/

def TRIGGER_TOKENS : Nat := 220000
def TARGET_TOKENS : Nat := 120000
def AUTO_COMPACT_THRESHOLD : Nat := 245000

/-- **[LOAD-BEARING via the drift checker] the ordering constraint.** Rolling
compression must fire before vibe's native compaction, or native wins the race
and replaces the whole conversation with a lossy summary — the exact behaviour
this proxy exists to prevent.

Vibe's shipped default is 200000 (`core/agents/models.py:177`), which is *below*
this trigger; leaving it there inverts the ordering. That inversion was
introduced by hand during this work and caught by this constraint.

Mutation that breaks it: set either literal to vibe's default. -/
theorem rolling_precedes_native : TRIGGER_TOKENS < AUTO_COMPACT_THRESHOLD := by
  unfold TRIGGER_TOKENS AUTO_COMPACT_THRESHOLD; omega

/-- The compressor must aim *below* its own trigger, or a freshly compressed
conversation is immediately over the line again and every request compresses. -/
theorem target_below_trigger : TARGET_TOKENS < TRIGGER_TOKENS := by
  unfold TARGET_TOKENS TRIGGER_TOKENS; omega

/-- The headroom is stated, not implied, so raising the trigger without raising
the threshold is a visible edit. -/
theorem headroom_is_25k : AUTO_COMPACT_THRESHOLD - TRIGGER_TOKENS = 25000 := by
  unfold AUTO_COMPACT_THRESHOLD TRIGGER_TOKENS; omega

/-! ## 8. Corpus — the binding to the shipped Python

Everything above is a theorem about a *model*. The model is only worth something
if the Python does the same thing, and a Lean file cannot check that: it stays
green whatever `compressor.py` does. That is the F1/F5 lesson from `Router.lean`,
where two theorems compiled for a week while asserting the exact negation of the
shipped regex.

So the cases below are evaluated on **both** sides. `check-compressor-drift.py`
regenerates this whole section from `compressor-cases.json`, diffs it against
what is here, then runs the same cases through the real `RollingCompressor` and
compares every number. Divergence in either direction is a non-zero exit.

These also serve a second purpose: **anti-vacuity witnesses**. A theorem like
`pinned_never_cut` is satisfied trivially by a conversation with no pins
(`[] = []`). `case_pin_mid` below has a real pin, inside the replaced span, that
a pinless policy would have destroyed — so the general theorem is not being read
against an empty set. -/

def mkP (num den summ ack : Nat) : Policy :=
  { keepNum := num, keepDen := den, summaryChars := fun _ => summ, ackChars := ack }

def sys (n : Nat) : Msg := { role := Role.system, chars := n }
def usr (n : Nat) : Msg := { role := Role.user, chars := n }

/-- A user message that IS one pin span end to end: `[PIN:<mac>]…[/PIN]` and
nothing else, so the authenticated span is the whole message and `pinChars = n`.
This is the shape `POST /pin` returns pasted on its own. -/
def usrPin (n : Nat) : Msg :=
  { role := Role.user, chars := n, pinned := true, pinChars := n }

/-- A user message of `n` chars carrying a pin span of only `k` — the inline case
that defect D-P made impossible and that review 5 fixed. `k < n` is the whole
point: it is the witness that retention is scoped to what was authenticated
rather than to the message, so `pinExtract_le_pinChars` is not being read against
a corpus where the two coincide. -/
def usrPinSpan (n k : Nat) : Msg :=
  { role := Role.user, chars := n, pinned := true, pinChars := k }

def ast (n : Nat) : Msg := { role := Role.assistant, chars := n }

/-- An assistant turn carrying a pin that authenticated. Ineligible since D-O:
the model must not be able to pin its own output. -/
def astPin (n : Nat) : Msg :=
  { role := Role.assistant, chars := n, pinned := true, pinChars := n }

def astCall (n : Nat) : Msg := { role := Role.assistant, chars := n, hasToolCalls := true }
def astCallPin (n : Nat) : Msg :=
  { role := Role.assistant, chars := n, hasToolCalls := true, pinned := true,
    pinChars := n }
def toolRes (n : Nat) : Msg := { role := Role.tool, chars := n }
def toolResPin (n : Nat) : Msg :=
  { role := Role.tool, chars := n, pinned := true, pinChars := n }
def sumMsg (n : Nat) : Msg := { role := Role.user, chars := n, synthetic := true }
def sumMsgPin (n : Nat) : Msg :=
  { role := Role.user, chars := n, pinned := true, synthetic := true, pinChars := n }

/-- The refusal code the Python must log and expose on `/health`. Comparing
strings rather than constructors is deliberate: the string is the thing that
actually crosses the boundary into the log and the status endpoint, so this is
the surface the drift checker can read on both sides. -/
def outcomeCode (p : Policy) (c : Conv) : String :=
  match stepE p c with
  | .error .nothingToCompress => "nothingToCompress"
  | .error .pinBudget => "pinBudget"
  | .error .summaryTooLarge => "summaryTooLarge"
  | .ok _ => "ok"

/-- Observables of a single step. A refusal leaves the conversation untouched,
which is what `compress() -> None` means at the call site. -/
def stepLen (p : Policy) (c : Conv) : Nat :=
  match stepE p c with | .ok c' => c'.length | .error _ => c.length

def stepChars (p : Policy) (c : Conv) : Nat :=
  match stepE p c with | .ok c' => countChars c' | .error _ => countChars c

def stepPins (p : Policy) (c : Conv) : Nat :=
  match stepE p c with
  | .ok c' => (c'.filter effectivePinned).length
  | .error _ => (c.filter effectivePinned).length

-- CORPUS-BEGIN (generated by check-compressor-drift.py; do not hand-edit)
def case_plain : Conv :=
  [sys 3000, usr 1000, ast 2000, usr 1500, ast 2500, usr 1200, ast 1800, usr 900, ast 1100]
def pol_plain : Policy := mkP 1 2 812 160
theorem case_plain_spec :
    systemHead case_plain = 1
      ∧ startIdx case_plain = 1
      ∧ findKeepIndex case_plain 1 2 = 5
      ∧ cutOf pol_plain case_plain = 5
      ∧ spanChars case_plain 5 = 7000
      ∧ pinChars case_plain 5 = 0
      ∧ countChars case_plain = 15000
      ∧ (case_plain.filter effectivePinned).length = 0
      ∧ outcomeCode pol_plain case_plain = "ok"
      ∧ stepLen pol_plain case_plain = 7
      ∧ stepChars pol_plain case_plain = 8972
      ∧ stepPins pol_plain case_plain = 0
      ∧ (run pol_plain case_plain).length = 7
      ∧ countChars (run pol_plain case_plain) = 8972
      ∧ ((run pol_plain case_plain).filter effectivePinned).length = 0
    := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def case_d3_sysheavy : Conv :=
  [sys 31107, usr 500, ast 600, usr 400, ast 300, usr 450, ast 250]
def pol_d3_sysheavy : Policy := mkP 1 2 372 160
theorem case_d3_sysheavy_spec :
    systemHead case_d3_sysheavy = 1
      ∧ startIdx case_d3_sysheavy = 1
      ∧ findKeepIndex case_d3_sysheavy 1 2 = 3
      ∧ cutOf pol_d3_sysheavy case_d3_sysheavy = 3
      ∧ spanChars case_d3_sysheavy 3 = 1100
      ∧ pinChars case_d3_sysheavy 3 = 0
      ∧ countChars case_d3_sysheavy = 33607
      ∧ (case_d3_sysheavy.filter effectivePinned).length = 0
      ∧ outcomeCode pol_d3_sysheavy case_d3_sysheavy = "ok"
      ∧ stepLen pol_d3_sysheavy case_d3_sysheavy = 7
      ∧ stepChars pol_d3_sysheavy case_d3_sysheavy = 33039
      ∧ stepPins pol_d3_sysheavy case_d3_sysheavy = 0
      ∧ (run pol_d3_sysheavy case_d3_sysheavy).length = 7
      ∧ countChars (run pol_d3_sysheavy case_d3_sysheavy) = 33039
      ∧ ((run pol_d3_sysheavy case_d3_sysheavy).filter effectivePinned).length = 0
    := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def case_tool_walk : Conv :=
  [sys 1000, usr 2000, astCall 3000, toolRes 4000, toolRes 3500, toolRes 3000, toolRes 2500, 
   usr 1000, ast 900]
def pol_tool_walk : Policy := mkP 1 2 372 160
theorem case_tool_walk_spec :
    systemHead case_tool_walk = 1
      ∧ startIdx case_tool_walk = 1
      ∧ findKeepIndex case_tool_walk 1 2 = 5
      ∧ cutOf pol_tool_walk case_tool_walk = 2
      ∧ spanChars case_tool_walk 2 = 2000
      ∧ pinChars case_tool_walk 2 = 0
      ∧ countChars case_tool_walk = 20900
      ∧ (case_tool_walk.filter effectivePinned).length = 0
      ∧ outcomeCode pol_tool_walk case_tool_walk = "ok"
      ∧ stepLen pol_tool_walk case_tool_walk = 10
      ∧ stepChars pol_tool_walk case_tool_walk = 19432
      ∧ stepPins pol_tool_walk case_tool_walk = 0
      ∧ (run pol_tool_walk case_tool_walk).length = 10
      ∧ countChars (run pol_tool_walk case_tool_walk) = 19432
      ∧ ((run pol_tool_walk case_tool_walk).filter effectivePinned).length = 0
    := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def case_existing_summary : Conv :=
  [sys 1000, sumMsg 5000, ast 800, usr 2000, ast 3000, usr 1500, ast 2500, usr 1200, ast 1300]
def pol_existing_summary : Policy := mkP 1 2 812 160
theorem case_existing_summary_spec :
    systemHead case_existing_summary = 1
      ∧ startIdx case_existing_summary = 3
      ∧ findKeepIndex case_existing_summary 1 2 = 5
      ∧ cutOf pol_existing_summary case_existing_summary = 5
      ∧ spanChars case_existing_summary 5 = 10800
      ∧ pinChars case_existing_summary 5 = 0
      ∧ countChars case_existing_summary = 18300
      ∧ (case_existing_summary.filter effectivePinned).length = 0
      ∧ outcomeCode pol_existing_summary case_existing_summary = "ok"
      ∧ stepLen pol_existing_summary case_existing_summary = 7
      ∧ stepChars pol_existing_summary case_existing_summary = 8472
      ∧ stepPins pol_existing_summary case_existing_summary = 0
      ∧ (run pol_existing_summary case_existing_summary).length = 7
      ∧ countChars (run pol_existing_summary case_existing_summary) = 8472
      ∧ ((run pol_existing_summary case_existing_summary).filter effectivePinned).length = 0
    := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def case_pin_mid : Conv :=
  [sys 1000, usr 2000, ast 3000, usrPin 2500, ast 4000, usr 1500, ast 1000, usr 1200, ast 1300]
def pol_pin_mid : Policy := mkP 1 2 812 160
theorem case_pin_mid_spec :
    systemHead case_pin_mid = 1
      ∧ startIdx case_pin_mid = 1
      ∧ findKeepIndex case_pin_mid 1 2 = 5
      ∧ cutOf pol_pin_mid case_pin_mid = 5
      ∧ spanChars case_pin_mid 5 = 11500
      ∧ pinChars case_pin_mid 5 = 2500
      ∧ countChars case_pin_mid = 17500
      ∧ (case_pin_mid.filter effectivePinned).length = 1
      ∧ outcomeCode pol_pin_mid case_pin_mid = "ok"
      ∧ stepLen pol_pin_mid case_pin_mid = 8
      ∧ stepChars pol_pin_mid case_pin_mid = 9472
      ∧ stepPins pol_pin_mid case_pin_mid = 1
      ∧ (run pol_pin_mid case_pin_mid).length = 8
      ∧ countChars (run pol_pin_mid case_pin_mid) = 9472
      ∧ ((run pol_pin_mid case_pin_mid).filter effectivePinned).length = 1
    := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def case_pin_saturated : Conv :=
  [sys 1000, usrPin 9000, usrPin 8000, usr 500, ast 600, usr 700, ast 800]
def pol_pin_saturated : Policy := mkP 1 2 372 160
theorem case_pin_saturated_spec :
    systemHead case_pin_saturated = 1
      ∧ startIdx case_pin_saturated = 1
      ∧ findKeepIndex case_pin_saturated 1 2 = 3
      ∧ cutOf pol_pin_saturated case_pin_saturated = 3
      ∧ spanChars case_pin_saturated 3 = 17000
      ∧ pinChars case_pin_saturated 3 = 17000
      ∧ countChars case_pin_saturated = 20600
      ∧ (case_pin_saturated.filter effectivePinned).length = 2
      ∧ outcomeCode pol_pin_saturated case_pin_saturated = "pinBudget"
      ∧ stepLen pol_pin_saturated case_pin_saturated = 7
      ∧ stepChars pol_pin_saturated case_pin_saturated = 20600
      ∧ stepPins pol_pin_saturated case_pin_saturated = 2
      ∧ (run pol_pin_saturated case_pin_saturated).length = 7
      ∧ countChars (run pol_pin_saturated case_pin_saturated) = 20600
      ∧ ((run pol_pin_saturated case_pin_saturated).filter effectivePinned).length = 2
    := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def case_pin_tool_ineligible : Conv :=
  [sys 1000, usr 2000, astCall 3000, toolResPin 4000, usr 1500, ast 1000, usr 1200, ast 1300]
def pol_pin_tool_ineligible : Policy := mkP 1 2 372 160
theorem case_pin_tool_ineligible_spec :
    systemHead case_pin_tool_ineligible = 1
      ∧ startIdx case_pin_tool_ineligible = 1
      ∧ findKeepIndex case_pin_tool_ineligible 1 2 = 4
      ∧ cutOf pol_pin_tool_ineligible case_pin_tool_ineligible = 4
      ∧ spanChars case_pin_tool_ineligible 4 = 9000
      ∧ pinChars case_pin_tool_ineligible 4 = 0
      ∧ countChars case_pin_tool_ineligible = 15000
      ∧ (case_pin_tool_ineligible.filter effectivePinned).length = 0
      ∧ outcomeCode pol_pin_tool_ineligible case_pin_tool_ineligible = "ok"
      ∧ stepLen pol_pin_tool_ineligible case_pin_tool_ineligible = 7
      ∧ stepChars pol_pin_tool_ineligible case_pin_tool_ineligible = 6532
      ∧ stepPins pol_pin_tool_ineligible case_pin_tool_ineligible = 0
      ∧ (run pol_pin_tool_ineligible case_pin_tool_ineligible).length = 7
      ∧ countChars (run pol_pin_tool_ineligible case_pin_tool_ineligible) = 6532
      ∧ ((run pol_pin_tool_ineligible case_pin_tool_ineligible).filter effectivePinned).length = 0
    := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def case_pin_synthetic : Conv :=
  [sys 1000, sumMsgPin 5000, ast 800, usr 2000, ast 3000, usr 1500, ast 2500, usr 1200, 
   ast 1300]
def pol_pin_synthetic : Policy := mkP 1 2 812 160
theorem case_pin_synthetic_spec :
    systemHead case_pin_synthetic = 1
      ∧ startIdx case_pin_synthetic = 3
      ∧ findKeepIndex case_pin_synthetic 1 2 = 5
      ∧ cutOf pol_pin_synthetic case_pin_synthetic = 5
      ∧ spanChars case_pin_synthetic 5 = 10800
      ∧ pinChars case_pin_synthetic 5 = 0
      ∧ countChars case_pin_synthetic = 18300
      ∧ (case_pin_synthetic.filter effectivePinned).length = 0
      ∧ outcomeCode pol_pin_synthetic case_pin_synthetic = "ok"
      ∧ stepLen pol_pin_synthetic case_pin_synthetic = 7
      ∧ stepChars pol_pin_synthetic case_pin_synthetic = 8472
      ∧ stepPins pol_pin_synthetic case_pin_synthetic = 0
      ∧ (run pol_pin_synthetic case_pin_synthetic).length = 7
      ∧ countChars (run pol_pin_synthetic case_pin_synthetic) = 8472
      ∧ ((run pol_pin_synthetic case_pin_synthetic).filter effectivePinned).length = 0
    := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def case_short : Conv :=
  [sys 1000, usr 2000, ast 3000, usr 1500, ast 2500]
def pol_short : Policy := mkP 1 2 372 160
theorem case_short_spec :
    systemHead case_short = 1
      ∧ startIdx case_short = 1
      ∧ findKeepIndex case_short 1 2 = 1
      ∧ cutOf pol_short case_short = 1
      ∧ spanChars case_short 1 = 0
      ∧ pinChars case_short 1 = 0
      ∧ countChars case_short = 10000
      ∧ (case_short.filter effectivePinned).length = 0
      ∧ outcomeCode pol_short case_short = "nothingToCompress"
      ∧ stepLen pol_short case_short = 5
      ∧ stepChars pol_short case_short = 10000
      ∧ stepPins pol_short case_short = 0
      ∧ (run pol_short case_short).length = 5
      ∧ countChars (run pol_short case_short) = 10000
      ∧ ((run pol_short case_short).filter effectivePinned).length = 0
    := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def case_summary_too_large : Conv :=
  [sys 3000, usr 1000, ast 2000, usr 1500, ast 2500, usr 1200, ast 1800, usr 900, ast 1100]
def pol_summary_too_large : Policy := mkP 1 2 7000 160
theorem case_summary_too_large_spec :
    systemHead case_summary_too_large = 1
      ∧ startIdx case_summary_too_large = 1
      ∧ findKeepIndex case_summary_too_large 1 2 = 5
      ∧ cutOf pol_summary_too_large case_summary_too_large = 5
      ∧ spanChars case_summary_too_large 5 = 7000
      ∧ pinChars case_summary_too_large 5 = 0
      ∧ countChars case_summary_too_large = 15000
      ∧ (case_summary_too_large.filter effectivePinned).length = 0
      ∧ outcomeCode pol_summary_too_large case_summary_too_large = "summaryTooLarge"
      ∧ stepLen pol_summary_too_large case_summary_too_large = 9
      ∧ stepChars pol_summary_too_large case_summary_too_large = 15000
      ∧ stepPins pol_summary_too_large case_summary_too_large = 0
      ∧ (run pol_summary_too_large case_summary_too_large).length = 9
      ∧ countChars (run pol_summary_too_large case_summary_too_large) = 15000
      ∧ ((run pol_summary_too_large case_summary_too_large).filter effectivePinned).length = 0
    := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def case_all_system : Conv :=
  [sys 1000, sys 2000]
def pol_all_system : Policy := mkP 1 2 372 160
theorem case_all_system_spec :
    systemHead case_all_system = 2
      ∧ startIdx case_all_system = 2
      ∧ findKeepIndex case_all_system 1 2 = 2
      ∧ cutOf pol_all_system case_all_system = 2
      ∧ spanChars case_all_system 2 = 0
      ∧ pinChars case_all_system 2 = 0
      ∧ countChars case_all_system = 3000
      ∧ (case_all_system.filter effectivePinned).length = 0
      ∧ outcomeCode pol_all_system case_all_system = "nothingToCompress"
      ∧ stepLen pol_all_system case_all_system = 2
      ∧ stepChars pol_all_system case_all_system = 3000
      ∧ stepPins pol_all_system case_all_system = 0
      ∧ (run pol_all_system case_all_system).length = 2
      ∧ countChars (run pol_all_system case_all_system) = 3000
      ∧ ((run pol_all_system case_all_system).filter effectivePinned).length = 0
    := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def case_boundary_exact : Conv :=
  [sys 1000, usr 2000, ast 2000, usr 2000, usr 2000, ast 1000, ast 1000, usr 1000, ast 1000]
def pol_boundary_exact : Policy := mkP 1 2 812 160
theorem case_boundary_exact_spec :
    systemHead case_boundary_exact = 1
      ∧ startIdx case_boundary_exact = 1
      ∧ findKeepIndex case_boundary_exact 1 2 = 4
      ∧ cutOf pol_boundary_exact case_boundary_exact = 4
      ∧ spanChars case_boundary_exact 4 = 6000
      ∧ pinChars case_boundary_exact 4 = 0
      ∧ countChars case_boundary_exact = 13000
      ∧ (case_boundary_exact.filter effectivePinned).length = 0
      ∧ outcomeCode pol_boundary_exact case_boundary_exact = "ok"
      ∧ stepLen pol_boundary_exact case_boundary_exact = 8
      ∧ stepChars pol_boundary_exact case_boundary_exact = 7972
      ∧ stepPins pol_boundary_exact case_boundary_exact = 0
      ∧ (run pol_boundary_exact case_boundary_exact).length = 7
      ∧ countChars (run pol_boundary_exact case_boundary_exact) = 5972
      ∧ ((run pol_boundary_exact case_boundary_exact).filter effectivePinned).length = 0
    := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def case_ratio_3_10 : Conv :=
  [sys 3000, usr 1000, ast 2000, usr 1500, ast 2500, usr 1200, ast 1800, usr 900, ast 1100]
def pol_ratio_3_10 : Policy := mkP 3 10 372 160
theorem case_ratio_3_10_spec :
    systemHead case_ratio_3_10 = 1
      ∧ startIdx case_ratio_3_10 = 1
      ∧ findKeepIndex case_ratio_3_10 3 10 = 5
      ∧ cutOf pol_ratio_3_10 case_ratio_3_10 = 5
      ∧ spanChars case_ratio_3_10 5 = 7000
      ∧ pinChars case_ratio_3_10 5 = 0
      ∧ countChars case_ratio_3_10 = 15000
      ∧ (case_ratio_3_10.filter effectivePinned).length = 0
      ∧ outcomeCode pol_ratio_3_10 case_ratio_3_10 = "ok"
      ∧ stepLen pol_ratio_3_10 case_ratio_3_10 = 7
      ∧ stepChars pol_ratio_3_10 case_ratio_3_10 = 8532
      ∧ stepPins pol_ratio_3_10 case_ratio_3_10 = 0
      ∧ (run pol_ratio_3_10 case_ratio_3_10).length = 7
      ∧ countChars (run pol_ratio_3_10 case_ratio_3_10) = 8532
      ∧ ((run pol_ratio_3_10 case_ratio_3_10).filter effectivePinned).length = 0
    := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def case_pin_multi_round : Conv :=
  [sys 1000, sumMsg 812, ast 160, usrPin 2500, usr 3000, ast 4000, usr 1500, ast 1000, 
   usr 1200, ast 1300]
def pol_pin_multi_round : Policy := mkP 1 2 812 160
theorem case_pin_multi_round_spec :
    systemHead case_pin_multi_round = 1
      ∧ startIdx case_pin_multi_round = 3
      ∧ findKeepIndex case_pin_multi_round 1 2 = 6
      ∧ cutOf pol_pin_multi_round case_pin_multi_round = 6
      ∧ spanChars case_pin_multi_round 6 = 10472
      ∧ pinChars case_pin_multi_round 6 = 2500
      ∧ countChars case_pin_multi_round = 16472
      ∧ (case_pin_multi_round.filter effectivePinned).length = 1
      ∧ outcomeCode pol_pin_multi_round case_pin_multi_round = "ok"
      ∧ stepLen pol_pin_multi_round case_pin_multi_round = 8
      ∧ stepChars pol_pin_multi_round case_pin_multi_round = 9472
      ∧ stepPins pol_pin_multi_round case_pin_multi_round = 1
      ∧ (run pol_pin_multi_round case_pin_multi_round).length = 8
      ∧ countChars (run pol_pin_multi_round case_pin_multi_round) = 9472
      ∧ ((run pol_pin_multi_round case_pin_multi_round).filter effectivePinned).length = 1
    := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def case_pin_assistant_ineligible : Conv :=
  [sys 1000, usr 2000, astPin 2500, usr 3000, ast 4000, usr 1500, ast 1000, usr 1200, ast 1300]
def pol_pin_assistant_ineligible : Policy := mkP 1 2 812 160
theorem case_pin_assistant_ineligible_spec :
    systemHead case_pin_assistant_ineligible = 1
      ∧ startIdx case_pin_assistant_ineligible = 1
      ∧ findKeepIndex case_pin_assistant_ineligible 1 2 = 5
      ∧ cutOf pol_pin_assistant_ineligible case_pin_assistant_ineligible = 5
      ∧ spanChars case_pin_assistant_ineligible 5 = 11500
      ∧ pinChars case_pin_assistant_ineligible 5 = 0
      ∧ countChars case_pin_assistant_ineligible = 17500
      ∧ (case_pin_assistant_ineligible.filter effectivePinned).length = 0
      ∧ outcomeCode pol_pin_assistant_ineligible case_pin_assistant_ineligible = "ok"
      ∧ stepLen pol_pin_assistant_ineligible case_pin_assistant_ineligible = 7
      ∧ stepChars pol_pin_assistant_ineligible case_pin_assistant_ineligible = 6972
      ∧ stepPins pol_pin_assistant_ineligible case_pin_assistant_ineligible = 0
      ∧ (run pol_pin_assistant_ineligible case_pin_assistant_ineligible).length = 7
      ∧ countChars (run pol_pin_assistant_ineligible case_pin_assistant_ineligible) = 6972
      ∧ ((run pol_pin_assistant_ineligible case_pin_assistant_ineligible).filter effectivePinned).length = 0
    := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def case_pin_inline_span : Conv :=
  [sys 1000, usr 2000, usrPinSpan 2500 400, usr 3000, ast 4000, usr 1500, ast 1000, usr 1200, 
   ast 1300]
def pol_pin_inline_span : Policy := mkP 1 2 812 160
theorem case_pin_inline_span_spec :
    systemHead case_pin_inline_span = 1
      ∧ startIdx case_pin_inline_span = 1
      ∧ findKeepIndex case_pin_inline_span 1 2 = 5
      ∧ cutOf pol_pin_inline_span case_pin_inline_span = 5
      ∧ spanChars case_pin_inline_span 5 = 11500
      ∧ pinChars case_pin_inline_span 5 = 400
      ∧ countChars case_pin_inline_span = 17500
      ∧ (case_pin_inline_span.filter effectivePinned).length = 1
      ∧ outcomeCode pol_pin_inline_span case_pin_inline_span = "ok"
      ∧ stepLen pol_pin_inline_span case_pin_inline_span = 8
      ∧ stepChars pol_pin_inline_span case_pin_inline_span = 7372
      ∧ stepPins pol_pin_inline_span case_pin_inline_span = 1
      ∧ (run pol_pin_inline_span case_pin_inline_span).length = 8
      ∧ countChars (run pol_pin_inline_span case_pin_inline_span) = 7372
      ∧ ((run pol_pin_inline_span case_pin_inline_span).filter effectivePinned).length = 1
    := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def case_sys_boundary_tail : Conv :=
  [sys 3000, usr 1000, ast 2000, usr 1500, ast 2500, sys 3200, usr 1200, ast 1800, usr 900, 
   ast 1100]
def pol_sys_boundary_tail : Policy := mkP 1 2 812 160
theorem case_sys_boundary_tail_spec :
    systemHead case_sys_boundary_tail = 1
      ∧ startIdx case_sys_boundary_tail = 1
      ∧ findKeepIndex case_sys_boundary_tail 1 2 = 6
      ∧ cutOf pol_sys_boundary_tail case_sys_boundary_tail = 4
      ∧ spanChars case_sys_boundary_tail 4 = 4500
      ∧ pinChars case_sys_boundary_tail 4 = 0
      ∧ countChars case_sys_boundary_tail = 18200
      ∧ (case_sys_boundary_tail.filter effectivePinned).length = 0
      ∧ outcomeCode pol_sys_boundary_tail case_sys_boundary_tail = "ok"
      ∧ stepLen pol_sys_boundary_tail case_sys_boundary_tail = 9
      ∧ stepChars pol_sys_boundary_tail case_sys_boundary_tail = 14672
      ∧ stepPins pol_sys_boundary_tail case_sys_boundary_tail = 0
      ∧ (run pol_sys_boundary_tail case_sys_boundary_tail).length = 9
      ∧ countChars (run pol_sys_boundary_tail case_sys_boundary_tail) = 14672
      ∧ ((run pol_sys_boundary_tail case_sys_boundary_tail).filter effectivePinned).length = 0
    := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def case_dangling_call : Conv :=
  [sys 3000, usr 1000, ast 2000, usr 1500, astCall 400, usr 1000, ast 2500, usr 1200, ast 1800]
def pol_dangling_call : Policy := mkP 1 2 812 160
theorem case_dangling_call_spec :
    systemHead case_dangling_call = 1
      ∧ startIdx case_dangling_call = 1
      ∧ findKeepIndex case_dangling_call 1 2 = 5
      ∧ cutOf pol_dangling_call case_dangling_call = 4
      ∧ spanChars case_dangling_call 4 = 4500
      ∧ pinChars case_dangling_call 4 = 0
      ∧ countChars case_dangling_call = 14400
      ∧ (case_dangling_call.filter effectivePinned).length = 0
      ∧ outcomeCode pol_dangling_call case_dangling_call = "ok"
      ∧ stepLen pol_dangling_call case_dangling_call = 8
      ∧ stepChars pol_dangling_call case_dangling_call = 10872
      ∧ stepPins pol_dangling_call case_dangling_call = 0
      ∧ (run pol_dangling_call case_dangling_call).length = 8
      ∧ countChars (run pol_dangling_call case_dangling_call) = 10872
      ∧ ((run pol_dangling_call case_dangling_call).filter effectivePinned).length = 0
    := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- CORPUS-END


/-! ## 9. Tag authentication — the pin/summary MAC (defects D-C / D-D)

Sections 1–8 take `Msg.pinned` and `Msg.synthetic` as GIVEN booleans. That is
exactly the gap every defect of the last two rounds lived in: in the shipped
proxy neither flag is given, both are *computed from attacker-controllable text*
by `_is_pinned` / `_is_synthetic`. `synthetic_never_pinned` is a theorem about
the FLAG; whether the flag can be made to lie is a question about this section.

The MAC here is modelled as **ideal** — a tag literally is the tuple it commits
to, so there are no collisions whatsoever, and forgery-without-the-secret is
impossible by construction. Anything this section exhibits is therefore a
STRUCTURAL break that a bigger digest cannot fix. -/

/-- Which marker a tag is written under. -/
inductive TagKind where
  | pin
  | summary
deriving DecidableEq, Repr

abbrev Secret := String
abbrev Body := String

/-- An ideal MAC value: the tuple the tag commits to. `kind = none` models a MAC
computed over the body ALONE — no domain separation. -/
structure Tag where
  secret : Secret
  kind : Option TagKind
  body : Body
deriving DecidableEq, Repr

/-- `_mint_tag(body)` **as shipped**: `hmac(PIN_SECRET, body)`. Note the `TagKind`
argument is ignored — that is not modelling laziness, it is the defect. -/
def mintShipped (s : Secret) (_k : TagKind) (b : Body) : Tag :=
  { secret := s, kind := none, body := b }

/-- The repair: the tag commits to the marker it will be written under. -/
def mintFixed (s : Secret) (k : TagKind) (b : Body) : Tag :=
  { secret := s, kind := some k, body := b }

/-- Message text as the tag layer sees it: a canonical body plus embedded tags.
`_strip_tags` removes tags of BOTH kinds, so `body` is what the MAC is taken
over regardless of which marker carried the tag. -/
structure TaggedText where
  tags : List (TagKind × Tag) := []
  body : Body := ""
deriving DecidableEq, Repr

/-- `_strip_tags`. -/
def canonBody (t : TaggedText) : Body := t.body

/-- `pattern.search`: the FIRST tag written under marker `k`, or none. -/
def firstTag (k : TagKind) (t : TaggedText) : Option Tag :=
  match t.tags.find? (fun p => p.1 == k) with
  | some p => some p.2
  | none => none

/-- `_verify_tag`, parameterised by the mint so shipped and fixed share it. -/
def verifyWith (mint : Secret → TagKind → Body → Tag)
    (s : Secret) (k : TagKind) (t : TaggedText) : Bool :=
  match firstTag k t with
  | some tg => tg == mint s k (canonBody t)
  | none => false

def verifyShipped (s : Secret) (k : TagKind) (t : TaggedText) : Bool :=
  verifyWith mintShipped s k t

def verifyFixed (s : Secret) (k : TagKind) (t : TaggedText) : Bool :=
  verifyWith mintFixed s k t

/-- What `POST /pin` hands back for `b`. The route is unauthenticated and bound
to loopback, so any agent with a shell reaches it. -/
def pinRouteOutput (s : Secret) (b : Body) : TaggedText :=
  { tags := [(TagKind.pin, mintShipped s TagKind.pin b)], body := b }

/-- The identical tag value, re-written under the SUMMARY marker. -/
def replayAsSummary (s : Secret) (b : Body) : TaggedText :=
  { tags := [(TagKind.summary, mintShipped s TagKind.pin b)], body := b }

/-- The proxy's own summary, as it appears in the model's context. -/
def proxySummary (s : Secret) (b : Body) : TaggedText :=
  { tags := [(TagKind.summary, mintShipped s TagKind.summary b)], body := b }

/-- The same tag lifted out of the summary and re-written as a PIN. Requires no
oracle at all: the tag is sitting in the context window. -/
def modelReplayPin (s : Secret) (b : Body) : TaggedText :=
  { tags := [(TagKind.pin, mintShipped s TagKind.summary b)], body := b }

/-- **[LOAD-BEARING]** the shipped MAC is kind-blind, so a tag minted for one
marker authenticates under the other. With `POST /pin` reachable this turns the
pin route into a SUMMARY-forgery oracle and reopens defect D-D in full.

Mutation that breaks it: give `mintShipped` the `k` argument (i.e. `mintFixed`). -/
theorem shipped_tag_kind_confusion (s : Secret) (b : Body) :
    verifyShipped s TagKind.pin (pinRouteOutput s b) = true
      ∧ verifyShipped s TagKind.summary (replayAsSummary s b) = true := by
  constructor <;>
    simp [verifyShipped, verifyWith, firstTag, mintShipped, pinRouteOutput,
      replayAsSummary, canonBody]

/-- **[LOAD-BEARING]** and the oracle is not even needed: the tag on the proxy's
OWN summary replays as a pin on a verbatim copy of the summary body. The copy
reads as pinned and NOT synthetic, which is precisely the configuration
`synthetic_never_pinned` exists to make impossible — an unbounded stack of
summaries, each pinned verbatim and regenerated every round.

`synthetic_never_pinned` is not wrong; it is a theorem about `Msg.synthetic`.
This says the flag is not a faithful oracle for "the proxy wrote it".

Mutation that breaks it: domain-separate the mint. -/
theorem summary_tag_replays_as_pin (s : Secret) (b : Body) :
    verifyShipped s TagKind.summary (proxySummary s b) = true
      ∧ verifyShipped s TagKind.pin (modelReplayPin s b) = true
      ∧ verifyShipped s TagKind.summary (modelReplayPin s b) = false
      ∧ canonBody (modelReplayPin s b) = canonBody (proxySummary s b) := by
  refine ⟨?_, ?_, ?_, rfl⟩ <;>
    simp [verifyShipped, verifyWith, firstTag, mintShipped, proxySummary,
      modelReplayPin, canonBody]

/-- **[LOAD-BEARING]** domain separation closes both attacks: a tag minted under
one marker never verifies under the other, for every secret and every body. -/
theorem fixed_blocks_kind_confusion (s : Secret) (b : Body) :
    verifyFixed s TagKind.summary
        { tags := [(TagKind.summary, mintFixed s TagKind.pin b)], body := b } = false
      ∧ verifyFixed s TagKind.pin
        { tags := [(TagKind.pin, mintFixed s TagKind.summary b)], body := b } = false := by
  constructor <;> simp [verifyFixed, verifyWith, firstTag, mintFixed, canonBody]

/-- **[LOAD-BEARING]** the fixed mint still ACCEPTS the honest case, so the
repair is not "reject everything". -/
theorem fixed_accepts_honest (s : Secret) (b : Body) :
    verifyFixed s TagKind.pin
        { tags := [(TagKind.pin, mintFixed s TagKind.pin b)], body := b } = true
      ∧ verifyFixed s TagKind.summary
        { tags := [(TagKind.summary, mintFixed s TagKind.summary b)], body := b } = true := by
  constructor <;> simp [verifyFixed, verifyWith, firstTag, mintFixed, canonBody]

-- Executable witnesses: the attacks, computed rather than asserted.
#guard verifyShipped "SEC" TagKind.summary (replayAsSummary "SEC" "forged summary") = true
#guard verifyShipped "SEC" TagKind.pin (modelReplayPin "SEC" "summary body") = true
#guard verifyFixed "SEC" TagKind.summary
  { tags := [(TagKind.summary, mintFixed "SEC" TagKind.pin "forged summary")],
    body := "forged summary" } = false


/-! ## 10. `_validate_tool_pairs` — the sanitizer that runs AFTER `rebuild`

`pinned_never_cut` is a theorem about `rebuild`. The server then calls
`_validate_tool_pairs` on the merged payload, and nothing above can see it.
Defect D-E was exactly that blind spot: the sanitizer deleted the whole leading
run, summary and pins included.

The repair added a RESCUE. This section models the repaired function and asks
the only question that matters for a function whose job is removing orphans:
**is its output orphan-free?** It is not. -/

/-- A message as the server layer sees it: ids matter, characters do not. -/
structure SMsg where
  role : Role
  callIds : List String := []
  resultId : Option String := none
  text : TaggedText := {}
  pinnedFlag : Bool := false
deriving DecidableEq, Repr

/-- The proxy ack literal, canonicalised. -/
def ackBody : Body := "ACK"

def sHasToolUse (m : SMsg) : Bool := !m.callIds.isEmpty

/-- `_is_synthetic`. Note what it does NOT test: the role, and the presence of
tool ids. That omission is the subject of `rescue_can_emit_orphan`. -/
def sIsSynthetic (s : Secret) (m : SMsg) : Bool :=
  verifyShipped s TagKind.summary m.text || (canonBody m.text == ackBody)

def sIsPinned (s : Secret) (m : SMsg) : Bool :=
  m.pinnedFlag || verifyShipped s TagKind.pin m.text

def sPinEligible (s : Secret) (m : SMsg) : Bool :=
  (m.role == Role.user || m.role == Role.assistant) && !sHasToolUse m && !sIsSynthetic s m

def sEffectivePinned (s : Secret) (m : SMsg) : Bool :=
  sIsPinned s m && sPinEligible s m

/-- `_system_prefix_len`. -/
def sysPrefixLen : List SMsg → Nat
  | [] => 0
  | m :: ms => if m.role = Role.system then sysPrefixLen ms + 1 else 0

/-- The `valid_from` scan, transcribed. `known` accumulates over the WHOLE body
from index 0 — including messages the function is about to drop. -/
def validFromAux : List SMsg → Nat → List String → Nat → Nat
  | [], _, _, vf => vf
  | m :: ms, i, known, vf =>
      if m.role = Role.assistant then
        validFromAux ms (i + 1) (known ++ m.callIds) vf
      else if m.role = Role.tool then
        match m.resultId with
        | some rid =>
            if known.contains rid then validFromAux ms (i + 1) known vf
            else validFromAux ms (i + 1) known (i + 1)
        | none => validFromAux ms (i + 1) known (i + 1)
      else validFromAux ms (i + 1) known vf

def validFrom (body : List SMsg) : Nat := validFromAux body 0 [] 0

/-- The D-E rescue predicate, as shipped. -/
def rescuableShipped (s : Secret) (m : SMsg) : Bool :=
  sEffectivePinned s m || sIsSynthetic s m

/-- `_validate_tool_pairs` as shipped after the D-E fix. -/
def validateToolPairs (s : Secret) (msgs : List SMsg) : List SMsg :=
  let head := sysPrefixLen msgs
  let sys := msgs.take head
  let body := msgs.drop head
  let vf := validFrom body
  if vf = 0 then sys ++ body
  else sys ++ (body.take vf).filter (rescuableShipped s) ++ body.drop vf

/-- Wire-legality: every `tool` message is preceded by an assistant that issued
its id. Violating this is a hard 400 from Mistral. -/
def orphanFreeAux : List SMsg → List String → Bool
  | [], _ => true
  | m :: ms, known =>
      if m.role = Role.assistant then orphanFreeAux ms (known ++ m.callIds)
      else if m.role = Role.tool then
        match m.resultId with
        | some rid => known.contains rid && orphanFreeAux ms known
        | none => false
      else orphanFreeAux ms known

def orphanFree (msgs : List SMsg) : Bool := orphanFreeAux msgs []

/-! ### Counterexample 1 — the rescue emits an orphan (defect in the D-E fix)

`_is_synthetic` is content-only, so a **tool result** whose text is the ack
literal counts as synthetic and gets rescued, while the assistant that issued
its `tool_call_id` is dropped. A model that makes any tool print the ack literal
reaches this; so does a summary tag minted through `POST /pin`. -/

def atkAckToolResult : List SMsg :=
  [ { role := Role.system }
  , { role := Role.assistant, callIds := ["call_A"] }
  , { role := Role.tool, resultId := some "call_A", text := { body := ackBody } }
  , { role := Role.tool, resultId := some "call_GHOST" }
  , { role := Role.user } ]

/-! ### Counterexample 2 — `known` accumulates across DROPPED messages

Independent of the rescue, and older than it: `known_ids` is built from index 0,
so a tool message that SURVIVES can have been validated against an assistant
that did not. -/

def atkDroppedCall : List SMsg :=
  [ { role := Role.system }
  , { role := Role.assistant, callIds := ["call_X"] }
  , { role := Role.tool, resultId := some "call_GHOST" }
  , { role := Role.user }
  , { role := Role.tool, resultId := some "call_X" } ]

/-- **[LOAD-BEARING]** the sanitizer whose entire purpose is removing orphans
emits one, and the result is a FIXED POINT — running it again does not repair
the payload, so the session wedges on a hard 400 rather than degrading.

Mutation that breaks it: gate the rescue on role and tool-freedom
(`rescuableFixed`). -/
theorem rescue_can_emit_orphan :
    orphanFree (validateToolPairs "S" atkAckToolResult) = false
      ∧ validateToolPairs "S" (validateToolPairs "S" atkAckToolResult)
          = validateToolPairs "S" atkAckToolResult := by
  constructor <;> rfl

/-- **[LOAD-BEARING]** the second, independent orphan path: `known` is
accumulated over messages that are then dropped. This one predates the D-E fix
and is not caused by the rescue — `rescuableShipped` rescues nothing here. -/
theorem known_ids_span_dropped_messages :
    orphanFree atkDroppedCall = false
      ∧ orphanFree (validateToolPairs "S" atkDroppedCall) = false := by
  constructor <;> rfl

/-! ### The repair -/

/-- Rescue only what can carry neither half of a tool group. -/
def rescuableFixed (s : Secret) (m : SMsg) : Bool :=
  (sEffectivePinned s m || sIsSynthetic s m)
    && (m.role == Role.user || m.role == Role.assistant)
    && m.callIds.isEmpty && m.resultId.isNone

/-- Recompute validity over the SURVIVING messages: drop any tool message whose
call is not present earlier in the output being built. -/
def dropOrphansAux : List SMsg → List String → List SMsg
  | [], _ => []
  | m :: ms, known =>
      if m.role = Role.assistant then m :: dropOrphansAux ms (known ++ m.callIds)
      else if m.role = Role.tool then
        match m.resultId with
        | some rid =>
            if known.contains rid then m :: dropOrphansAux ms known
            else dropOrphansAux ms known
        | none => dropOrphansAux ms known
      else m :: dropOrphansAux ms known

def validateToolPairsFixed (s : Secret) (msgs : List SMsg) : List SMsg :=
  let head := sysPrefixLen msgs
  let sys := msgs.take head
  let body := msgs.drop head
  let vf := validFrom body
  let kept := (body.take vf).filter (rescuableFixed s) ++ body.drop vf
  sys ++ dropOrphansAux kept []

/-- **[LOAD-BEARING]** the orphan filter is correct relative to any starting
knowledge set. This is the induction the headline theorem rests on; MEASURED as
killed by M37, so it is not mere scaffolding. -/
theorem dropOrphansAux_orphanFree (l : List SMsg) :
    ∀ known : List String, orphanFreeAux (dropOrphansAux l known) known = true := by
  induction l with
  | nil => intro known; rfl
  | cons m ms ih =>
    intro known
    by_cases ha : m.role = Role.assistant
    · simp [dropOrphansAux, orphanFreeAux, ha, ih]
    · by_cases ht : m.role = Role.tool
      · cases hr : m.resultId with
        | none => simp [dropOrphansAux, ht, hr, ih]
        | some rid =>
          by_cases hk : rid ∈ known
          · simp [dropOrphansAux, orphanFreeAux, ht, hr, hk, ih]
          · simp [dropOrphansAux, ht, hr, hk, ih]
      · simp [dropOrphansAux, orphanFreeAux, ha, ht, ih]

/-- **[INFRASTRUCTURE]** a leading run of system messages neither supplies nor
consumes tool ids. -/
theorem orphanFreeAux_system_prefix (sys : List SMsg)
    (h : ∀ m ∈ sys, m.role = Role.system) (rest : List SMsg) (known : List String) :
    orphanFreeAux (sys ++ rest) known = orphanFreeAux rest known := by
  induction sys with
  | nil => rfl
  | cons m ms ih =>
    have hm : m.role = Role.system := h m (by simp)
    have hms : ∀ x ∈ ms, x.role = Role.system := fun x hx => h x (by simp [hx])
    have ha : ¬ (m.role = Role.assistant) := by rw [hm]; intro hc; cases hc
    have ht : ¬ (m.role = Role.tool) := by rw [hm]; intro hc; cases hc
    simp [orphanFreeAux, ha, ht, ih hms]

/-- **[LOAD-BEARING]** the leading `sysPrefixLen` messages really are system.
MEASURED as killed by M46 (`sysPrefixLen: always 0`), which is the server-layer
twin of the D3 mutation M15. -/
theorem mem_take_sysPrefixLen (c : List SMsg) :
    ∀ m ∈ c.take (sysPrefixLen c), m.role = Role.system := by
  induction c with
  | nil => intro m hm; simp at hm
  | cons a as ih =>
    intro m hm
    by_cases h : a.role = Role.system
    · simp [sysPrefixLen, h, List.take_succ_cons] at hm
      rcases hm with hm | hm
      · rw [hm]; exact h
      · exact ih m hm
    · simp [sysPrefixLen, h] at hm

/-- **[LOAD-BEARING]** the repaired sanitizer emits an orphan-free payload for
EVERY input — not for a corpus, for every input. This is the property the
shipped function lacks and the reason the two counterexamples above exist.

Mutation that breaks it: drop the `dropOrphansAux` pass, or ungate the rescue. -/
theorem fixed_validate_orphanFree (s : Secret) (msgs : List SMsg) :
    orphanFree (validateToolPairsFixed s msgs) = true := by
  unfold orphanFree validateToolPairsFixed
  rw [orphanFreeAux_system_prefix _ (mem_take_sysPrefixLen msgs)]
  exact dropOrphansAux_orphanFree _ []

/-- **[LOAD-BEARING]** and the repair is not "delete everything": on both attack
inputs it keeps the legal messages and sheds only the orphans. -/
theorem fixed_validate_keeps_content :
    (validateToolPairsFixed "S" atkAckToolResult).length = 2
      ∧ (validateToolPairsFixed "S" atkDroppedCall).length = 2 := by
  constructor <;> rfl

-- Executed, not asserted.
#guard orphanFree atkAckToolResult = false
#guard orphanFree (validateToolPairs "S" atkAckToolResult) = false
#guard orphanFree (validateToolPairs "S" atkDroppedCall) = false
#guard orphanFree (validateToolPairsFixed "S" atkAckToolResult) = true
#guard orphanFree (validateToolPairsFixed "S" atkDroppedCall) = true


/-! ## 11. The key chain — `_hash_messages`, `chain_start`, `find_match`

Defect D-A lived here, and the fix carries a claim in a code comment:

> Over-skipping is harmless here: only `match_end` determines the injection
> point, so skipping a message that was not actually pinned costs nothing.

That claim is the subject of this section. It is **false**, and the reason is
that `find_match` returns the FIRST occurrence of the chain: shortening a chain
strictly widens the set of positions it can match at, so `match_end` itself can
move earlier. `match_end` is not invariant under over-skipping — it is the very
thing over-skipping perturbs. -/

abbrev Hash := String

/-- `start = 2` then the D-A forward walk over effectively-pinned messages. -/
def chainStartWalk (s : Secret) : Nat → List SMsg → Nat
  | i, [] => i
  | i, m :: ms => if sEffectivePinned s m then chainStartWalk s (i + 1) ms else i

/-- The shipped `start`: skip `[summary, ack]`, then walk pins. -/
def chainStart (s : Secret) (summarized : List SMsg) : Nat :=
  chainStartWalk s 2 (summarized.drop 2)

/-- `msg_hashes[start:start+len] == oh`, i.e. a contiguous occurrence. -/
def occursAt (chain : List Hash) (hs : List Hash) : Bool :=
  hs.take chain.length == chain

/-- `CompressionStore.find_match`, transcribed: the FIRST contiguous occurrence,
returning the index one past its end. `if not oh: continue` is the `isEmpty`
guard — an empty chain is skipped, never treated as a wildcard. -/
def findMatchGo : Nat → List Hash → List Hash → Option Nat
  | _, _, [] => none
  | n, chain, h :: t =>
      if occursAt chain (h :: t) then some (n + chain.length)
      else findMatchGo (n + 1) chain t

def findMatchEnd (chain : List Hash) (hs : List Hash) : Option Nat :=
  if chain.isEmpty then none else findMatchGo 0 chain hs

/-! ### The refutation

`hsAmbiguous` is a request whose hash sequence repeats — the ordinary case in an
agent loop, where an identical short tool result or an identical "continue" turn
recurs. `chainTrue` is the chain that starts on the pinned message; `chainOver`
is the same chain with that one message over-skipped. -/

def hsAmbiguous : List Hash := ["a", "b", "q", "p", "a", "b"]
def chainTrue : List Hash := ["p", "a", "b"]
def chainOver : List Hash := ["a", "b"]

/-- **[LOAD-BEARING]** over-skipping moves `match_end`. The full chain first
matches at end 6; the over-skipped chain first matches at end 2. The server then
computes `new_messages = messages[match_end:]`, so the summary prefix is spliced
over a four-message-shorter span — the messages the summary already covers are
left in the payload alongside it, which is duplication, not compression.

This refutes the comment at both D-A sites. Over-skipping is safe only when the
shortened chain has no earlier occurrence, which is a property of the traffic,
not of the code.

Mutation that breaks it: make `findMatchEnd` return the LAST occurrence. -/
theorem overskip_moves_match_end :
    findMatchEnd chainTrue hsAmbiguous = some 6
      ∧ findMatchEnd chainOver hsAmbiguous = some 2 := by
  constructor <;> rfl

/-- **[LOAD-BEARING]** the one thing over-skipping cannot do is turn the entry
into a wildcard: an empty chain never matches, for every request. So the failure
mode of skipping everything is a dead entry — a paid summarizer call whose
result can never be injected — and not a mis-splice. That half of the comment
holds.

Mutation that breaks it: drop the `chain.isEmpty` guard (i.e. `if not oh`). -/
theorem empty_chain_never_matches (hs : List Hash) : findMatchEnd [] hs = none := by
  simp [findMatchEnd]

/-- **[DECORATIVE]** under-skipping is the failure D-A actually fixed: a chain
that still begins on the pinned message cannot match a client history in which
that message sits near the front rather than at the summary boundary.

MEASURED: no mutation in `mutate-lean.py` kills this. It is a computed
illustration of D-A, not a guarantee — exact contiguous matching makes "a chain
containing an absent hash does not match" true of any correct matcher, so the
statement constrains nothing that `findMatchEnd` could get wrong. Kept because
it documents the defect concretely; labelled honestly because it is not
evidence. The load-bearing content of D-A is `chainStart_walks_pins`. -/
def hsClient : List Hash := ["u1", "pin", "u2", "a2", "u3"]
def chainUnderSkipped : List Hash := ["pin", "u2", "a2"]
def chainWalked : List Hash := ["u2", "a2"]

theorem underskip_kills_the_match :
    findMatchEnd chainUnderSkipped ["u2", "a2", "u3"] = none
      ∧ findMatchEnd chainWalked ["u2", "a2", "u3"] = some 2 := by
  constructor <;> rfl

/-! ### The walk itself

`chainStartWalk` stops at the first non-pinned message. Its correctness is
therefore conditional on the hoisted pins being CONTIGUOUS from index 2, which
`rebuild` does guarantee — `pinnedIn` emits them as one block directly after
`[summary, ack]`. But pin status is recomputed by HMAC at walk time, so the walk
sees the pins only while the secret is stable; `_load_pin_secret` falls back to a
process-local secret on any `OSError`, and after that fallback every previously
tagged message stops verifying and the walk under-skips. -/

/-- **[INFRASTRUCTURE]** the walk stops at the first message that does not
verify. MEASURED: no mutation kills this, and the reason is instructive — M40
(`the walk never advances`) makes the walk return `i` unconditionally, which
still satisfies this statement. The negative half alone therefore does not
pin down the walk; `walk_advances_on_pinned` is the half that does. -/
theorem walk_stops_at_first_unpinned (s : Secret) (i : Nat) (m : SMsg) (ms : List SMsg)
    (h : sEffectivePinned s m = false) :
    chainStartWalk s i (m :: ms) = i := by
  simp [chainStartWalk, h]

/-- **[LOAD-BEARING]** the positive half: on a pinned message the walk ADVANCES.
Together with `walk_stops_at_first_unpinned` this characterises the D-A walk,
and unlike that theorem it is destroyed by M40 — the mutation that reinstates
the bare `start = 2` of the original defect.

When verification fails wholesale — the rotated-secret case, which
`_load_pin_secret` reaches on any `OSError` — every tagged message stops
verifying, the walk takes the stopping branch immediately, and the chain
silently degrades to exactly the `start = 2` D-A was raised to fix. -/
theorem walk_advances_on_pinned (s : Secret) (i : Nat) (m : SMsg) (ms : List SMsg)
    (h : sEffectivePinned s m = true) :
    chainStartWalk s i (m :: ms) = chainStartWalk s (i + 1) ms := by
  simp [chainStartWalk, h]

def pinnedMsg : SMsg := { role := Role.user, pinnedFlag := true }
def plainMsg : SMsg := { role := Role.user }

/-- **[LOAD-BEARING]** the whole point of D-A, as an executed example: with two
hoisted pins the chain must start at 4, not 2. -/
theorem chainStart_walks_pins :
    chainStart "S" [plainMsg, plainMsg, pinnedMsg, pinnedMsg, plainMsg] = 4
      ∧ chainStart "S" [plainMsg, plainMsg, plainMsg] = 2 := by
  constructor <;> rfl

-- Executed, not asserted.
#guard findMatchEnd chainTrue hsAmbiguous = some 6
#guard findMatchEnd chainOver hsAmbiguous = some 2
#guard findMatchEnd [] hsAmbiguous = none
#guard chainStart "S" [plainMsg, plainMsg, pinnedMsg, pinnedMsg, plainMsg] = 4
#eval "over-skipped match_end = " ++ toString (findMatchEnd chainOver hsAmbiguous)
#eval "true       match_end = " ++ toString (findMatchEnd chainTrue hsAmbiguous)

/-! ## 12. The sanitizer as SHIPPED vs as MODELLED (review 4)

Section 10 proves `fixed_validate_orphanFree` about `validateToolPairsFixed`.
That function applies `dropOrphansAux` **unconditionally**. The Python it claims
to describe did not:

```python
if valid_from == 0:
    return system_msgs + body          # <-- no sweep on this branch
...
return _drop_broken_tool_groups(system_msgs + rescued + body[valid_from:])
```

So the proof described a function nobody had implemented, and said nothing about
the branch that ordinary traffic actually takes. Two further gaps, both MEASURED
by exhaustive search over every message sequence of length ≤ 6 (137,256 inputs):

* `orphanFree` only constrains **tool results**. The Python docstring claims both
  directions ("Mistral rejects BOTH"), and a dangling **call** is the artefact a
  cut between a call and its results actually produces. That direction had no
  predicate here at all, so no theorem could see it.
* `_drop_broken_tool_groups` decided membership with SETS, ignoring position, so
  a result preceding its call counted as satisfied.

This section adds the missing predicate, models the shipped function honestly,
exhibits the counterexamples as executed `#guard`s, and proves the repair that
was landed in `vibe-rc-server.py` this round. -/

/-- The direction `orphanFree` does not capture: every id announced by a kept
assistant must have a matching tool result LATER in the list. An assistant whose
`tool_calls` carry no usable id can never be satisfied, so it counts as dangling.
Mistral: "Not the same number of function calls and responses". -/
def danglingFreeAux : List SMsg → Bool
  | [] => true
  | m :: ms =>
      if m.role = Role.assistant && !m.callIds.isEmpty then
        m.callIds.all (fun cid => ms.any (fun r =>
          r.role = Role.tool && r.resultId = some cid)) && danglingFreeAux ms
      else danglingFreeAux ms

def danglingFree (msgs : List SMsg) : Bool := danglingFreeAux msgs

/-- `_validate_tool_pairs` as it was SHIPPED before review 4: the sweep is skipped
whenever the prefix walk found nothing. `sweep` stands for any final pass. -/
def validateToolPairsShipped (sweep : List SMsg → List SMsg)
    (s : Secret) (msgs : List SMsg) : List SMsg :=
  let head := sysPrefixLen msgs
  let sys := msgs.take head
  let body := msgs.drop head
  let vf := validFrom body
  if vf = 0 then sys ++ body
  else sweep (sys ++ (body.take vf).filter (rescuableFixed s) ++ body.drop vf)

/-- A dangling call with no orphan result anywhere: `validFrom = 0`, so the
shipped function returns it untouched no matter how good `sweep` is. -/
def atkDanglingCall : List SMsg :=
  [ { role := Role.system }
  , { role := Role.assistant, callIds := ["call_D"] }
  , { role := Role.user } ]

/-- **[LOAD-BEARING]** the early return defeats the sweep *for every possible
sweep*. Quantifying over `sweep` is the point: this is not a weakness of the
particular pass that was written, it is the branch never reaching one.

Mutation that breaks it: make the shipped model unconditional (i.e. delete the
`if vf = 0` arm), which is exactly the repair landed in the server. -/
theorem shipped_early_return_defeats_any_sweep (sweep : List SMsg → List SMsg) :
    danglingFree (validateToolPairsShipped sweep "S" atkDanglingCall) = false := by
  rfl

/-- **[LOAD-BEARING]** and the same input is a FIXED POINT of the shipped
function, so re-running the sanitizer never repairs it. -/
theorem shipped_dangling_is_stable (sweep : List SMsg → List SMsg) :
    validateToolPairsShipped sweep "S" atkDanglingCall = atkDanglingCall := by
  rfl

/-- The repair, as landed: sweep unconditionally, and reject in BOTH directions.
`dropOrphansAux` already removes orphan results in order; `dropDangling` removes
assistants whose ids lack a later result. Dropping an assistant can orphan a
result that depended on it, so the two are iterated to a fixpoint — modelled here
by the measured bound (one pass of each suffices for the shipped Python's inputs
because `dropOrphansAux` is applied last). -/
def dropDangling : List SMsg → List SMsg
  | [] => []
  | m :: ms =>
      if m.role = Role.assistant && !m.callIds.isEmpty then
        if m.callIds.all (fun cid => ms.any (fun r =>
             r.role = Role.tool && r.resultId = some cid))
        then m :: dropDangling ms
        else dropDangling ms
      else m :: dropDangling ms

def validateToolPairsV4 (s : Secret) (msgs : List SMsg) : List SMsg :=
  let head := sysPrefixLen msgs
  let sys := msgs.take head
  let body := msgs.drop head
  let vf := validFrom body
  let kept := (body.take vf).filter (rescuableFixed s) ++ body.drop vf
  sys ++ dropOrphansAux (dropDangling kept) []

/-- **[LOAD-BEARING]** `dropDangling` only ever removes ASSISTANT messages, so a
tool result present in the input is present in the output. This is what makes the
dangling test stable under the pass: the witnesses it relies on cannot vanish.

Mutation that breaks it: make `dropDangling` drop tool messages too. -/
theorem dropDangling_preserves_tool (r : SMsg) (hr : r.role = Role.tool) :
    ∀ l : List SMsg, r ∈ l → r ∈ dropDangling l := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons b bs ih =>
    intro h
    have hnotr : (r.role = Role.assistant && !r.callIds.isEmpty) = false := by
      simp [hr]
    rcases List.mem_cons.mp h with hb | hb
    · subst hb
      simp [dropDangling, hnotr]
    · by_cases hba : (b.role = Role.assistant && !b.callIds.isEmpty) = true
      · by_cases hbc : (b.callIds.all (fun cid => bs.any (fun x =>
            x.role = Role.tool && x.resultId = some cid))) = true
        · simp [dropDangling, hba, hbc]
          exact Or.inr (ih hb)
        · simp [dropDangling, hba, hbc]
          exact ih hb
      · simp [dropDangling, hba]
        exact Or.inr (ih hb)

/-- **[LOAD-BEARING]** `dropDangling` really does discharge the dangling-call
direction, for every input and independent of the orphan pass.

Mutation that breaks it: replace the `callIds.all …` test with `true`, or drop
the recursive call. -/
theorem dropDangling_danglingFree (l : List SMsg) :
    danglingFree (dropDangling l) = true := by
  simp only [danglingFree]
  induction l with
  | nil => rfl
  | cons a as ih =>
    by_cases h : (a.role = Role.assistant && !a.callIds.isEmpty) = true
    · by_cases hall : (a.callIds.all (fun cid => as.any (fun x =>
          x.role = Role.tool && x.resultId = some cid))) = true
      · have hsub : (a.callIds.all (fun cid => (dropDangling as).any (fun x =>
            x.role = Role.tool && x.resultId = some cid))) = true := by
          refine List.all_eq_true.mpr ?_
          intro cid hcid
          have hc := List.all_eq_true.mp hall cid hcid
          obtain ⟨r, hrmem, hrp⟩ := List.any_eq_true.mp hc
          have hrtool : r.role = Role.tool := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hrp
            exact hrp.1
          exact List.any_eq_true.mpr
            ⟨r, dropDangling_preserves_tool r hrtool as hrmem, hrp⟩
        simp only [dropDangling, h, if_pos, hall, danglingFreeAux, hsub,
          Bool.true_and]
        exact ih
      · simp only [dropDangling, h, hall, if_pos, if_neg, Bool.false_eq_true,
          not_false_eq_true]
        exact ih
    · have h' : (a.role = Role.assistant && !a.callIds.isEmpty) = false := by
        simpa using h
      simp only [dropDangling, h', Bool.false_eq_true, if_false, danglingFreeAux]
      exact ih

/-- **[LOAD-BEARING]** the landed sanitizer is orphan-free for EVERY input,
including the `validFrom = 0` branch the shipped one skipped.

Mutation that breaks it: reintroduce the `if vf = 0 then sys ++ body` arm, or
delete the `dropOrphansAux` pass. -/
theorem v4_validate_orphanFree (s : Secret) (msgs : List SMsg) :
    orphanFree (validateToolPairsV4 s msgs) = true := by
  unfold orphanFree validateToolPairsV4
  rw [orphanFreeAux_system_prefix _ (mem_take_sysPrefixLen msgs)]
  exact dropOrphansAux_orphanFree _ []

/-- **[LOAD-BEARING]** the repair is not "delete everything": the dangling-call
counterexample loses exactly the broken assistant and keeps the rest. -/
theorem v4_keeps_content :
    (validateToolPairsV4 "S" atkDanglingCall).length = 2
      ∧ (validateToolPairsV4 "S" atkAckToolResult).length = 2 := by
  constructor <;> rfl

/-! ### An obligation this file does NOT discharge

`danglingFree (validateToolPairsV4 s msgs) = true` is **not proved here**, and it
is not proved because the composition, not either pass, is what carries it:
`dropOrphansAux` runs after `dropDangling` and removes tool results, which is
exactly the operation that can strand an assistant that `dropDangling` had just
accepted. The informal argument is that `dropOrphansAux` never removes an
assistant and never removes a result whose call precedes it, so a result a KEPT
assistant depends on is always retained — but that is an argument, and this file's
whole discipline is that an argument is not a proof.

What IS established: `dropDangling_danglingFree` for the pass, `v4_validate_orphanFree`
for the composition, and the executed `#guard`s below for the measured
counterexamples. The Python landed this round iterates BOTH passes to a fixpoint,
which is strictly stronger than what is modelled here; 137,256 exhaustive inputs
agreed with it. Treat the general composition claim as MEASURED, not PROVED. -/

-- Executed, not asserted. The shipped function's two failures, and the repair.
#guard danglingFree atkDanglingCall = false
#guard danglingFree (validateToolPairsShipped (fun l => l) "S" atkDanglingCall) = false
#guard validateToolPairsShipped (fun l => l) "S" atkDanglingCall = atkDanglingCall
#guard danglingFree (validateToolPairsV4 "S" atkDanglingCall) = true
#guard orphanFree (validateToolPairsV4 "S" atkDanglingCall) = true
#guard orphanFree (validateToolPairsV4 "S" atkAckToolResult) = true
#guard danglingFree (validateToolPairsV4 "S" atkAckToolResult) = true
#guard orphanFree (validateToolPairsV4 "S" atkDroppedCall) = true
#guard danglingFree (validateToolPairsV4 "S" atkDroppedCall) = true
-- and the predicate is not vacuous: it rejects something and accepts something
#guard danglingFree [{ role := Role.assistant, callIds := ["z"] }] = false
#guard danglingFree ([{ role := Role.assistant, callIds := ["z"] },
                      { role := Role.tool, resultId := some "z" }]) = true

#print axioms v4_validate_orphanFree
#print axioms dropDangling_danglingFree
#print axioms dropDangling_preserves_tool
#print axioms shipped_early_return_defeats_any_sweep
#print axioms shipped_dangling_is_stable
#print axioms v4_keeps_content


/-! ## 12. Review 6 — the drop invariant, the decline chain, and reachability

Three claims this file did not previously make. Each exists because a *runtime*
claim and a *proved* claim had drifted apart, and the gap was invisible.

### Why `monotone_shrink` was not enough

`monotone_shrink` proves `countChars (rebuild ...) < countChars c`. But `rebuild`
is **not** what goes on the wire. `vibe-rc-server.py:1137-1140` builds

    merged = current_messages[:sys_head] ++ result.prefix ++ current_messages[tail:]
    merged = _validate_tool_pairs(merged)

and forwards *that*. `_validate_tool_pairs` runs **after** every size argument in
this file, and it is a transform the model did not describe at all. So the proved
shrink covered an object one function short of the wire, and "compression
succeeded" (the proxy logged it, `/health` counted it) and "the payload actually
got smaller" were two different claims with only the first checked.

`forwarded_shrinks` closes that gap — but only under a hypothesis, and the
hypothesis is the real result. -/

/-- Characters are monotone under sublisting: dropping messages never adds
characters. Holds for *any* assignment of `chars`, so it says nothing about which
messages are dropped — only that dropping is not creating. -/
theorem countChars_le_of_sublist {a b : Conv} (h : a.Sublist b) :
    countChars a ≤ countChars b := by
  unfold countChars
  induction h with
  | slnil => simp
  | cons m _ ih => simp; omega
  | cons_cons m _ ih => simp; omega

/-- **[LOAD-BEARING] the drop invariant, over the object actually forwarded.**

If a step succeeds and the post-rebuild sanitizer only ever *drops* messages,
then the forwarded conversation is strictly smaller than the one it replaced.

The hypothesis `hsan` is the whole point. `_validate_tool_pairs` satisfies it
today only because its rescue re-attaches a **subset** of what it dropped
(`rescued = [m for m in dropped if _rescue_eligible(m)]`). It is entirely
plausible to "fix" an orphaned tool call by *synthesising* a placeholder tool
result instead — a natural repair, and one that would break this hypothesis
silently while every existing theorem in this file stayed green, because none of
them mention the sanitizer.

So this theorem is also a standing obligation on that function: **the sanitizer
must never manufacture content.** If it ever does, the runtime guard
`merged_chars < msg_chars` (`vibe-rc-server.py:1142`) is the only thing left
standing between that and a forwarded payload that grew.

**What `san` is, and what its hypothesis is worth.** `san` models exactly one
function — `_validate_tool_pairs` (`vibe-rc-server.py:1140`), applied to the
already-rebuilt list. It does NOT model the whole forward path: the summary and
ack are new messages and are emphatically not a sublist of the input, but they
enter inside `rebuild`, which `monotone_shrink` already covers. The composition
is therefore `rebuild` (adds a bounded prefix, proved shrinking) followed by
`san` (drops only, hypothesis below).

`(san c').Sublist c'` is **MEASURED of the Python, never PROVED**: exhaustive
over every message sequence up to length 5 across 8 message shapes — 37,449
inputs, zero non-subsequences, zero growth. The check is executed on every drift
run (`check-compressor-drift.py`, R6-4), so the hypothesis is bound to the code
rather than assumed about it. Treat the end-to-end shrink claim as PROVED
modulo a MEASURED hypothesis, which is weaker than proved and stronger than
asserted — and say so rather than rounding it up.

**REVIEW-6 WEAKENING, and it was found by an instrument no mutation can supply.**
This hypothesis used to read `∀ x : Conv, (san x).Sublist x` — the sanitizer
drops-only on EVERY conversation. Mutation testing cannot detect an unnecessary
hypothesis (breaking the model still kills the theorem either way), so the
audit was hypothesis WEAKENING: restate with the assumption removed and see
whether it still builds. It did. The proof applies
`countChars_le_of_sublist` at exactly one point, `c'`, so the universal
quantifier was decoration.

That is not cosmetic — it shrinks what R6-4 has to measure. The obligation is
now "`_validate_tool_pairs` drops-only on the conversations `rebuild` actually
produces", not "on every conversation expressible in the type". The 37,449-input
sweep over-satisfies the real obligation, which is the right direction for an
empirical hypothesis to err. Weaker hypothesis, same conclusion, stronger
theorem.

(The same audit found `decline_chain_unbounded`'s `hstuck` is genuinely
load-bearing: dropping it fails to build, because `clientRounds` unfolds through
`g (run p c)` and nothing bounds `run p c` without it.)

Mutation that breaks it: make the rescue synthesise a replacement message rather
than re-attach an existing one; or drop the `merged_chars < msg_chars` guard,
which is the runtime twin of `hsan`. -/
theorem forwarded_shrinks (p : Policy) (san : Conv → Conv)
    (c c' : Conv) (hsan : (san c').Sublist c')
    (h : stepE p c = .ok c') :
    countChars (san c') < countChars c := by
  have h1 := countChars_le_of_sublist hsan
  have h2 := monotone_shrink p c c' h
  omega

-- Self-contained witness. Deliberately NOT `case_plain`: that lives inside the
-- generated CORPUS block, and a counterexample whose meaning depends on
-- regenerated data is a counterexample that can be edited away by accident.
def r6_case : Conv :=
  [sys 3000, usr 1000, ast 2000, usr 1500, ast 2500, usr 1200, ast 1800, usr 900, ast 1100]
def r6_pol : Policy := mkP 1 2 812 160

/-- **[LOAD-BEARING] the hypothesis of `forwarded_shrinks` is not decoration.**

Without `hsan` the conclusion is false: here is a successful step and a sanitizer
under which the forwarded conversation is *no smaller* than the original. The
witness inflates rather than drops (`x ++ x`), which is exactly the shape a
"synthesise the missing half of the tool pair" repair would take.

Measured: `countChars r6_case = 15,000`, the rebuild is `8,972`, and
`8,972 * 2 = 17,944 > 15,000`. So a sanitizer that merely duplicated its input
would turn a logged 40% saving into a 20% *increase*, with `compression_count`
incremented and `total_tokens_saved` credited either way — because both are
incremented inside `compress_ex` (`compressor.py:1370-1382`), before the server
ever evaluates whether the merged payload was an improvement. -/
theorem forwarded_shrink_needs_drops_only :
    ∃ (p : Policy) (c c' : Conv) (san : Conv → Conv),
      stepE p c = .ok c' ∧ countChars c ≤ countChars (san c') := by
  refine ⟨r6_pol, r6_case, rebuild r6_pol r6_case (cutOf r6_pol r6_case),
          (fun x => x ++ x), rfl, by decide⟩

/-! ### D-F, stated as a specification rather than an anecdote

The measured decline chain `24,261 -> 25,300 -> 27,828` with the trigger firing
every round is not a curiosity: it is the shape of an unbounded-growth property.
`run_fixpoint` already says a declined step is a fixpoint. Compose that with a
client that keeps talking and the conclusion is that nothing bounds the context.

`clientRounds` is one round of the real loop: the proxy gets its chance (`run`),
then the client appends its next turn (`g`). -/
def clientRounds (p : Policy) (g : Conv → Conv) : Nat → Conv → Conv
  | 0, c => c
  | n + 1, c => clientRounds p g n (g (run p c))

/-- **[INFRASTRUCTURE] D-F, as a theorem.** Measured, not claimed: this theorem
and its corollary **survived all 66 mutations**. That is not a compliment. It
quantifies over `hstuck` and `hgrow` as *hypotheses* rather than over the
compressor's own definitions, so no mutation of `stepE`, `rebuild`, `maxIdx` or
`countChars` can falsify it. It is a true statement about arithmetic that names
the D-F failure mode precisely; it is **not** evidence that this codebase avoids
that failure mode. Do not cite it as a guarantee about the proxy.

What would make it load-bearing is a proof that `hstuck` is *unreachable* for the
real policy — i.e. that the proxy cannot get permanently stuck. That is NOT
proved here and, given `summaryChars` is an arbitrary function (the model may
return anything), it is false in general: `pin_saturation_refuses` exhibits
conversations where every summary fails to shrink.

If the proxy can never compress (`hstuck`: every round is a fixpoint) and the
client adds at least one character per round (`hgrow`), then context grows
without bound — at least one character per round, forever.

The contrapositive is the specification worth having: **for the context to stay
bounded, some round must actually compress.** A proxy that declines correctly is
still a proxy that is not helping, and "declined correctly" is not a success
state — it is the precondition of this theorem.

Note what is NOT assumed: nothing about summary quality, nothing about the
summarizer, and `g` is arbitrary. The only assumptions are that the proxy is
stuck and the conversation is still moving. -/
theorem decline_chain_unbounded (p : Policy) (g : Conv → Conv)
    (hstuck : ∀ x : Conv, run p x = x)
    (hgrow : ∀ x : Conv, countChars x < countChars (g x)) :
    ∀ (n : Nat) (c : Conv), countChars c + n ≤ countChars (clientRounds p g n c) := by
  intro n
  induction n with
  | zero => intro c; simp [clientRounds]
  | succ k ih =>
    intro c
    have hs := hstuck c
    have hg := hgrow c
    have := ih (g (run p c))
    rw [hs] at this
    simp only [clientRounds, hs]
    omega

/-- The same fact in the form that names the failure: no bound survives. -/
theorem decline_chain_exceeds_any_bound (p : Policy) (g : Conv → Conv)
    (hstuck : ∀ x : Conv, run p x = x)
    (hgrow : ∀ x : Conv, countChars x < countChars (g x)) (c : Conv) (B : Nat) :
    ∃ n, B < countChars (clientRounds p g n c) := by
  refine ⟨B + 1, ?_⟩
  have := decline_chain_unbounded p g hstuck hgrow (B + 1) c
  omega

/-! ### Reachability — which conversations can compress at all

Anomaly (a) of review 6: three 8-agent runs compressed zero times while a subagent
made 15 requests. The structural half of the answer is decidable and proved here.
The *token-trigger* half is NOT modelled: the trigger lives in the server
(`est_tokens > TRIGGER_TOKENS`) and is measured, never proved. Compression fires
only when BOTH hold, so this theorem is a necessary condition, not the whole
story — see the report's anomaly (a) for the measured half. -/
def canCompress (p : Policy) (c : Conv) : Bool :=
  match stepE p c with | .ok _ => true | .error _ => false

/-- **[LOAD-BEARING] the structural floor.** `max_idx = len - 4` pins the last
four messages, so a conversation of four messages or fewer has no compressible
span at all — for *every* policy, at any trigger, however large those four
messages are. A subagent that answers in a handful of turns is therefore
unreachable by compression on shape alone.

Mutation that breaks it: change `max_idx` from `len - 4` to `len`. -/
theorem short_conv_never_compresses (p : Policy) (c : Conv) (h : c.length ≤ 4) :
    stepE p c = .error .nothingToCompress := by
  have h1 : cutOf p c ≤ startIdx c := by
    have hle := safeCut_le c (startIdx c) (findKeepIndex c p.keepNum p.keepDen)
    have hfk := findKeepIndex_le c p.keepNum p.keepDen
    have hsh := systemHead_le_startIdx c
    unfold maxIdx at hfk
    unfold cutOf
    omega
  unfold stepE
  rw [if_pos h1]

theorem short_conv_cannot_compress (p : Policy) (c : Conv) (h : c.length ≤ 4) :
    canCompress p c = false := by
  unfold canCompress
  rw [short_conv_never_compresses p c h]

-- Executed, not asserted. Note the third: four messages of 9,000 chars each is
-- 36,000 characters — far past any trigger — and still cannot compress. Size is
-- not what makes a conversation compressible; shape is.
#guard canCompress r6_pol r6_case = true
#guard canCompress r6_pol ([sys 100, usr 100, ast 100, usr 100] : Conv) = false
#guard canCompress r6_pol ([usr 9000, ast 9000, usr 9000, ast 9000] : Conv) = false
-- and the numbers behind that third case are real
#guard countChars ([usr 9000, ast 9000, usr 9000, ast 9000] : Conv) = 36000

#print axioms countChars_le_of_sublist
#print axioms forwarded_shrinks
#print axioms forwarded_shrink_needs_drops_only
#print axioms decline_chain_unbounded
#print axioms decline_chain_exceeds_any_bound
#print axioms short_conv_never_compresses
#print axioms short_conv_cannot_compress

/-! ### Grounding the decline chain in the real policy

`decline_chain_unbounded` is quantified over an abstract `p` whose behaviour is
supplied entirely by `hstuck`, which is why it survived all 66 mutations: no
mutation of a concrete definition can reach it. That makes the arithmetic honest
and the *relevance* unproven.

What follows removes the hypothesis at a point. `hstuck` is not merely
satisfiable in principle — the REAL `stepE`, on a conversation this proxy can
actually receive, declines by computation. Every fact below is `rfl` or `decide`
against the shipped definitions, so mutating the pin-saturation guard, the cut,
or the eligibility rule breaks these and not just the corpus. -/

/-- Every character of the compressible span is inside an eligible pin. This is
the `pinBudget` state, and it is **scale-free**: it does not depend on the
conversation being small, so no trigger threshold rescues it. -/
def r6_stuck : Conv :=
  [sys 1000, usrPin 9000, usrPin 8000, usr 500, ast 600, usr 700, ast 800]
def r6_stuck_pol : Policy := mkP 1 2 372 160

/-- **[LOAD-BEARING] the stuck state is reachable by the shipped policy.**
Not a hypothesis: `stepE` computes to `pinBudget` here. -/
theorem real_stepE_can_decline :
    stepE r6_stuck_pol r6_stuck = .error .pinBudget := by rfl

/-- The span really is fully pinned — the decline is the pin budget, not an
accident of the cut landing somewhere degenerate. -/
theorem real_stuck_is_pin_saturated :
    spanChars r6_stuck (cutOf r6_stuck_pol r6_stuck) = 17000
      ∧ pinChars r6_stuck (cutOf r6_stuck_pol r6_stuck) = 17000 := by
  refine ⟨rfl, rfl⟩

/-- **[LOAD-BEARING]** and therefore `run` is a fixpoint here BY COMPUTATION,
discharging `decline_chain_unbounded`'s `hstuck` at a real point rather than
assuming it. -/
theorem real_run_is_stuck : run r6_stuck_pol r6_stuck = r6_stuck :=
  run_error _ _ _ real_stepE_can_decline

/-- **[LOAD-BEARING] D-F, grounded.** From the real stuck state, one round of a
client that keeps talking strictly increases the context, with the proxy given
its chance and declining. This is the measured chain
`24,261 -> 25,300 -> 27,828` as a theorem about *this* compressor: the growth is
not the proxy failing to run, it is the proxy running and correctly refusing.

Note the honest scope: this says the shipped policy CAN enter a declining state
and that growth follows from it. It does NOT say the policy always declines —
that is false, and `forwarded_shrinks` is the case where it does not. -/
theorem stuck_round_grows (g : Conv → Conv)
    (hgrow : ∀ x : Conv, countChars x < countChars (g x)) :
    countChars r6_stuck < countChars (g (run r6_stuck_pol r6_stuck)) := by
  rw [real_run_is_stuck]
  exact hgrow _

#guard countChars r6_stuck = 20600
#guard (r6_stuck.filter effectivePinned).length = 2

#print axioms real_stepE_can_decline
#print axioms real_stuck_is_pin_saturated
#print axioms real_run_is_stuck
#print axioms stuck_round_grows


/-! ## REVIEW-6, section 12: the four `_safe_cut` disjuncts are independent

The Python side established by MUTATION that the pre-existing corpus detected
only **1 of 4** disjuncts, and that the culprit was masking: in a well-formed
transcript every `astCall` is immediately followed by its `toolRes`, so D4
rejects the boundary before D1 is ever consulted. That was a measurement over a
finite corpus. Below it is kernel-checked.
-/

/-- `badCut` with one disjunct deleted: `d = 1` drops `hasToolCalls` at
`cut - 1`, `2` drops `system` at `cut - 1`, `3` drops `system` at `cut`,
`4` drops `tool` at `cut`. `d = 0` deletes nothing. -/
def badCutNo (d : Nat) (c : Conv) (cut : Nat) : Bool :=
  let pre := match c[cut - 1]? with
    | some m => (if d == 1 then false else m.hasToolCalls)
                  || (if d == 2 then false else m.role == Role.system)
    | none => false
  let tl := match c[cut]? with
    | some m => (if d == 3 then false else m.role == Role.system)
                  || (if d == 4 then false else m.role == Role.tool)
    | none => false
  pre || tl

/-- **[LOAD-BEARING] the mutant family agrees with the original when it deletes
nothing.** Without this, every independence result below could be an artifact of
a mis-transcribed predicate rather than of the disjunct that was removed. -/
theorem badCutNo_zero (c : Conv) (cut : Nat) : badCutNo 0 c cut = badCut c cut := by
  unfold badCutNo badCut prefixEndsBad tailStartsBad
  cases c[cut - 1]? <;> cases c[cut]? <;> simp

/-- The `_safe_cut` walk, parameterised by its guard. -/
def safeCutAuxG (bad : Conv → Nat → Bool) (c : Conv) (floor : Nat) : Nat → Nat → Nat
  | 0, cut => max cut floor
  | fuel + 1, cut =>
      if floor < cut ∧ bad c cut = true then safeCutAuxG bad c floor fuel (cut - 1)
      else max cut floor

def safeCutG (bad : Conv → Nat → Bool) (c : Conv) (cut floor : Nat) : Nat :=
  safeCutAuxG bad c floor cut cut

theorem safeCutAuxG_badCut (c : Conv) (floor : Nat) : ∀ fuel cut,
    safeCutAuxG badCut c floor fuel cut = safeCutAux c floor fuel cut := by
  intro fuel
  induction fuel with
  | zero => intro cut; rfl
  | succ n ih => intro cut; simp only [safeCutAuxG, safeCutAux, ih]

/-- **[LOAD-BEARING] the parameterised walk instantiated at `badCut` IS
`safeCut`.** This is the bridge. Without it the independence theorems would be
true of some other function that merely looks like the one the port runs. -/
theorem safeCutG_badCut (c : Conv) (cut floor : Nat) :
    safeCutG badCut c cut floor = safeCut c cut floor :=
  safeCutAuxG_badCut c floor cut cut

/-- Witness for D1: an assistant turn carrying tool calls sits at `cut - 1` and
NOTHING follows it that D4 would catch — a **dangling call**, what an interrupted
or errored turn leaves behind. -/
def wD1 : Conv := [usr 100, usr 100, usr 100, usr 100, astCall 100, usr 100]
def wD2 : Conv := [usr 100, sys 100, usr 100]
def wD3 : Conv := [usr 100, usr 100, sys 100]
def wD4 : Conv := [usr 100, usr 100, toolRes 100]

/-- **[LOAD-BEARING] each disjunct is independently necessary, at the
predicate.** For each `d`, a conversation where `badCut` fires and the mutant
missing `d` does not. -/
theorem disjuncts_predicate_independent :
    (badCut wD1 5 = true ∧ badCutNo 1 wD1 5 = false) ∧
    (badCut wD2 2 = true ∧ badCutNo 2 wD2 2 = false) ∧
    (badCut wD3 2 = true ∧ badCutNo 3 wD3 2 = false) ∧
    (badCut wD4 2 = true ∧ badCutNo 4 wD4 2 = false) := by decide

/-- **[LOAD-BEARING] each disjunct is independently necessary, at the WALK.**
Stronger and the one that matters: deleting any single disjunct changes the cut
`_safe_cut` RETURNS, not merely the value of an internal predicate. Kernel-checked
counterpart of the Python mutation matrix. -/
theorem disjuncts_walk_independent :
    safeCutG badCut wD1 5 0 ≠ safeCutG (badCutNo 1) wD1 5 0 ∧
    safeCutG badCut wD2 2 0 ≠ safeCutG (badCutNo 2) wD2 2 0 ∧
    safeCutG badCut wD3 2 0 ≠ safeCutG (badCutNo 3) wD3 2 0 ∧
    safeCutG badCut wD4 2 0 ≠ safeCutG (badCutNo 4) wD4 2 0 := by decide

/-- A well-formed transcript: every `astCall` immediately followed by its
`toolRes`. -/
def wMasked : Conv := [usr 100, usr 100, astCall 100, toolRes 100, usr 100]

/-- **[LOAD-BEARING] D1 is MASKED BY D4 on well-formed traffic — proved, not
measured.** Deleting D1 changes nothing here, because D4 rejects the boundary
first. This is the whole explanation for why a corpus built from realistic
transcripts scored 1 of 4 while looking like it covered the guard, and why
`dangling_call` — a shape that never occurs in a clean run — was required to
discriminate D1 at all. -/
theorem d1_masked_by_d4_on_wellformed :
    safeCutG badCut wMasked 3 0 = safeCutG (badCutNo 1) wMasked 3 0 := by decide
