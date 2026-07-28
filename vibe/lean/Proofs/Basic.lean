/-
Copyright (c) 2026 Saimono. All rights reserved.
SPDX-FileCopyrightText: 2026 Saimono / Nova-Violet Role
SPDX-License-Identifier: AGPL-3.0-or-later OR EUPL-1.2
See NOTICE.md at the repository root for the full licence map.
Authors: Saimono
-/
import Mathlib

/-! # Mathlib smoke test

Each theorem below needs something Lean core does not have: `Nat.Prime` lemmas,
the reals, the algebraic hierarchy. If this file builds, mathlib is usable.
-/

def hello := "world"

-- Infinitude of primes, straight from mathlib.
theorem infinitely_many_primes (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p :=
  Nat.exists_infinite_primes n

-- Real numbers exist and are ordered — core Lean has no `ℝ`.
theorem sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 := by
  positivity

-- Group theory: mathlib's algebraic hierarchy.
theorem inv_mul_cancel_left' {G : Type*} [Group G] (a b : G) : a⁻¹ * (a * b) = b := by
  group

-- Core tactics still available on the mathlib toolchain.
theorem grind_still_here (a b : ℕ) (h : a ≤ b) : a < b + 1 := by
  grind

-- Negative control, kept commented. Uncomment to re-confirm the oracle rejects:
-- the claim is false (x = -1 gives 1 = -1) and `positivity` is the wrong tactic.
-- theorem false_in_mathlib (x : ℝ) : Real.sqrt (x^2) = x := by
--   positivity
