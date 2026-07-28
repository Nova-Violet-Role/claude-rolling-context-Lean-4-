/-
Copyright (c) 2026 Saimono. All rights reserved.
Released under AGPL-3.0-or-later OR EUPL-1.2; see NOTICE at the repository root.
Authors: Saimono
-/
import Mathlib

/-! # Four theorems, argued rather than cited

Each result below is built from its own argument. Mathlib's *infrastructure* is used freely
(`Nat.Prime` API, `Rat` num/den, `Finset` sums, Lagrange's theorem for finite groups), but the
headline lemma that states the same thing is never invoked:

* `Nat.exists_infinite_primes` is **not** used — Euclid's construction is carried out.
* `irrational_sqrt_two` / `Nat.Prime.irrational_sqrt` are **not** used — infinite descent is run
  over the naturals and then transported to `ℝ`.
* `Finset.sum_range_id_mul_two` and friends are **not** used — plain induction.
* `ZMod.pow_card_sub_one_eq_one` is **not** used — Fermat is derived from Lagrange.
-/

/-! ## 1. Euclid: the primes are unbounded

Classic argument: any prime factor of `n! + 1` cannot be `≤ n`, because it would then divide `n!`
and hence divide `1`.
-/

theorem infinitude_primes : ∀ n : ℕ, ∃ p, n ≤ p ∧ Nat.Prime p := by
  intro n
  have hfac : 0 < Nat.factorial n := Nat.factorial_pos n
  have hne : Nat.factorial n + 1 ≠ 1 := by omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  refine ⟨p, ?_, hp⟩
  by_contra hlt
  have hlt' : p < n := Nat.not_le.mp hlt
  have h1 : p ∣ Nat.factorial n := Nat.dvd_factorial hp.pos hlt'.le
  have h2 : p ∣ 1 := (Nat.dvd_add_right h1).mp hpd
  exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

/-! ## 2. `√2` is irrational

The arithmetic core is proved first, by infinite descent on the numerator: no pair of naturals
with `n ≠ 0` satisfies `m² = 2n²`. Coprimality is never assumed — the descent supplies it.
-/

/-- Infinite descent: `m ^ 2 = 2 * n ^ 2` has no solution with `n ≠ 0`. -/
theorem no_nat_sqrt_two : ∀ m n : ℕ, n ≠ 0 → m ^ 2 ≠ 2 * n ^ 2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hn h
    -- `m ^ 2` is even, so `m` is even (this is where primality of 2 enters).
    have hm2 : 2 ∣ m ^ 2 := ⟨n ^ 2, h⟩
    have hm : 2 ∣ m := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hm2
    obtain ⟨k, rfl⟩ := hm
    -- `(2k)² = 2n²` gives `n² = 2k²`: the same equation, strictly smaller.
    have h4 : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by rw [← h]; ring
    have h2 : n ^ 2 = 2 * k ^ 2 := (Nat.eq_of_mul_eq_mul_left (by norm_num) h4).symm
    have hk : k ≠ 0 := by
      rintro rfl
      exact hn (by simpa using h2)
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hlt : n < 2 * k := by nlinarith [h2, hkpos]
    exact ih n hlt k hk h2

theorem sqrt_two_irrational : Irrational (Real.sqrt 2) := by
  rintro ⟨q, hq⟩
  have hq2 : (q : ℝ) ^ 2 = 2 := by
    rw [hq]
    exact Real.sq_sqrt (by norm_num)
  have hqq : q ^ 2 = 2 := by exact_mod_cast hq2
  have hdz : q.den ≠ 0 := (Rat.den_pos q).ne'
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast hdz
  have hnum : (q.num : ℚ) = q * (q.den : ℚ) := (div_eq_iff hd).mp (Rat.num_div_den q)
  have key : (q.num : ℚ) ^ 2 = 2 * (q.den : ℚ) ^ 2 := by
    rw [hnum, mul_pow, hqq]
  have keyZ : q.num ^ 2 = 2 * (q.den : ℤ) ^ 2 := by exact_mod_cast key
  have keyN : q.num.natAbs ^ 2 = 2 * q.den ^ 2 := by
    have h := congrArg Int.natAbs keyZ
    simpa [Int.natAbs_mul, Int.natAbs_pow] using h
  exact no_nat_sqrt_two _ _ hdz keyN

/-! ## 3. The first `n` odd numbers sum to `n²` -/

theorem sum_odds (n : ℕ) : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

/-! ## 4. Fermat's little theorem, from Lagrange

Chosen because it stresses a completely different part of mathlib from the three above: no
`Nat.Prime` divisibility juggling, no `Finset` induction, no reals. Instead it goes through the
*group* structure — `(ZMod p)ˣ` is a finite group of order `p - 1`, and Lagrange's theorem
(`pow_card_eq_one`) does the work. That is the classical proof: Fermat is a corollary of
Lagrange, not an independent fact. Deriving it this way exercises the `Fact`/instance machinery,
`ZMod` fields, `Units` coercions and `Nat.totient` — all untouched by theorems 1–3.
-/

theorem fermat_little {p : ℕ} [Fact (Nat.Prime p)] (a : ZMod p) (ha : a ≠ 0) :
    a ^ (p - 1) = 1 := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).pos.ne'⟩
  obtain ⟨u, rfl⟩ : IsUnit a := isUnit_iff_ne_zero.mpr ha
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : Nat.Prime p)]
  have hlag : u ^ Fintype.card (ZMod p)ˣ = 1 := pow_card_eq_one
  rw [hcard] at hlag
  have h2 : ((u ^ (p - 1) : (ZMod p)ˣ) : ZMod p) = ((1 : (ZMod p)ˣ) : ZMod p) := by rw [hlag]
  simpa using h2

/-- The `a ^ p = a` form, valid at `a = 0` too. -/
theorem fermat_little_pow {p : ℕ} [Fact (Nat.Prime p)] (a : ZMod p) : a ^ p = a := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hp : 0 < p := (Fact.out : Nat.Prime p).pos
    simp [zero_pow hp.ne']
  · have h := fermat_little a ha
    have hp : 1 ≤ p := (Fact.out : Nat.Prime p).one_lt.le
    calc a ^ p = a ^ (p - 1 + 1) := by rw [Nat.sub_add_cancel hp]
      _ = a ^ (p - 1) * a := by rw [pow_succ]
      _ = a := by rw [h, one_mul]

/-! ## Axiom audit -/

#print axioms infinitude_primes
#print axioms no_nat_sqrt_two
#print axioms sqrt_two_irrational
#print axioms sum_odds
#print axioms fermat_little
#print axioms fermat_little_pow
