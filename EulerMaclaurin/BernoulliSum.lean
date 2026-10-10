/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import Mathlib.NumberTheory.Bernoulli

/-!
# Sums with the Bernoulli numbers `bernoulli'`

The numbers `bernoulli' n = (-1) ^ n * bernoulli n` satisfy $B'_1 = 1/2$ and $B'_n = 0$ for odd
$n \ge 3$.  Hence in a sum
$$\sum_{k < p} \frac{B'_{k + 1}}{(k + 1)!} c_k$$
only the term $k = 0$ and the terms $k = 2 j + 1$ survive, and the coefficient of the latter is
$B_{2 j + 2} / (2 j + 2)!$.  This regrouping turns the boundary terms of the Euler-Maclaurin
formula at integer end points into the familiar sum over the even Bernoulli numbers.

## Main results

* `sum_range_bernoulli'_div_factorial_smul`: the regrouping, for a field $K$ of characteristic zero
  acting on a $K$-module.

## Tags

Bernoulli numbers, regrouping, odd Bernoulli numbers vanish
-/

public section

open scoped Nat

/-- Regrouping the coefficients `B'_{k+1} / (k + 1)!`, `k < p`, where `B'_n = bernoulli' n`:
since `B'_1 = 1 / 2` and `B'_n = 0` for odd `n ≥ 3`, only `k = 0`, with coefficient `1 / 2`, and the
odd values `k = 2 * j + 1` survive, with coefficient `B_{2 * j + 2} / (2 * j + 2)!`.  The hypothesis
`p ≠ 0` is needed for the term `k = 0`. -/
theorem sum_range_bernoulli'_div_factorial_smul {K G : Type*} [Field K] [CharZero K]
    [AddCommGroup G] [Module K G] {p : ℕ} (hp : p ≠ 0) (c : ℕ → G) :
    ∑ k ∈ Finset.range p, ((bernoulli' (k + 1) : K) / ((k + 1)! : K)) • c k =
      (1 / 2 : K) • c 0 + ∑ j ∈ Finset.range (p / 2),
        ((bernoulli (2 * j + 2) : K) / ((2 * j + 2)! : K)) • c (2 * j + 1) := by
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp
  induction p, hp1 using Nat.le_induction with
  | base =>
    norm_num [bernoulli'_one]
  | succ p hp ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' p
    · have hodd : bernoulli' (2 * r + 1) = 0 :=
        bernoulli'_eq_zero_of_odd ⟨r, rfl⟩ (by omega)
      have hdiv : (2 * r + 1) / 2 = 2 * r / 2 := by omega
      rw [hdiv]
      simp [hodd]
    · have h1 : (2 * r + 1 + 1) / 2 = r + 1 := by omega
      have h2 : (2 * r + 1) / 2 = r := by omega
      have h3 : 2 * r + 1 + 1 = 2 * r + 2 := rfl
      rw [h1, h2, Finset.sum_range_succ, h3,
        ← bernoulli_eq_bernoulli'_of_ne_one (by omega : 2 * r + 2 ≠ 1)]
      module
