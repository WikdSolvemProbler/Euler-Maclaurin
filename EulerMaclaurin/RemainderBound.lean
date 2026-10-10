/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import EulerMaclaurin.BernoulliBounds
public import EulerMaclaurin.Formula

/-!
# Bounds for the remainder of the Euler-Maclaurin formula

The remainder `EulerMaclaurin.remainder p g a b = (-1)^(p + 1) / p! • ∫_a^b P_p • g` of the
Euler-Maclaurin formula is bounded in terms of `∫_a^b ‖g‖` and a bound on the periodic Bernoulli
function `P_p`.  With the explicit bounds of `EulerMaclaurin.BernoulliBounds` this gives, for an
interval integrable function `g` valued in a real normed space and `a ≤ b`,

* `‖remainder 1 g a b‖ ≤ 1 / 2 * ∫_a^b ‖g‖`,
* `‖remainder p g a b‖ ≤ 2 ζ(p) / (2 π)^p * ∫_a^b ‖g‖` for `p ≥ 2`,
* `‖remainder p g a b‖ ≤ 4 / 6^p * ∫_a^b ‖g‖` for `p ≥ 2`, a rational constant,

and, if `‖g‖ ≤ M` on `[a, b]`, `‖remainder p g a b‖ ≤ 4 / 6^p * (M * (b - a))`.  For even `p` the
constant `2 ζ(p) / (2 π)^p` equals `|B_p| / p!`, where `|B_p|` is the supremum of
`|bernoulliFun p|` on `[0, 1]`, so no better constant is possible from the size of `P_p` alone.

This file is meant for Mathlib as part of `Mathlib/NumberTheory/EulerMaclaurin.lean`, or as a
sibling file `Mathlib/NumberTheory/EulerMaclaurin/RemainderBound.lean` if the import weight of the
zeta function is a concern there.

## Main results

* `EulerMaclaurin.norm_remainder_le_of_forall_abs_bernoulliFun_le`: the remainder is bounded by
  any uniform bound for `bernoulliFun p` on `[0, 1]`.
* `EulerMaclaurin.norm_remainder_one_le`, `EulerMaclaurin.norm_remainder_le`,
  `EulerMaclaurin.norm_remainder_le_four_div_six_pow`: the three bounds above.
* `EulerMaclaurin.norm_remainder_le_of_norm_le`: the bound for a function bounded by a constant.

## Tags

Euler-Maclaurin formula, remainder estimate, Bernoulli polynomial
-/

public section

open MeasureTheory

open scoped Nat Real

namespace EulerMaclaurin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℝ → E} {a b : ℝ}

/-- **The generic bound for the remainder.**  If `|B_p(x)| ≤ D` for `x ∈ [0, 1]`, then
`‖remainder p g a b‖ ≤ D / p! * ∫ t in a..b, ‖g t‖` for `a ≤ b` and `g` interval integrable.
Only interval integrability of `g` is used, not that of the product with the periodic Bernoulli
function. -/
theorem norm_remainder_le_of_forall_abs_bernoulliFun_le {p : ℕ} {D : ℝ} (hab : a ≤ b)
    (hD : ∀ x ∈ Set.Icc (0 : ℝ) 1, |bernoulliFun p x| ≤ D) (hg : IntervalIntegrable g volume a b) :
    ‖remainder p g a b‖ ≤ D / p ! * ∫ t in a..b, ‖g t‖ := by
  have hint : ‖∫ t in a..b, periodicBernoulli p t • g t‖ ≤ ∫ t in a..b, D * ‖g t‖ :=
    intervalIntegral.norm_integral_le_of_norm_le hab (ae_of_all _ fun t _ ↦ by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hD _ ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩)
        (norm_nonneg _)) (hg.norm.const_mul D)
  rw [intervalIntegral.integral_const_mul] at hint
  rw [remainder, norm_smul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_natCast]
  exact (mul_le_mul_of_nonneg_left hint (by positivity)).trans_eq (by ring)

/-- The remainder of order `1` is bounded with the exact constant `1 / 2`: the periodic Bernoulli
function `Int.fract x - 1 / 2` of order `1` has supremum norm `1 / 2`. -/
theorem norm_remainder_one_le (hab : a ≤ b) (hg : IntervalIntegrable g volume a b) :
    ‖remainder 1 g a b‖ ≤ 1 / 2 * ∫ t in a..b, ‖g t‖ := by
  have h := norm_remainder_le_of_forall_abs_bernoulliFun_le (p := 1) (D := 1 / 2) hab
    (fun x hx ↦ by
      rw [bernoulliFun_one, abs_le]
      constructor <;> linarith [hx.1, hx.2]) hg
  simpa using h

/-- **Bound for the remainder of order `p ≥ 2`.**  The factorial in the definition of the
remainder cancels the one in the bound for the Bernoulli polynomial, so the constant
`2 ζ(p) / (2 π)^p` decays geometrically in `p`. -/
theorem norm_remainder_le {p : ℕ} (hp : 2 ≤ p) (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) :
    ‖remainder p g a b‖ ≤ 2 * (riemannZeta p).re / (2 * π) ^ p * ∫ t in a..b, ‖g t‖ := by
  have h := norm_remainder_le_of_forall_abs_bernoulliFun_le hab
    (fun x hx ↦ abs_bernoulliFun_le hp hx) hg
  have hfac : ((p ! : ℕ) : ℝ) ≠ 0 := by positivity
  rwa [mul_div_right_comm, mul_div_cancel_right₀ _ hfac] at h

/-- **Rational bound for the remainder of order `p ≥ 2`.**  The constant `4 / 6^p` contains no
transcendental number, so the bound can be evaluated exactly. -/
theorem norm_remainder_le_four_div_six_pow {p : ℕ} (hp : 2 ≤ p) (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) :
    ‖remainder p g a b‖ ≤ 4 / 6 ^ p * ∫ t in a..b, ‖g t‖ := by
  have h := norm_remainder_le_of_forall_abs_bernoulliFun_le hab
    (fun x hx ↦ abs_bernoulliFun_le_four_mul_factorial_div_six_pow hp hx) hg
  have hfac : ((p ! : ℕ) : ℝ) ≠ 0 := by positivity
  rwa [mul_div_right_comm, mul_div_cancel_right₀ _ hfac] at h

/-- If `‖g‖ ≤ M` on `[a, b]` then the remainder of order `p ≥ 2` is at most
`4 / 6^p * (M * (b - a))`, an expression in the four parameters `p`, `M`, `a` and `b` with no
integral left to evaluate. -/
theorem norm_remainder_le_of_norm_le {p : ℕ} {M : ℝ} (hp : 2 ≤ p) (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (hM : ∀ t ∈ Set.Icc a b, ‖g t‖ ≤ M) :
    ‖remainder p g a b‖ ≤ 4 / 6 ^ p * (M * (b - a)) := by
  refine (norm_remainder_le_four_div_six_pow hp hab hg).trans
    (mul_le_mul_of_nonneg_left ?_ (by positivity))
  simpa [mul_comm] using intervalIntegral.integral_mono_on hab hg.norm intervalIntegrable_const hM

end EulerMaclaurin
