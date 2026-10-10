/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ZetaValues

/-!
# Explicit bounds for the Bernoulli polynomials on `[0, 1]`

Remainder estimates in the Euler-Maclaurin formula need a bound on `sup_{x ∈ [0, 1]} |B_k(x)|`
with `B_k = bernoulliFun k` the Bernoulli polynomial.  Compactness gives some bound, but an
opaque one.  This file derives explicit constants from Mathlib's Fourier expansion of the
periodized Bernoulli polynomial (`hasSum_one_div_nat_pow_mul_fourier`): taking norms termwise in

  `B_k(x) = -k! / (2 π i)^k * ∑_{n ≠ 0} e(n x) / n^k`

gives, for `k ≥ 2` and `x ∈ [0, 1]`,

  `|B_k(x)| ≤ 2 ζ(k) * k! / (2 π)^k`.

Since `ζ(k) ≤ ζ(2) = π² / 6 < 2`, this yields the rational bound `|B_k(x)| ≤ 4 * k! / 6^k`.  For
even `k` the constant `2 ζ(k) * k! / (2 π)^k` equals `|B_k|`, so the bound there reads
`|B_{2m}(x)| ≤ |B_{2m}|` and is attained at `x = 0` (`bernoulliFun_eval_zero`).

This file is meant for Mathlib as an extension of `Mathlib/NumberTheory/ZetaValues.lean`, or as a
sibling file `Mathlib/NumberTheory/BernoulliBounds.lean` if the import weight of
`Mathlib.NumberTheory.LSeries.RiemannZeta` is a concern there.

## Main results

* `abs_bernoulliFun_le`: `|B_k(x)| ≤ 2 ζ(k) * k! / (2 π)^k` for `2 ≤ k` and `x ∈ [0, 1]`.
* `abs_bernoulliFun_le_four_mul_factorial_div_six_pow`: the rational bound `4 * k! / 6^k`.
* `abs_bernoulliFun_two_mul_le_abs_bernoulli`: the sharp bound `|B_{2m}(x)| ≤ |B_{2m}|`.

## Tags

Bernoulli polynomial, zeta function, Fourier series, explicit bound
-/

public section

open Complex

open scoped Nat Real

/-- For `k ≥ 2`, the real part of `ζ(k)` is the sum of the series `∑ 1 / n^k`. -/
private theorem hasSum_re_riemannZeta {k : ℕ} (hk : 2 ≤ k) :
    HasSum (fun n : ℕ ↦ 1 / (n : ℝ) ^ k) (riemannZeta k).re := by
  have hs := (Real.summable_one_div_nat_pow.mpr (by omega : 1 < k)).hasSum
  have h : riemannZeta k = ((∑' n : ℕ, 1 / (n : ℝ) ^ k : ℝ) : ℂ) := by
    rw [zeta_nat_eq_tsum_of_gt_one (by omega), Complex.ofReal_tsum]
    simp
  rwa [h, Complex.ofReal_re]

/-- The series `∑ 1 / n^k` is dominated by `ζ(2) = π² / 6` for `k ≥ 2`. -/
private theorem re_riemannZeta_le {k : ℕ} (hk : 2 ≤ k) : (riemannZeta k).re ≤ π ^ 2 / 6 := by
  refine hasSum_le (fun n ↦ ?_) (hasSum_re_riemannZeta hk) hasSum_zeta_two
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [zero_pow (show k ≠ 0 by omega)]
  · exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by exact_mod_cast hn) hk)

/-- **Explicit bound for the Bernoulli polynomials.**  For `k ≥ 2` and `x ∈ [0, 1]`,
`|B_k(x)| ≤ 2 ζ(k) * k! / (2 π)^k`.  The proof takes norms termwise in the Fourier expansion
`hasSum_one_div_nat_pow_mul_fourier`. -/
theorem abs_bernoulliFun_le {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun k x| ≤ 2 * (riemannZeta k).re * k ! / (2 * π) ^ k := by
  have hnorm : ‖-(2 * (π : ℂ) * I) ^ k / (k ! : ℂ) * (bernoulliFun k x : ℂ)‖ ≤
      2 * (riemannZeta k).re := by
    refine (hasSum_one_div_nat_pow_mul_fourier hk hx).norm_le_of_bounded
      ((hasSum_re_riemannZeta hk).mul_left 2) fun n ↦ ?_
    have hfourier : ∀ m : ℤ, ‖fourier m (x : UnitAddCircle)‖ = 1 := fun m ↦ Circle.norm_coe _
    have h1 : ‖fourier (n : ℤ) (x : UnitAddCircle) +
        (-1 : ℂ) ^ k * fourier (-(n : ℤ)) (x : UnitAddCircle)‖ ≤ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, hfourier, hfourier]
      norm_num
    have h2 : ‖(1 : ℂ) / (n : ℂ) ^ k‖ = 1 / (n : ℝ) ^ k := by simp [norm_pow]
    rw [norm_mul, h2, mul_comm 2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hval : ‖-(2 * (π : ℂ) * I) ^ k / (k ! : ℂ) * (bernoulliFun k x : ℂ)‖ =
      (2 * π) ^ k * |bernoulliFun k x| / k ! := by
    rw [norm_mul, norm_div, norm_neg, norm_pow,
      show ‖(2 * (π : ℂ) * I)‖ = 2 * π by simp [abs_of_pos Real.pi_pos],
      Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    ring
  rw [hval, div_le_iff₀ (by positivity)] at hnorm
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- **Rational bound for the Bernoulli polynomials.**  For `k ≥ 2` and `x ∈ [0, 1]`,
`|B_k(x)| ≤ 4 * k! / 6^k`.  No transcendental constant occurs, which is convenient for certified
numerical estimates.  It follows from `abs_bernoulliFun_le` since `2 ζ(k) ≤ π² / 3 < 4` and
`6 < 2 π`. -/
theorem abs_bernoulliFun_le_four_mul_factorial_div_six_pow {k : ℕ} (hk : 2 ≤ k) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : |bernoulliFun k x| ≤ 4 * k ! / 6 ^ k := by
  refine (abs_bernoulliFun_le hk hx).trans ?_
  have hπ : π ^ 2 < 12 :=
    calc π ^ 2 < 3.15 ^ 2 := pow_lt_pow_left₀ Real.pi_lt_d2 Real.pi_pos.le two_ne_zero
      _ < 12 := by norm_num
  have h2 : 2 * (riemannZeta k).re ≤ 4 := by linarith [re_riemannZeta_le hk]
  have h6 : (6 : ℝ) ^ k ≤ (2 * π) ^ k :=
    pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) k
  calc 2 * (riemannZeta k).re * k ! / (2 * π) ^ k ≤ 4 * k ! / (2 * π) ^ k := by gcongr
    _ ≤ 4 * k ! / 6 ^ k := by gcongr

/-- **Sharp bound in even degree.**  For every `m` and `x ∈ [0, 1]`,
`|B_{2m}(x)| ≤ |B_{2m}|`, where the right-hand side is the Bernoulli number.  The bound is attained
at `x = 0` (`bernoulliFun_eval_zero`).  It is `abs_bernoulliFun_le` together with the value of
`ζ(2m)` in terms of `B_{2m}`. -/
theorem abs_bernoulliFun_two_mul_le_abs_bernoulli (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun (2 * m) x| ≤ |(bernoulli (2 * m) : ℝ)| := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hk : 2 ≤ 2 * m := by omega
  refine (abs_bernoulliFun_le hk hx).trans ?_
  rw [(hasSum_re_riemannZeta hk).unique (hasSum_zeta_nat hm.ne')]
  have h2 : (2 : ℝ) ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h3 : (2 * π) ^ (2 * m) = 2 * 2 ^ (2 * m - 1) * π ^ (2 * m) := by rw [mul_pow, h2]
  have hπ : π ^ (2 * m) ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hfac : ((2 * m)! : ℝ) ≠ 0 := by positivity
  calc 2 * ((-1 : ℝ) ^ (m + 1) * 2 ^ (2 * m - 1) * π ^ (2 * m) * bernoulli (2 * m) /
        (2 * m)!) * (2 * m)! / (2 * π) ^ (2 * m)
      = (-1 : ℝ) ^ (m + 1) * bernoulli (2 * m) := by
        rw [h3]
        field_simp
    _ ≤ |(-1 : ℝ) ^ (m + 1) * bernoulli (2 * m)| := le_abs_self _
    _ = |(bernoulli (2 * m) : ℝ)| := by simp [abs_mul]
