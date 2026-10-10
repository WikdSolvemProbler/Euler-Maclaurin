/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import EulerMaclaurin
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Examples for the Euler-Maclaurin formula

These examples check that the hypotheses of the theorems in `EulerMaclaurin` are satisfiable and
that the conclusions are nondegenerate:

* Faulhaber's formula for $\sum i^2$ is the case $p = 3$ of the formula for a family of
  derivatives, where the remainder vanishes.
* The formula of order $2$ for the exponential function on $[0, n]$, stated with the integral, the
  boundary terms and the remainder integral written out.
* The remainder integral of order $1$ of a constant function is a nonzero number.
* The remainder bounds and the bounds for the Bernoulli polynomials are concrete inequalities.
-/

public section

open EulerMaclaurin MeasureTheory

open scoped Nat

/-- The derivatives of `t ↦ t ^ 2`: `t ^ 2`, `2 * t`, `2` and then `0`. -/
@[expose] noncomputable def sqFamily : ℕ → ℝ → ℝ
  | 0 => fun t ↦ t ^ 2
  | 1 => fun t ↦ 2 * t
  | 2 => fun _ ↦ 2
  | _ + 3 => fun _ ↦ 0

theorem hasDerivAt_sqFamily {k : ℕ} (hk : k < 3) (x : ℝ) :
    HasDerivAt (sqFamily k) (sqFamily (k + 1) x) x := by
  interval_cases k
  · simpa [sqFamily] using hasDerivAt_pow 2 x
  · simpa [sqFamily] using (hasDerivAt_id x).const_mul (2 : ℝ)
  · simpa [sqFamily] using hasDerivAt_const x (2 : ℝ)

/-- **Faulhaber's formula** `∑_{i = 0}^{n} i ^ 2 = n ^ 3 / 3 + n ^ 2 / 2 + n / 6` is the formula
of order `3` for `t ↦ t ^ 2`, whose remainder integral is zero. -/
example (n : ℕ) :
    ∑ i ∈ Finset.Icc (0 : ℤ) n, (i : ℝ) ^ 2 = (n : ℝ) ^ 3 / 3 + (n : ℝ) ^ 2 / 2 + n / 6 := by
  have h := sum_Icc_eq_integral_add_of_hasDerivWithinAt (p := 3) (F := sqFamily) (a := 0)
    (b := n) (by norm_num) (Int.natCast_nonneg n)
    (fun k hk x _ ↦ (hasDerivAt_sqFamily hk x).hasDerivWithinAt)
    (by simp [sqFamily])
  have hrem : (∫ t in ((0 : ℤ) : ℝ)..((n : ℤ) : ℝ),
      periodizedBernoulli 3 t • sqFamily 3 t) = 0 := by
    simp [sqFamily]
  have hint : (∫ t in ((0 : ℤ) : ℝ)..((n : ℤ) : ℝ), sqFamily 0 t) = (n : ℝ) ^ 3 / 3 := by
    norm_num [sqFamily, integral_pow]
  have hsum : ∑ j ∈ Finset.range (3 / 2),
      (((bernoulli (2 * j + 2) : ℚ) : ℝ) / ((2 * j + 2)! : ℝ)) •
        (sqFamily (2 * j + 1) ((n : ℤ) : ℝ) - sqFamily (2 * j + 1) ((0 : ℤ) : ℝ)) =
      (n : ℝ) / 6 := by
    norm_num [Finset.sum_range_succ, bernoulli_two, Nat.factorial, sqFamily]
    ring
  rw [hrem, hint, hsum] at h
  simp only [sqFamily, smul_eq_mul] at h
  push_cast at h
  linarith

/-- The formula of order `2` for the exponential function on `[0, n]`, with the integral, the
boundary terms and the remainder integral written out.  Here `B_2 / 2! = 1 / 12`, the first
derivative of the exponential is itself, and the coefficient of the remainder is
`(-1) ^ 3 / 2! = -1 / 2`. -/
example (n : ℕ) (hn : 0 < n) :
    ∑ i ∈ Finset.Icc 0 n, Real.exp i =
      (Real.exp n - 1) + (1 + Real.exp n) / 2 + (Real.exp n - 1) / 12 +
        (-1 / 2) * ∫ t in (0 : ℝ)..n, periodizedBernoulli 2 t * Real.exp t := by
  have h := sum_Icc_nat_eq_integral_add (f := Real.exp) (p := 2) (a := 0) (b := n)
    (by norm_num) (Nat.zero_le n) Real.contDiff_exp.contDiffOn
  simp only [Nat.cast_zero] at h
  have hU : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) n) := uniqueDiffOn_Icc (by exact_mod_cast hn)
  have hder : ∀ (k : ℕ), ∀ x ∈ Set.Icc (0 : ℝ) n,
      iteratedDerivWithin k Real.exp (Set.Icc (0 : ℝ) n) x = Real.exp x := fun k x hx ↦ by
    rw [iteratedDerivWithin_eq_iteratedDeriv hU Real.contDiff_exp.contDiffAt hx,
      iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hint : (∫ t in (0 : ℝ)..n,
      periodizedBernoulli 2 t • iteratedDerivWithin 2 Real.exp (Set.Icc (0 : ℝ) n) t) =
      ∫ t in (0 : ℝ)..n, periodizedBernoulli 2 t * Real.exp t := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hn0] at ht
    simp only [smul_eq_mul, hder 2 t ht]
  have hsum : ∑ j ∈ Finset.range (2 / 2),
      (((bernoulli (2 * j + 2) : ℚ) : ℝ) / ((2 * j + 2)! : ℝ)) •
        (iteratedDerivWithin (2 * j + 1) Real.exp (Set.Icc (0 : ℝ) n) n -
          iteratedDerivWithin (2 * j + 1) Real.exp (Set.Icc (0 : ℝ) n) 0) =
      (Real.exp n - 1) / 12 := by
    have h2 : 2 / 2 = 1 := rfl
    rw [h2, Finset.sum_range_one]
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [hder 1 n ⟨hn0, le_rfl⟩, hder 1 0 ⟨le_rfl, hn0⟩]
    norm_num [bernoulli_two, Nat.factorial]
    ring
  have hc : ((-1 : ℝ) ^ (2 + 1) / (2 ! : ℝ)) = -1 / 2 := by norm_num [Nat.factorial]
  rw [hsum, hint, hc, integral_exp] at h
  simp only [Real.exp_zero, smul_eq_mul] at h
  linarith

/-- The remainder integral of order `1` of the constant function `1` on `[0, 1 / 2]` is `-1 / 8`,
so the remainder bounds are not statements about the zero vector. -/
example : ∫ t in (0 : ℝ)..(1 / 2), periodizedBernoulli 1 t • (1 : ℂ) = -(1 / 8) := by
  have hEq : ∀ t ∈ Set.uIcc (0 : ℝ) (1 / 2),
      periodizedBernoulli 1 t • (1 : ℂ) = ((t - 1 / 2 : ℝ) : ℂ) := fun t ht ↦ by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
    rw [Complex.real_smul, mul_one, periodizedBernoulli_coe, bernoulliFun_one,
      Int.fract_eq_self.2 ⟨ht.1, by linarith [ht.2]⟩]
  have hreal : (∫ t in (0 : ℝ)..(1 / 2), (t - 1 / 2)) = -(1 / 8) := by
    rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
      intervalIntegrable_const, integral_id]
    norm_num
  rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_ofReal, hreal]
  norm_num

/-- The rational bound for the remainder integral of order `2` on `[0, 1]` for the constant
function `1`: `4 * 2! / 6 ^ 2 = 2 / 9`. -/
example : ‖∫ t in (0 : ℝ)..1, periodizedBernoulli 2 t • (1 : ℂ)‖ ≤ 2 / 9 :=
  (norm_integral_periodizedBernoulli_smul_le_of_norm_le 2 (M := 1) zero_le_one
    intervalIntegrable_const fun _ _ ↦ by simp).trans_eq (by norm_num [Nat.factorial])

/-- The sharp bound in even order: for `g = 1` on `[0, 1]` the remainder integral of order `2` is
at most `|B_2| = 1 / 6`. -/
example : ‖∫ t in (0 : ℝ)..1, periodizedBernoulli (2 * 1) t • (1 : ℂ)‖ ≤ 1 / 6 :=
  (norm_integral_periodizedBernoulli_two_mul_smul_le 1 zero_le_one
    intervalIntegrable_const).trans_eq (by norm_num [bernoulli_two])

/-- The bound for the Bernoulli polynomials at `k = 2` and `x = 1 / 2`: `|B_2(1 / 2)| = 1 / 12`
is below `4 * 2! / 6 ^ 2 = 2 / 9`. -/
example : |bernoulliFun 2 (1 / 2 : ℝ)| ≤ 4 * (2 ! : ℝ) / 6 ^ 2 :=
  abs_bernoulliFun_le_four_mul_factorial_div_six_pow 2 ⟨by norm_num, by norm_num⟩

/-- The rational bound holds in degree `1` as well: `|B_1(0)| = 1 / 2 ≤ 4 * 1! / 6`. -/
example : |bernoulliFun 1 (0 : ℝ)| ≤ 4 * (1 ! : ℝ) / 6 ^ 1 :=
  abs_bernoulliFun_le_four_mul_factorial_div_six_pow 1 ⟨le_rfl, zero_le_one⟩

/-- The sharp bound in even degree is attained at `0`, so it cannot be improved. -/
example : |bernoulliFun (2 * 1) (0 : ℝ)| = |((bernoulli (2 * 1) : ℚ) : ℝ)| := by
  rw [bernoulliFun_eval_zero]

example : |bernoulliFun (2 * 1) (1 / 2 : ℝ)| ≤ |((bernoulli (2 * 1) : ℚ) : ℝ)| :=
  abs_bernoulliFun_two_mul_le_abs_bernoulli 1 ⟨by norm_num, by norm_num⟩
