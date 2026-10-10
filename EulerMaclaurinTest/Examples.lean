/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import EulerMaclaurin

/-!
# Examples for the Euler-Maclaurin formula

These examples check that the hypotheses of the theorems in `EulerMaclaurin` are satisfiable and
that the conclusions are nondegenerate:

* Faulhaber's formula for `∑ i ^ 2` is the case `p = 3` of the formula for a family of derivatives,
  where the remainder vanishes.
* The `C^p` version applies to the exponential function.
* The remainder of order `1` of a constant function is a nonzero number.
* The remainder bounds and the bound for the Bernoulli polynomials are concrete inequalities.
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
of order `3` for `t ↦ t ^ 2`, whose remainder is zero. -/
example (n : ℕ) :
    ∑ i ∈ Finset.Icc (0 : ℤ) n, (i : ℝ) ^ 2 = (n : ℝ) ^ 3 / 3 + (n : ℝ) ^ 2 / 2 + n / 6 := by
  have h := sum_Icc_eq_integral_add_of_hasDerivWithinAt (p := 3) (F := sqFamily) (a := 0)
    (b := n) (by norm_num) (Int.natCast_nonneg n)
    (fun k hk x _ ↦ (hasDerivAt_sqFamily hk x).hasDerivWithinAt)
    (by simp [sqFamily])
  have hrem : remainder 3 (sqFamily 3) ((0 : ℤ) : ℝ) ((n : ℤ) : ℝ) = 0 := by
    simp [remainder, sqFamily]
  have hint : (∫ t in ((0 : ℤ) : ℝ)..((n : ℤ) : ℝ), sqFamily 0 t) = (n : ℝ) ^ 3 / 3 := by
    norm_num [sqFamily, integral_pow]
  have hsum : ∑ j ∈ Finset.Icc 1 (3 / 2),
      (((bernoulli (2 * j) : ℚ) : ℝ) / ((2 * j)! : ℝ)) •
        (sqFamily (2 * j - 1) ((n : ℤ) : ℝ) - sqFamily (2 * j - 1) ((0 : ℤ) : ℝ)) =
      (n : ℝ) / 6 := by
    norm_num [Finset.Icc_self, bernoulli_two, Nat.factorial, sqFamily]
    ring
  rw [hrem, hint, hsum] at h
  simp only [sqFamily, smul_eq_mul] at h
  push_cast at h
  linarith

/-- The formula for a `C^p` function applies to the exponential function. -/
example (n : ℕ) : True := by
  have _ := sum_Icc_nat_eq_integral_add (f := Real.exp) (p := 2) (a := 0) (b := n) (by norm_num)
    (Nat.zero_le n) Real.contDiff_exp.contDiffOn
  trivial

/-- The remainder of order `1` of the constant function `1` on `[0, 1 / 2]` is `-1 / 8`, so the
remainder bounds are not statements about the zero vector. -/
example : remainder 1 (fun _ ↦ (1 : ℂ)) 0 (1 / 2) = -(1 / 8) := by
  have hEq : ∀ t ∈ Set.uIcc (0 : ℝ) (1 / 2),
      periodicBernoulli 1 t • (1 : ℂ) = ((t - 1 / 2 : ℝ) : ℂ) := fun t ht ↦ by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
    rw [Complex.real_smul, mul_one, periodicBernoulli_one,
      Int.fract_eq_self.2 ⟨ht.1, by linarith [ht.2]⟩]
  have hreal : (∫ t in (0 : ℝ)..(1 / 2), (t - 1 / 2)) = -(1 / 8) := by
    rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
      intervalIntegrable_const, integral_id]
    norm_num
  rw [remainder, intervalIntegral.integral_congr hEq, intervalIntegral.integral_ofReal, hreal]
  push_cast
  norm_num [Complex.real_smul]

/-- The rational bound for the remainder of order `2` on `[0, 1]` for the constant function `1`:
`4 / 6 ^ 2 = 1 / 9`. -/
example : ‖remainder 2 (fun _ ↦ (1 : ℂ)) 0 1‖ ≤ 1 / 9 :=
  (norm_remainder_le_of_norm_le (p := 2) (M := 1) le_rfl zero_le_one intervalIntegrable_const
    fun _ _ ↦ by simp).trans_eq (by norm_num)

/-- The bound for the Bernoulli polynomials at `k = 2` and `x = 1 / 2`: `|B_2(1 / 2)| = 1 / 12`
is below `4 * 2! / 6 ^ 2 = 2 / 9`. -/
example : |bernoulliFun 2 (1 / 2 : ℝ)| ≤ 4 * (2 ! : ℝ) / 6 ^ 2 :=
  abs_bernoulliFun_le_four_mul_factorial_div_six_pow le_rfl ⟨by norm_num, by norm_num⟩

/-- The sharp bound in even degree is attained at `0`, so it cannot be improved. -/
example : |bernoulliFun (2 * 1) (0 : ℝ)| = |((bernoulli (2 * 1) : ℚ) : ℝ)| := by
  rw [bernoulliFun_eval_zero]

example : |bernoulliFun (2 * 1) (1 / 2 : ℝ)| ≤ |((bernoulli (2 * 1) : ℚ) : ℝ)| :=
  abs_bernoulliFun_two_mul_le_abs_bernoulli 1 ⟨by norm_num, by norm_num⟩
