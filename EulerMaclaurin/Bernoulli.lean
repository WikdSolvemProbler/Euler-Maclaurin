/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import Mathlib.NumberTheory.ZetaValues

/-!
# Bernoulli polynomials: explicit bounds, periodization and integration by parts

Let $B_k$ be the Bernoulli polynomial, `bernoulliFun k : ℝ → ℝ`, and let
`periodizedBernoulli k : UnitAddCircle → ℝ` be its periodization, which agrees with $B_k$ on
$[0, 1)$.  Summation formulas such as the Euler-Maclaurin formula use three facts about these
functions, which this file proves.

## Explicit bounds

Taking norms termwise in Mathlib's Fourier expansion of $B_k$ on $[0, 1]$
(`hasSum_one_div_nat_pow_mul_fourier`) gives, for $k \ge 2$ and $x \in [0, 1]$,
$$|B_k(x)| \le \frac{2 \, k!}{(2 \pi)^k} \sum_{n \ge 1} \frac{1}{n^k}.$$
For $k = 2m$ the series is evaluated by `hasSum_zeta_nat`, and the constant becomes the Bernoulli
number: $|B_{2m}(x)| \le |B_{2m}|$ for $x \in [0, 1]$, with equality at $x = 0$.

## Periodization

The periodic function on the real line is the composite of `periodizedBernoulli k` with the
quotient map $\mathbb{R} \to \mathbb{R} / \mathbb{Z}$, which is a coercion in Lean:
$$P_k(x) = B_k(\{x\}),$$
where $\{x\}$ is the fractional part (`periodizedBernoulli_coe`).  This gives its value on
$[m, m + 1)$ for an integer $m$, its value at the integers, its measurability (also for $k = 1$,
where it has jumps at the integers), and the interval integrability of its product with an
interval integrable function.

## Integration by parts

For a differentiable $f$,
$$\int_a^b B_n(t - c) f(t) \, dt = \frac{1}{n + 1} \Bigl( B_{n + 1}(b - c) f(b)
  - B_{n + 1}(a - c) f(a) - \int_a^b B_{n + 1}(t - c) f'(t) \, dt \Bigr),$$
since $B_{n + 1}' = (n + 1) B_n$ (`integral_bernoulliFun_comp_sub_right_smul`).  This is the step
that raises the order in the Euler-Maclaurin formula.

## Main results

* `abs_bernoulliFun_le`: $|B_k(x)| \le 2 \, k! \, (\sum_{n \ge 1} n^{-k}) / (2 \pi)^k$ for
  $2 \le k$ and $x \in [0, 1]$.
* `abs_bernoulliFun_two_mul_le_abs_bernoulli`: the sharp bound $|B_{2m}(x)| \le |B_{2m}|$.
* `periodizedBernoulli_coe`: $P_k(x) = B_k(\{x\})$.
* `periodizedBernoulli_coe_of_mem_Ico_intCast`: $P_k(x) = B_k(x - m)$ for $x \in [m, m + 1)$.
* `periodizedBernoulli_intCast`: $P_k(m) = B_k$ for an integer $m$.
* `measurable_periodizedBernoulli`: measurability of $P_k$ on the circle.
* `IntervalIntegrable.periodizedBernoulli_smul`: $P_k g$ is interval integrable if $g$ is.
* `integral_bernoulliFun_comp_sub_right_smul`: integration by parts against $B_n(t - c)$.

## Implementation notes

The file does not use the Riemann zeta function `riemannZeta`: the series $\sum 1 / n^k$ and
`hasSum_zeta_nat` suffice.  A form of `abs_bernoulliFun_le` with `riemannZeta k` in place of the
series is a one-line consequence.

## Tags

Bernoulli polynomial, periodization, explicit bound, Fourier series, integration by parts
-/

public section

open Complex MeasureTheory

open scoped Nat Real

/-- **Explicit bound for the Bernoulli polynomials.**  For `k ≥ 2` and `x ∈ [0, 1]`,
`|B_k(x)| ≤ 2 * (∑ n ≥ 1, 1 / n ^ k) * k! / (2 π) ^ k`.  The proof takes norms termwise in the
Fourier expansion `hasSum_one_div_nat_pow_mul_fourier`. -/
theorem abs_bernoulliFun_le {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun k x| ≤ 2 * (∑' n : ℕ, 1 / (n : ℝ) ^ k) * k ! / (2 * π) ^ k := by
  have hs := (Real.summable_one_div_nat_pow.mpr (by omega : 1 < k)).hasSum
  have hnorm : ‖-(2 * (π : ℂ) * I) ^ k / (k ! : ℂ) * (bernoulliFun k x : ℂ)‖ ≤
      2 * ∑' n : ℕ, 1 / (n : ℝ) ^ k := by
    refine (hasSum_one_div_nat_pow_mul_fourier hk hx).norm_le_of_bounded (hs.mul_left 2)
      fun n ↦ ?_
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

/-- **Sharp bound in even degree.**  For every `m` and `x ∈ [0, 1]`,
`|B_{2m}(x)| ≤ |B_{2m}|`, where the right-hand side is the Bernoulli number.  The bound is attained
at `x = 0` (`bernoulliFun_eval_zero`).  It is `abs_bernoulliFun_le` together with the value of
`ζ(2m)` given by `hasSum_zeta_nat`. -/
theorem abs_bernoulliFun_two_mul_le_abs_bernoulli (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun (2 * m) x| ≤ |(bernoulli (2 * m) : ℝ)| := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hk : 2 ≤ 2 * m := by omega
  refine (abs_bernoulliFun_le hk hx).trans ?_
  rw [(hasSum_zeta_nat hm.ne').tsum_eq]
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

/-- The periodized Bernoulli polynomial at the class of a real number `x` is `B_k` at the
fractional part of `x`.  This is the bridge between `periodizedBernoulli`, defined on the unit
circle, and the periodic function on `ℝ`. -/
theorem periodizedBernoulli_coe (k : ℕ) (x : ℝ) :
    periodizedBernoulli k x = bernoulliFun k (Int.fract x) := by
  rw [← AddCircle.coe_fract x]
  exact AddCircle.liftIco_zero_coe_apply
    (show Int.fract x ∈ Set.Ico (0 : ℝ) 1 from ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩)

/-- On `[m, m + 1)`, for an integer `m`, the periodized Bernoulli polynomial is the translate
`x ↦ bernoulliFun k (x - m)` of the Bernoulli polynomial. -/
theorem periodizedBernoulli_coe_of_mem_Ico_intCast {k : ℕ} {m : ℤ} {x : ℝ}
    (hx : x ∈ Set.Ico (m : ℝ) (m + 1)) : periodizedBernoulli k x = bernoulliFun k (x - m) := by
  rw [periodizedBernoulli_coe, ← Int.self_sub_floor, Int.floor_eq_iff.2 ⟨hx.1, hx.2⟩]

/-- At an integer, the periodized Bernoulli polynomial is the Bernoulli number. -/
@[simp]
theorem periodizedBernoulli_intCast (k : ℕ) (m : ℤ) :
    periodizedBernoulli k (m : ℝ) = bernoulli k := by
  rw [periodizedBernoulli_coe, Int.fract_intCast, bernoulliFun_eval_zero]

/-- The periodized Bernoulli polynomial is measurable on the circle for every `k`, including
`k = 1`, where it jumps at the origin. -/
theorem measurable_periodizedBernoulli (k : ℕ) : Measurable (periodizedBernoulli k) := by
  have h : Measurable fun x : Set.Ico (0 : ℝ) (0 + 1) ↦ bernoulliFun k x :=
    (continuous_bernoulliFun k).measurable.comp measurable_subtype_coe
  exact h.comp (AddCircle.measurableEquivIco 1 0).measurable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The product of the periodized Bernoulli polynomial with an interval integrable function is
interval integrable.  No continuity is needed: the periodized Bernoulli polynomial is measurable
and bounded. -/
theorem IntervalIntegrable.periodizedBernoulli_smul {k : ℕ} {g : ℝ → E} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun t : ℝ ↦ periodizedBernoulli k t • g t) volume a b := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_bernoulliFun k).continuousOn
  have hmeas : Measurable fun x : ℝ ↦ periodizedBernoulli k (x : UnitAddCircle) :=
    (measurable_periodizedBernoulli k).comp (AddCircle.measurable_mk' (a := 1))
  have hbound : ∀ x : ℝ, ‖periodizedBernoulli k (x : UnitAddCircle)‖ ≤ C := fun x ↦ by
    rw [periodizedBernoulli_coe]
    exact hC _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  rw [intervalIntegrable_iff] at hg ⊢
  exact hg.bdd_smul C hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

variable [CompleteSpace E]

/-- **Integration by parts against a translated Bernoulli polynomial.**  If `f` has derivative
`f'` within `[a, b]`, with `f'` interval integrable, then
`∫ B_n(t - c) • f(t) dt = (n + 1)⁻¹ • (B_{n+1}(b - c) • f(b) - B_{n+1}(a - c) • f(a)
  - ∫ B_{n+1}(t - c) • f'(t) dt)`. -/
theorem integral_bernoulliFun_comp_sub_right_smul (n : ℕ) {f f' : ℝ → E} {a b c : ℝ}
    (hf : ∀ x ∈ Set.uIcc a b, HasDerivWithinAt f (f' x) (Set.uIcc a b) x)
    (hf' : IntervalIntegrable f' volume a b) :
    ∫ t in a..b, bernoulliFun n (t - c) • f t =
      ((n : ℝ) + 1)⁻¹ • (bernoulliFun (n + 1) (b - c) • f b - bernoulliFun (n + 1) (a - c) • f a -
        ∫ t in a..b, bernoulliFun (n + 1) (t - c) • f' t) := by
  have hu : ∀ x : ℝ, HasDerivAt (fun t : ℝ ↦ bernoulliFun (n + 1) (t - c) / ((n : ℝ) + 1))
      (bernoulliFun n (x - c)) x := fun x ↦
    HasDerivAt.comp_sub_const x c (antideriv_bernoulliFun n (x - c))
  have hibp := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt
    (a := a) (b := b) (u := fun t : ℝ ↦ bernoulliFun (n + 1) (t - c) / ((n : ℝ) + 1))
    (u' := fun t : ℝ ↦ bernoulliFun n (t - c)) (v := f) (v' := f')
    (fun x _ ↦ (hu x).hasDerivWithinAt) hf
    (((continuous_bernoulliFun n).comp (continuous_sub_right c)).intervalIntegrable _ _) hf'
  have hscal : ∫ t in a..b, (bernoulliFun (n + 1) (t - c) / ((n : ℝ) + 1)) • f' t =
      ((n : ℝ) + 1)⁻¹ • ∫ t in a..b, bernoulliFun (n + 1) (t - c) • f' t := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    simp only [smul_smul, div_eq_inv_mul]
  rw [hscal] at hibp
  linear_combination (norm := module) hibp
