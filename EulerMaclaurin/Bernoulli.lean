/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
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
The series is at most $\zeta(2) = \pi^2 / 6 < 2$, and $2 \pi > 6$, so
$$|B_k(x)| \le \frac{4 \, k!}{6^k},$$
a rational bound which also holds for $k = 0$ and $k = 1$ (checked directly).  For $k = 2m$ the
series is evaluated by `hasSum_zeta_nat`, and the constant becomes the Bernoulli number:
$|B_{2m}(x)| \le |B_{2m}|$ for $x \in [0, 1]$, with equality at $x = 0$.

## Periodization

The periodic function on the real line is the composite of `periodizedBernoulli k` with the
quotient map $\mathbb{R} \to \mathbb{R} / \mathbb{Z}$, which is a coercion in Lean:
$$P_k(x) = B_k(\{x\}),$$
where $\{x\}$ is the fractional part (`periodizedBernoulli_coe`).  This gives its value on
$[m, m + 1)$ for an integer $m$, its measurability (also for $k = 1$, where it has jumps at the
integers), its bound, and the interval integrability of its product with an interval integrable
function.

## Integration by parts

For a differentiable $f$,
$$\int_a^b B_n(t - c) f(t) \, dt = \frac{1}{n + 1} \Bigl( B_{n + 1}(b - c) f(b)
  - B_{n + 1}(a - c) f(a) - \int_a^b B_{n + 1}(t - c) f'(t) \, dt \Bigr),$$
since $B_{n + 1}' = (n + 1) B_n$ (`integral_bernoulliFun_comp_sub_right_smul`).  This is the step
that raises the order in the Euler-Maclaurin formula.

## Main results

* `abs_bernoulliFun_le`: $|B_k(x)| \le 2 \, k! \, (\sum_{n \ge 1} n^{-k}) / (2 \pi)^k$ for
  $2 \le k$ and $x \in [0, 1]$.
* `abs_bernoulliFun_le_four_mul_factorial_div_six_pow`: the rational bound $4 \, k! / 6^k$.
* `abs_bernoulliFun_two_mul_le_abs_bernoulli`: the sharp bound $|B_{2m}(x)| \le |B_{2m}|$.
* `periodizedBernoulli_coe`: $P_k(x) = B_k(\{x\})$.
* `periodizedBernoulli_coe_of_mem_Ico_intCast`: $P_k(x) = B_k(x - m)$ for $x \in [m, m + 1)$.
* `abs_periodizedBernoulli_le_four_mul_factorial_div_six_pow`: the rational bound for $P_k$.
* `measurable_periodizedBernoulli_coe`: measurability of $P_k$ on $\mathbb{R}$.
* `IntervalIntegrable.periodizedBernoulli_smul`: $P_k g$ is interval integrable if $g$ is.
* `integral_bernoulliFun_comp_sub_right_smul`: integration by parts against $B_n(t - c)$.

## Implementation notes

The file does not use the Riemann zeta function `riemannZeta`: the series $\sum 1 / n^k$ and
`hasSum_zeta_nat` suffice, so no import of `Mathlib.NumberTheory.LSeries.RiemannZeta` is needed.
A form of `abs_bernoulliFun_le` with `riemannZeta k` is a one-line consequence, and belongs in
`Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean`.

This file is meant for Mathlib as an extension of `Mathlib/NumberTheory/ZetaValues.lean`.

## Tags

Bernoulli polynomial, periodization, explicit bound, Fourier series, integration by parts
-/

public section

open Complex MeasureTheory

open scoped Nat Real

/-- The series `∑ 1 / n ^ k` is dominated by `ζ(2) = π ^ 2 / 6` for `k ≥ 2`. -/
private theorem tsum_one_div_nat_pow_le {k : ℕ} (hk : 2 ≤ k) :
    ∑' n : ℕ, 1 / (n : ℝ) ^ k ≤ π ^ 2 / 6 := by
  refine hasSum_le (fun n ↦ ?_) (Real.summable_one_div_nat_pow.mpr (by omega : 1 < k)).hasSum
    hasSum_zeta_two
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [zero_pow (show k ≠ 0 by omega)]
  · exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by exact_mod_cast hn) hk)

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

/-- **Rational bound for the Bernoulli polynomials.**  For every `k` and `x ∈ [0, 1]`,
`|B_k(x)| ≤ 4 * k! / 6 ^ k`.  No transcendental constant occurs, which is convenient for certified
numerical estimates.  For `k ≥ 2` it follows from `abs_bernoulliFun_le` since the series is at most
`π ^ 2 / 6 < 2` and `6 < 2 π`; the cases `k = 0` and `k = 1` are direct. -/
theorem abs_bernoulliFun_le_four_mul_factorial_div_six_pow (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : |bernoulliFun k x| ≤ 4 * k ! / 6 ^ k := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · calc |bernoulliFun 0 x| = 1 := by simp
        _ ≤ 4 * (0 ! : ℝ) / 6 ^ 0 := by norm_num
    · have h : |x - 1 / 2| ≤ 1 / 2 := by
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2]
      calc |bernoulliFun 1 x| = |x - 1 / 2| := by rw [bernoulliFun_one]
        _ ≤ 1 / 2 := h
        _ ≤ 4 * (1 ! : ℝ) / 6 ^ 1 := by norm_num
  · refine (abs_bernoulliFun_le hk hx).trans ?_
    have hπ : π ^ 2 < 12 :=
      calc π ^ 2 < 3.15 ^ 2 := pow_lt_pow_left₀ Real.pi_lt_d2 Real.pi_pos.le two_ne_zero
        _ < 12 := by norm_num
    have h2 : 2 * (∑' n : ℕ, 1 / (n : ℝ) ^ k) ≤ 4 := by
      linarith [tsum_one_div_nat_pow_le hk]
    have h6 : (6 : ℝ) ^ k ≤ (2 * π) ^ k :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) k
    calc 2 * (∑' n : ℕ, 1 / (n : ℝ) ^ k) * k ! / (2 * π) ^ k ≤ 4 * k ! / (2 * π) ^ k := by
          gcongr
      _ ≤ 4 * k ! / 6 ^ k := by gcongr

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
  rw [periodizedBernoulli, ← AddCircle.coe_fract x,
    AddCircle.liftIco_coe_apply (a := (0 : ℝ)) (p := (1 : ℝ))
      (show Int.fract x ∈ Set.Ico (0 : ℝ) (0 + 1) by
        rw [zero_add]
        exact ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩)]

/-- On `[m, m + 1)`, for an integer `m`, the periodized Bernoulli polynomial is the translate
`x ↦ bernoulliFun k (x - m)` of the Bernoulli polynomial. -/
theorem periodizedBernoulli_coe_of_mem_Ico_intCast {k : ℕ} {m : ℤ} {x : ℝ}
    (hx : x ∈ Set.Ico (m : ℝ) (m + 1)) : periodizedBernoulli k x = bernoulliFun k (x - m) := by
  rw [periodizedBernoulli_coe, ← Int.self_sub_floor, Int.floor_eq_iff.2 ⟨hx.1, hx.2⟩]

/-- At an integer, the periodized Bernoulli polynomial is the Bernoulli number. -/
theorem periodizedBernoulli_intCast (k : ℕ) (m : ℤ) :
    periodizedBernoulli k (m : ℝ) = bernoulli k := by
  rw [periodizedBernoulli_coe, Int.fract_intCast, bernoulliFun_eval_zero]

/-- **Rational bound for the periodized Bernoulli polynomial**, on the whole circle, from
`abs_bernoulliFun_le_four_mul_factorial_div_six_pow`. -/
theorem abs_periodizedBernoulli_le_four_mul_factorial_div_six_pow (k : ℕ) (y : UnitAddCircle) :
    |periodizedBernoulli k y| ≤ 4 * k ! / 6 ^ k := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [periodizedBernoulli_coe]
  exact abs_bernoulliFun_le_four_mul_factorial_div_six_pow k
    ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

/-- The periodized Bernoulli polynomial, as a function on `ℝ`, is measurable for every `k`,
including `k = 1`, where it jumps at every integer. -/
theorem measurable_periodizedBernoulli_coe (k : ℕ) :
    Measurable fun x : ℝ ↦ periodizedBernoulli k x := by
  have h : (fun x : ℝ ↦ periodizedBernoulli k x) = bernoulliFun k ∘ Int.fract :=
    funext (periodizedBernoulli_coe k)
  rw [h]
  exact (continuous_bernoulliFun k).measurable.comp measurable_fract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The product of the periodized Bernoulli polynomial with an interval integrable function is
interval integrable.  No continuity is needed: the periodized Bernoulli polynomial is measurable
and bounded. -/
theorem IntervalIntegrable.periodizedBernoulli_smul {k : ℕ} {g : ℝ → E} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun t : ℝ ↦ periodizedBernoulli k t • g t) volume a b := by
  rw [intervalIntegrable_iff] at hg ⊢
  exact hg.bdd_smul (4 * k ! / 6 ^ k) (measurable_periodizedBernoulli_coe k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ (Real.norm_eq_abs _).trans_le
      (abs_periodizedBernoulli_le_four_mul_factorial_div_six_pow k x))

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
