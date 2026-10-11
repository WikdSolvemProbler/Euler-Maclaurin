/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import EulerMaclaurin.Formula
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Bounds for the remainder of the Euler-Maclaurin formula

The remainder term of the Euler-Maclaurin formula of order $p$ is
$$\frac{(-1)^{p + 1}}{p!} \int_a^b P_p(t) \, g(t) \, dt,$$
where $g$ is the $p$-th derivative and $P_p$ is the periodic Bernoulli function
(`periodizedBernoulli p`, evaluated at the class of $t$).  It is the error of the formula: the
difference between the sum and the integral plus the boundary terms of order $p$.  The bounds for
the remainder integral $\int_a^b P_p g$ are in terms of $\int_a^b \|g\|$ and a bound on $P_p$.  The
error is bounded by dividing by $p!$.

## A rational bound for the Bernoulli polynomials

For $k \ge 2$ the series $\sum_{n \ge 1} n^{-k}$ is at most $\zeta(2) = \pi^2 / 6 < 2$, and
$2 \pi > 6$, so `abs_bernoulliFun_le` gives
$$|B_k(x)| \le \frac{4 \, k!}{6^k}, \qquad x \in [0, 1].$$
This holds for $k = 0$ and $k = 1$ as well, by a direct computation.  The constant contains no
transcendental number, which is convenient for certified numerical estimates.

## Bounds for the remainder integral

For an interval integrable function $g$ valued in a real normed space and $a \le b$ the bounds are

* $\bigl\|\int_a^b P_p g\bigr\| \le D \int_a^b \|g\|$ whenever $|B_p(x)| \le D$ on $[0, 1]$,
* $\bigl\|\int_a^b P_1 g\bigr\| \le \frac{1}{2} \int_a^b \|g\|$,
* $\bigl\|\int_a^b P_p g\bigr\| \le \frac{2 \, p!}{(2 \pi)^p} \bigl(\sum_{n \ge 1} n^{-p}\bigr)
  \int_a^b \|g\|$ for $p \ge 2$,
* $\bigl\|\int_a^b P_p g\bigr\| \le \frac{4 \, p!}{6^p} \int_a^b \|g\|$, a rational constant,
* $\bigl\|\int_a^b P_{2m} g\bigr\| \le |B_{2m}| \int_a^b \|g\|$, with the Bernoulli number $B_{2m}$.

The constant in the bound for even order is the supremum of $|P_{2m}|$, so no better constant is
possible from the size of $P_{2m}$ alone.

## Error bounds for the formula

If $|B_p(x)| \le D$ on $[0, 1]$, dividing by $p!$ gives an error bound for the Euler-Maclaurin
formula itself: the difference between the sum and the integral plus the boundary terms of order $p$
is at most
$$\frac{D}{p!} \int_a^b \|f^{(p)}\|.$$
This is stated for a $C^p$ function and for a family of derivatives.  As for the formula, the
statement for a $C^p$ function has no suffix, and the statement for a family of derivatives has the
suffix `_of_hasDerivWithinAt` (see `EulerMaclaurin.Formula`).  The choices of $D$ above give the
error bounds with $D = 1/2$ for $p = 1$, with the series for $p \ge 2$, and with the rational
constant, which is $\frac{4}{6^p} \int_a^b \|f^{(p)}\|$.  For even $p = 2m$ the choice
$D = |B_{2m}|$ gives the classical form
$\frac{|B_{2m}|}{(2m)!} \int_a^b \|f^{(2m)}\|$.  The rational constant and the even order are stated
as theorems; the others follow from the general bound.

## Main results

* `abs_bernoulliFun_le_four_mul_factorial_div_six_pow`: the rational bound for the Bernoulli
  polynomials.
* `abs_periodizedBernoulli_le_four_mul_factorial_div_six_pow`: the same bound for the periodized
  Bernoulli polynomial on the circle.
* `EulerMaclaurin.norm_integral_periodizedBernoulli_smul_le`: the bound in terms of any uniform
  bound for $B_p$ on $[0, 1]$.
* `EulerMaclaurin.norm_integral_periodizedBernoulli_one_smul_le`: the bound with constant $1/2$
  for $p = 1$.
* `EulerMaclaurin.norm_integral_periodizedBernoulli_smul_le_tsum`: the bound with the series.
* `EulerMaclaurin.norm_integral_periodizedBernoulli_smul_le_four_mul_factorial_div_six_pow`: the
  rational bound, for every $p$.
* `EulerMaclaurin.norm_integral_periodizedBernoulli_two_mul_smul_le`: the sharp bound in even
  order.
* `EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le`: the error bound for the
  Euler-Maclaurin formula in terms of any uniform bound $D$ for $B_p$ on $[0, 1]$, for a $C^p$
  function.
* `EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le_of_hasDerivWithinAt`: the
  same bound for a family of derivatives.
* `EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le`: the error bound with the rational constant
  $4 / 6^p$, for a $C^p$ function.
* `EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_of_hasDerivWithinAt`: the same bound for a family
  of derivatives.
* `EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_two_mul_of_hasDerivWithinAt`: the error bound
  $|B_{2m}| / (2m)!$ in even order, for a family of derivatives.

## Tags

Euler-Maclaurin formula, remainder estimate, Bernoulli polynomial
-/

public section

open scoped Nat Real

/-- The series `∑ 1 / n ^ k` is dominated by `ζ(2) = π ^ 2 / 6` for `k ≥ 2`. -/
private theorem tsum_one_div_nat_pow_le {k : ℕ} (hk : 2 ≤ k) :
    ∑' n : ℕ, 1 / (n : ℝ) ^ k ≤ π ^ 2 / 6 := by
  refine hasSum_le (fun n ↦ ?_) (Real.summable_one_div_nat_pow.mpr (by omega : 1 < k)).hasSum
    hasSum_zeta_two
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [zero_pow (show k ≠ 0 by omega)]
  · exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by exact_mod_cast hn) hk)

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

/-- **Rational bound for the periodized Bernoulli polynomial**, on the whole circle, from
`abs_bernoulliFun_le_four_mul_factorial_div_six_pow`. -/
theorem abs_periodizedBernoulli_le_four_mul_factorial_div_six_pow (k : ℕ) (y : UnitAddCircle) :
    |periodizedBernoulli k y| ≤ 4 * k ! / 6 ^ k := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [periodizedBernoulli_coe]
  exact abs_bernoulliFun_le_four_mul_factorial_div_six_pow k
    ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

open MeasureTheory

namespace EulerMaclaurin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℝ → E} {a b : ℝ}

/-- **The generic bound for the remainder integral.**  If `|B_p(x)| ≤ D` for `x ∈ [0, 1]`, then
`‖∫ t in a..b, P_p t • g t‖ ≤ D * ∫ t in a..b, ‖g t‖` for `a ≤ b` and `g` interval integrable,
where `P_p = periodizedBernoulli p`.  Only interval integrability of `g` is used, not that of the
product with the periodic Bernoulli function. -/
theorem norm_integral_periodizedBernoulli_smul_le {p : ℕ} {D : ℝ} (hab : a ≤ b)
    (hD : ∀ x ∈ Set.Icc (0 : ℝ) 1, |bernoulliFun p x| ≤ D) (hg : IntervalIntegrable g volume a b) :
    ‖∫ t in a..b, periodizedBernoulli p t • g t‖ ≤ D * ∫ t in a..b, ‖g t‖ := by
  have hint : ‖∫ t in a..b, periodizedBernoulli p t • g t‖ ≤ ∫ t in a..b, D * ‖g t‖ :=
    intervalIntegral.norm_integral_le_of_norm_le hab (ae_of_all _ fun t _ ↦ by
      rw [norm_smul, Real.norm_eq_abs, periodizedBernoulli_coe]
      exact mul_le_mul_of_nonneg_right (hD _ ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩)
        (norm_nonneg _)) (hg.norm.const_mul D)
  rwa [intervalIntegral.integral_const_mul] at hint

/-- The remainder integral of order `1` is bounded with the exact constant `1 / 2`: the periodic
Bernoulli function `Int.fract x - 1 / 2` of order `1` has supremum norm `1 / 2`. -/
theorem norm_integral_periodizedBernoulli_one_smul_le (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) :
    ‖∫ t in a..b, periodizedBernoulli 1 t • g t‖ ≤ 1 / 2 * ∫ t in a..b, ‖g t‖ :=
  norm_integral_periodizedBernoulli_smul_le (D := 1 / 2) hab
    (fun x hx ↦ by
      rw [bernoulliFun_one, abs_le]
      constructor <;> linarith [hx.1, hx.2]) hg

/-- **Bound for the remainder integral of order `p ≥ 2`**, in terms of the series
`∑ 1 / n ^ p`, which is `ζ(p)`.  For even `p` the constant is the Bernoulli number, see
`norm_integral_periodizedBernoulli_two_mul_smul_le`. -/
theorem norm_integral_periodizedBernoulli_smul_le_tsum {p : ℕ} (hp : 2 ≤ p) (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) :
    ‖∫ t in a..b, periodizedBernoulli p t • g t‖ ≤
      2 * (∑' n : ℕ, 1 / (n : ℝ) ^ p) * p ! / (2 * π) ^ p * ∫ t in a..b, ‖g t‖ :=
  norm_integral_periodizedBernoulli_smul_le hab (fun _ hx ↦ abs_bernoulliFun_le hp hx) hg

/-- **Rational bound for the remainder integral**, for every order `p`.  The constant
`4 * p! / 6 ^ p` contains no transcendental number, so the bound can be evaluated exactly. -/
theorem norm_integral_periodizedBernoulli_smul_le_four_mul_factorial_div_six_pow (p : ℕ)
    (hab : a ≤ b) (hg : IntervalIntegrable g volume a b) :
    ‖∫ t in a..b, periodizedBernoulli p t • g t‖ ≤ 4 * p ! / 6 ^ p * ∫ t in a..b, ‖g t‖ :=
  norm_integral_periodizedBernoulli_smul_le hab
    (fun _ hx ↦ abs_bernoulliFun_le_four_mul_factorial_div_six_pow p hx) hg

/-- **Sharp bound for the remainder integral in even order.**  The constant is the Bernoulli number
`B_{2m}`, the supremum of `|bernoulliFun (2 * m)|` on `[0, 1]`. -/
theorem norm_integral_periodizedBernoulli_two_mul_smul_le (m : ℕ) (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) :
    ‖∫ t in a..b, periodizedBernoulli (2 * m) t • g t‖ ≤
      |(bernoulli (2 * m) : ℝ)| * ∫ t in a..b, ‖g t‖ :=
  norm_integral_periodizedBernoulli_smul_le hab
    (fun _ hx ↦ abs_bernoulliFun_two_mul_le_abs_bernoulli m hx) hg

/-- The remainder term of the Euler-Maclaurin formula of order `p`, with its coefficient
`(-1) ^ (p + 1) / p !`, has norm at most `D / p ! * ∫ ‖g‖` if `|B_p(x)| ≤ D` on `[0, 1]`. -/
private theorem norm_smul_integral_periodizedBernoulli_smul_le {p : ℕ} {D : ℝ} (hab : a ≤ b)
    (hD : ∀ x ∈ Set.Icc (0 : ℝ) 1, |bernoulliFun p x| ≤ D)
    (hg : IntervalIntegrable g volume a b) :
    ‖((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • ∫ t in a..b, periodizedBernoulli p t • g t‖ ≤
      D / p ! * ∫ t in a..b, ‖g t‖ := by
  have hcoef : |(-1 : ℝ) ^ (p + 1) / (p ! : ℝ)| = 1 / (p ! : ℝ) := by
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
  rw [norm_smul, Real.norm_eq_abs, hcoef]
  calc 1 / (p ! : ℝ) * ‖∫ t in a..b, periodizedBernoulli p t • g t‖
      ≤ 1 / (p ! : ℝ) * (D * ∫ t in a..b, ‖g t‖) :=
        mul_le_mul_of_nonneg_left (norm_integral_periodizedBernoulli_smul_le hab hD hg)
          (by positivity)
    _ = D / p ! * ∫ t in a..b, ‖g t‖ := by ring

/-- The constant `4 * p ! / 6 ^ p` of the rational bound for the Bernoulli polynomials, divided by
`p !`. -/
private theorem four_mul_factorial_div_six_pow_div_factorial (p : ℕ) :
    4 * (p ! : ℝ) / 6 ^ p / p ! = 4 / 6 ^ p := by
  have hne : (p ! : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Error bound for the Euler-Maclaurin formula** in terms of a uniform bound for the Bernoulli
polynomial, for a family of derivatives.  Under the hypotheses of
`EulerMaclaurin.sum_Ioc_eq_integral_add_of_hasDerivWithinAt`, if `|B_p(x)| ≤ D` for `x ∈ [0, 1]`,
the difference between the sum over the integers in `(a, b]` and the integral plus the boundary
terms of order `p` is at most `D / p ! * ∫ ‖F p‖`.  The constants in the bounds below are instances:
`D = 1 / 2` for `p = 1`, `D = 2 * ζ(p) * p ! / (2 * π) ^ p` for `p ≥ 2` (`abs_bernoulliFun_le`),
`D = |B_p|` for even `p`, and `D = 4 * p ! / 6 ^ p`. -/
theorem norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le_of_hasDerivWithinAt
    [CompleteSpace E] {p : ℕ} {D : ℝ} (hp : p ≠ 0) {F : ℕ → ℝ → E} (hab : a ≤ b)
    (hD : ∀ x ∈ Set.Icc (0 : ℝ) 1, |bernoulliFun p x| ≤ D)
    (hF : ∀ k < p, ∀ x ∈ Set.Icc a b, HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc a b) x)
    (hFp : IntervalIntegrable (F p) volume a b) :
    ‖∑ i ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, F 0 (i : ℝ) - (∫ t in a..b, F 0 t) -
        ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • F k b - periodizedBernoulli (k + 1) a • F k a)‖ ≤
      D / p ! * ∫ t in a..b, ‖F p t‖ := by
  rw [sum_Ioc_eq_integral_add_of_hasDerivWithinAt hp hab hF hFp]
  refine (le_of_eq ?_).trans (norm_smul_integral_periodizedBernoulli_smul_le hab hD hFp)
  congr 1
  abel

/-- **Error bound for the Euler-Maclaurin formula** for a `C^p` function, in terms of a uniform
bound for the Bernoulli polynomial: the case of
`EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le_of_hasDerivWithinAt` for the
derivatives `iteratedDerivWithin k f (Set.Icc a b)`. -/
theorem norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le [CompleteSpace E]
    {f : ℝ → E} {p : ℕ} {D : ℝ} (hp : p ≠ 0) (hab : a ≤ b)
    (hD : ∀ x ∈ Set.Icc (0 : ℝ) 1, |bernoulliFun p x| ≤ D)
    (hf : ContDiffOn ℝ p f (Set.Icc a b)) :
    ‖∑ i ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, f (i : ℝ) - (∫ t in a..b, f t) -
        ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • iteratedDerivWithin k f (Set.Icc a b) b -
            periodizedBernoulli (k + 1) a • iteratedDerivWithin k f (Set.Icc a b) a)‖ ≤
      D / p ! * ∫ t in a..b, ‖iteratedDerivWithin p f (Set.Icc a b) t‖ := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  · have hU : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hlt
    simpa only [iteratedDerivWithin_zero] using
      norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le_of_hasDerivWithinAt
        (F := fun k ↦ iteratedDerivWithin k f (Set.Icc a b)) hp hab hD
        (fun k hk x hx ↦ hf.hasDerivWithinAt_iteratedDerivWithin (by exact_mod_cast hk) hU hx)
        ((hf.continuousOn_iteratedDerivWithin le_rfl hU).intervalIntegrable_of_Icc hab)

/-- **Error bound for the Euler-Maclaurin formula** with the rational constant.  Under the
hypotheses of `EulerMaclaurin.sum_Ioc_eq_integral_add_of_hasDerivWithinAt`, the difference between
the sum over the integers in `(a, b]` and the integral plus the boundary terms of order `p` is at
most `4 / 6 ^ p * ∫ ‖F p‖`. -/
theorem norm_sum_Ioc_sub_integral_sub_le_of_hasDerivWithinAt [CompleteSpace E] {p : ℕ}
    (hp : p ≠ 0) {F : ℕ → ℝ → E} (hab : a ≤ b)
    (hF : ∀ k < p, ∀ x ∈ Set.Icc a b, HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc a b) x)
    (hFp : IntervalIntegrable (F p) volume a b) :
    ‖∑ i ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, F 0 (i : ℝ) - (∫ t in a..b, F 0 t) -
        ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • F k b - periodizedBernoulli (k + 1) a • F k a)‖ ≤
      4 / 6 ^ p * ∫ t in a..b, ‖F p t‖ :=
  (norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le_of_hasDerivWithinAt hp hab
    (fun _ hx ↦ abs_bernoulliFun_le_four_mul_factorial_div_six_pow p hx) hF hFp).trans_eq
    (by rw [four_mul_factorial_div_six_pow_div_factorial])

/-- **Error bound for the Euler-Maclaurin formula** with the rational constant, for a `C^p`
function.  Under the hypotheses of `EulerMaclaurin.sum_Ioc_eq_integral_add`, the difference between
the sum over the integers in `(a, b]` and the integral plus the boundary terms of order `p` is at
most `4 / 6 ^ p * ∫ ‖f^(p)‖`, where `f^(p)` is `iteratedDerivWithin p f (Set.Icc a b)`. -/
theorem norm_sum_Ioc_sub_integral_sub_le [CompleteSpace E] {f : ℝ → E} {p : ℕ}
    (hp : p ≠ 0) (hab : a ≤ b) (hf : ContDiffOn ℝ p f (Set.Icc a b)) :
    ‖∑ i ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, f (i : ℝ) - (∫ t in a..b, f t) -
        ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • iteratedDerivWithin k f (Set.Icc a b) b -
            periodizedBernoulli (k + 1) a • iteratedDerivWithin k f (Set.Icc a b) a)‖ ≤
      4 / 6 ^ p * ∫ t in a..b, ‖iteratedDerivWithin p f (Set.Icc a b) t‖ :=
  (norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le hp hab
    (fun _ hx ↦ abs_bernoulliFun_le_four_mul_factorial_div_six_pow p hx) hf).trans_eq
    (by rw [four_mul_factorial_div_six_pow_div_factorial])

/-- **Error bound for the Euler-Maclaurin formula in even order.**  Under the hypotheses of
`EulerMaclaurin.sum_Ioc_eq_integral_add_of_hasDerivWithinAt` with `p = 2 * m`, the difference
between the sum over the integers in `(a, b]` and the integral plus the boundary terms of order
`2 * m` is at most `|B_{2m}| / (2m)! * ∫ ‖F (2 * m)‖`, the classical form of the error term. -/
theorem norm_sum_Ioc_sub_integral_sub_le_two_mul_of_hasDerivWithinAt [CompleteSpace E] {m : ℕ}
    (hm : m ≠ 0) {F : ℕ → ℝ → E} (hab : a ≤ b)
    (hF : ∀ k < 2 * m, ∀ x ∈ Set.Icc a b,
      HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc a b) x)
    (hFp : IntervalIntegrable (F (2 * m)) volume a b) :
    ‖∑ i ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, F 0 (i : ℝ) - (∫ t in a..b, F 0 t) -
        ∑ k ∈ Finset.range (2 * m), ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • F k b - periodizedBernoulli (k + 1) a • F k a)‖ ≤
      |(bernoulli (2 * m) : ℝ)| / (2 * m)! * ∫ t in a..b, ‖F (2 * m) t‖ :=
  norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le_of_hasDerivWithinAt (by omega) hab
    (fun _ hx ↦ abs_bernoulliFun_two_mul_le_abs_bernoulli m hx) hF hFp

end EulerMaclaurin
