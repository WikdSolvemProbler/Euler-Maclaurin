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

The remainder of the Euler-Maclaurin formula of order $p$ is
$$\frac{(-1)^{p + 1}}{p!} \int_a^b P_p(t) \, g(t) \, dt,$$
where $g$ is the $p$-th derivative and $P_p$ is the periodic Bernoulli function
(`periodizedBernoulli p`, evaluated at the class of $t$).  The bounds below are for the integral
$\int_a^b P_p g$, in terms of $\int_a^b \|g\|$ and a bound on $P_p$.  The remainder itself is
bounded by dividing by $p!$.

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
* $\bigl\|\int_a^b P_{2m} g\bigr\| \le |B_{2m}| \int_a^b \|g\|$, with the Bernoulli number $B_{2m}$,

and, if $\|g\| \le M$ on $[a, b]$, $\bigl\|\int_a^b P_p g\bigr\| \le \frac{4 \, p!}{6^p} M (b - a)$.
The constant in the bound for even order is the supremum of $|P_{2m}|$, so no better constant is
possible from the size of $P_{2m}$ alone.

Dividing the rational bound by $p!$ gives an error bound for the Euler-Maclaurin formula itself:
the difference between the sum and the integral plus the boundary terms of order $p$ is at most
$\frac{4}{6^p} \int_a^b \|f^{(p)}\|$.

## Main results

* `EulerMaclaurin.abs_bernoulliFun_le_four_mul_factorial_div_six_pow`: the rational bound for the
  Bernoulli polynomials.
* `EulerMaclaurin.abs_periodizedBernoulli_le_four_mul_factorial_div_six_pow`: the same bound for
  the periodized Bernoulli polynomial on the circle.
* `EulerMaclaurin.norm_integral_periodizedBernoulli_smul_le`: the bound in terms of any uniform
  bound for $B_p$ on $[0, 1]$.
* `EulerMaclaurin.norm_integral_periodizedBernoulli_one_smul_le`: the bound with constant $1/2$
  for $p = 1$.
* `EulerMaclaurin.norm_integral_periodizedBernoulli_smul_le_tsum`: the bound with the series.
* `EulerMaclaurin.norm_integral_periodizedBernoulli_smul_le_four_mul_factorial_div_six_pow`: the
  rational bound, for every $p$.
* `EulerMaclaurin.norm_integral_periodizedBernoulli_two_mul_smul_le`: the sharp bound in even
  order.
* `EulerMaclaurin.norm_integral_periodizedBernoulli_smul_le_of_norm_le`: the bound for a function
  bounded by a constant.
* `EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le`: the error bound for the Euler-Maclaurin
  formula.

## Tags

Euler-Maclaurin formula, remainder estimate, Bernoulli polynomial
-/

public section

open MeasureTheory

open scoped Nat Real

namespace EulerMaclaurin

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

/-- If `‖g‖ ≤ M` on `[a, b]` then the remainder integral of order `p` is at most
`4 * p! / 6 ^ p * (M * (b - a))`, an expression in the four parameters `p`, `M`, `a` and `b` with
no integral left to evaluate. -/
theorem norm_integral_periodizedBernoulli_smul_le_of_norm_le (p : ℕ) {M : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (hM : ∀ t ∈ Set.Icc a b, ‖g t‖ ≤ M) :
    ‖∫ t in a..b, periodizedBernoulli p t • g t‖ ≤ 4 * p ! / 6 ^ p * (M * (b - a)) := by
  refine (norm_integral_periodizedBernoulli_smul_le_four_mul_factorial_div_six_pow p hab hg).trans
    (mul_le_mul_of_nonneg_left ?_ (by positivity))
  simpa [mul_comm] using intervalIntegral.integral_mono_on hab hg.norm intervalIntegrable_const hM

/-- The remainder term of the Euler-Maclaurin formula of order `p`, with its coefficient
`(-1) ^ (p + 1) / p !`, has norm at most `4 / 6 ^ p * ∫ ‖g‖`. -/
private theorem norm_smul_integral_periodizedBernoulli_smul_le {p : ℕ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) :
    ‖((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • ∫ t in a..b, periodizedBernoulli p t • g t‖ ≤
      4 / 6 ^ p * ∫ t in a..b, ‖g t‖ := by
  have hcoef : |(-1 : ℝ) ^ (p + 1) / (p ! : ℝ)| = 1 / (p ! : ℝ) := by
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
  rw [norm_smul, Real.norm_eq_abs, hcoef]
  have hne : (p ! : ℝ) ≠ 0 := by positivity
  calc 1 / (p ! : ℝ) * ‖∫ t in a..b, periodizedBernoulli p t • g t‖
      ≤ 1 / (p ! : ℝ) * (4 * p ! / 6 ^ p * ∫ t in a..b, ‖g t‖) :=
        mul_le_mul_of_nonneg_left
          (norm_integral_periodizedBernoulli_smul_le_four_mul_factorial_div_six_pow p hab hg)
          (by positivity)
    _ = 4 / 6 ^ p * ∫ t in a..b, ‖g t‖ := by
        field_simp

/-- **Error bound for the Euler-Maclaurin formula.**  Under the hypotheses of
`EulerMaclaurin.sum_Ioc_eq_integral_add_of_hasDerivWithinAt`, the difference between the sum over
the integers in `(a, b]` and the integral plus the boundary terms of order `p` is at most
`4 / 6 ^ p * ∫ ‖F p‖`. -/
theorem norm_sum_Ioc_sub_integral_sub_le [CompleteSpace E] {p : ℕ} (hp : p ≠ 0) {F : ℕ → ℝ → E}
    (hab : a ≤ b)
    (hF : ∀ k < p, ∀ x ∈ Set.Icc a b, HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc a b) x)
    (hFp : IntervalIntegrable (F p) volume a b) :
    ‖∑ i ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, F 0 (i : ℝ) - (∫ t in a..b, F 0 t) -
        ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • F k b - periodizedBernoulli (k + 1) a • F k a)‖ ≤
      4 / 6 ^ p * ∫ t in a..b, ‖F p t‖ := by
  rw [sum_Ioc_eq_integral_add_of_hasDerivWithinAt hp hab hF hFp]
  refine (le_of_eq ?_).trans (norm_smul_integral_periodizedBernoulli_smul_le (p := p) hab hFp)
  congr 1
  abel

end EulerMaclaurin
