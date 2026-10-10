/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import EulerMaclaurin.Bernoulli

/-!
# Bounds for the remainder of the Euler-Maclaurin formula

The remainder of the Euler-Maclaurin formula of order $p$ is
$$\frac{(-1)^{p + 1}}{p!} \int_a^b P_p(t) \, g(t) \, dt,$$
where $g$ is the $p$-th derivative and $P_p$ is the periodic Bernoulli function
(`periodizedBernoulli p`, evaluated at the class of $t$).  The bounds below are for the integral
$\int_a^b P_p g$, in terms of $\int_a^b \|g\|$ and a bound on $P_p$.  The remainder itself is
bounded by dividing by $p!$.

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

## Main results

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

## Implementation notes

This file is meant for Mathlib as part of `Mathlib/NumberTheory/EulerMaclaurin.lean`.

## Tags

Euler-Maclaurin formula, remainder estimate, Bernoulli polynomial
-/

public section

open MeasureTheory

open scoped Nat Real

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
      |((bernoulli (2 * m) : ℚ) : ℝ)| * ∫ t in a..b, ‖g t‖ :=
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

end EulerMaclaurin
