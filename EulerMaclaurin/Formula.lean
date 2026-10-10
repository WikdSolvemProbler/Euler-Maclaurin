/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import EulerMaclaurin.Bernoulli
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# The Euler-Maclaurin summation formula

Let $E$ be a complete real normed space, let $a \le b$ be integers and let $p \ge 1$.  Let
$B_n$ be the Bernoulli numbers and let $P_p(t) = B_p(\{t\})$ be the periodic Bernoulli function,
which in Lean is `periodizedBernoulli p`, evaluated at the class of the real number $t$.  For a
function $f : \mathbb{R} \to E$ which is $C^p$ on $[a, b]$,
$$\sum_{i = a + 1}^{b} f(i) = \int_a^b f(t) \, dt
  + \sum_{k = 0}^{p - 1} \frac{(-1)^{k + 1} B_{k + 1}}{(k + 1)!}
    \bigl( f^{(k)}(b) - f^{(k)}(a) \bigr)
  + \frac{(-1)^{p + 1}}{p!} \int_a^b P_p(t) f^{(p)}(t) \, dt.$$
This is the form with the sum over `Finset.Ioc a b`.  It has uniform coefficients, no case
distinction on the parity of $p$, and it is additive over adjacent intervals, like the Abel
summation formula.  Since $B_1 = -1/2$ and $B_n = 0$ for odd $n \ge 3$, the sum over
`Finset.Icc a b` is
$$\sum_{i = a}^{b} f(i) = \int_a^b f(t) \, dt + \frac{f(a) + f(b)}{2}
  + \sum_{j = 0}^{\lfloor p / 2 \rfloor - 1} \frac{B_{2j + 2}}{(2j + 2)!}
    \bigl( f^{(2j + 1)}(b) - f^{(2j + 1)}(a) \bigr)
  + \frac{(-1)^{p + 1}}{p!} \int_a^b P_p(t) f^{(p)}(t) \, dt.$$
Bounds on the remainder integral are in `EulerMaclaurin.RemainderBound`.

## Main results

* `EulerMaclaurin.sum_Ioc_eq_integral_add`: the formula for a $C^p$ function, with the sum over
  `Finset.Ioc a b` and the derivatives written as `iteratedDerivWithin`.
* `EulerMaclaurin.sum_Ioc_eq_integral_add_of_hasDerivWithinAt`: the same formula for a family
  `F : ℕ → ℝ → E` of successive derivatives, where `F (k + 1)` is a derivative of `F k` within
  $[a, b]$ for $k < p$ and `F p` is only interval integrable.  Closed forms for the derivatives can
  be used directly, and the $C^p$ version is a corollary.
* `EulerMaclaurin.sum_Icc_eq_integral_add` and
  `EulerMaclaurin.sum_Icc_eq_integral_add_of_hasDerivWithinAt`: the same two statements for
  the sum over `Finset.Icc a b`, with the boundary terms regrouped as above.
* `EulerMaclaurin.sum_Icc_nat_eq_integral_add`: the $C^p$ statement for `Finset.Icc` with end
  points in `ℕ`.

## Implementation notes

The order $p$ must be positive: the term with $k = 0$ comes from the integration by parts that
raises the order from $0$ to $1$.  Every order $p \ge 1$ is covered, odd and even.

The proof integrates by parts on one unit interval $[m, m + 1]$ against the polynomial
$t \mapsto B_{k + 1}(t - m) / (k + 1)$, which is smooth, so the corners of the periodic function at
the integers play no role (`integral_bernoulliFun_comp_sub_right_smul`).  The unit interval formula
is then summed by induction on the right end point.  On a unit interval the periodic Bernoulli
function agrees with the polynomial except at the right end point, a null set.

Only one-sided derivatives are required at the end points $a$ and $b$, as in
`trapezoidal_error_le` in `Mathlib/MeasureTheory/Integral/IntervalIntegral/TrapezoidalRule.lean`.

This file is meant for Mathlib as `Mathlib/NumberTheory/EulerMaclaurin.lean`.

## References

* [T. M. Apostol, *An elementary view of Euler's summation formula*][apostol1999]
* [R. L. Graham, D. E. Knuth, O. Patashnik, *Concrete Mathematics*, Section 9.5][graham1994]
* [NIST Digital Library of Mathematical Functions, Section 2.10(i)][dlmf]

## Tags

Euler-Maclaurin formula, summation formula, Bernoulli numbers, Bernoulli polynomials
-/

public section

open MeasureTheory

open scoped Nat

namespace EulerMaclaurin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Integration by parts against a Bernoulli polynomial on the unit interval `[m, m + 1]`. -/
private theorem integral_unit_bernoulliFun_smul (n : ℕ) {f f' : ℝ → E} {m : ℝ}
    (hf : ∀ x ∈ Set.Icc m (m + 1), HasDerivWithinAt f (f' x) (Set.Icc m (m + 1)) x)
    (hf' : IntervalIntegrable f' volume m (m + 1)) :
    ∫ t in m..m + 1, bernoulliFun n (t - m) • f t =
      ((n : ℝ) + 1)⁻¹ • (bernoulliFun (n + 1) 1 • f (m + 1) - bernoulliFun (n + 1) 0 • f m -
        ∫ t in m..m + 1, bernoulliFun (n + 1) (t - m) • f' t) := by
  have h := integral_bernoulliFun_comp_sub_right_smul n (a := m) (b := m + 1) (c := m)
    (by rwa [Set.uIcc_of_le (by linarith)]) hf'
  simpa only [add_sub_cancel_left, sub_self] using h

/-- The Euler-Maclaurin formula on the unit interval `[m, m + 1]`, with the Bernoulli polynomial
`B_p(t - m)` in the remainder in place of the periodic Bernoulli function. -/
private theorem unit_formula {p : ℕ} (hp : p ≠ 0) {F : ℕ → ℝ → E} {m : ℝ}
    (hF : ∀ k < p, ∀ x ∈ Set.Icc m (m + 1),
      HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc m (m + 1)) x)
    (hFp : IntervalIntegrable (F p) volume m (m + 1)) :
    F 0 (m + 1) - ∫ t in m..m + 1, F 0 t =
      ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) * ((bernoulli (k + 1) : ℚ) : ℝ) / ((k + 1)! : ℝ)) •
          (F k (m + 1) - F k m) +
        ((-1 : ℝ) ^ (p + 1) / p !) • ∫ t in m..m + 1, bernoulliFun p (t - m) • F p t := by
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp
  clear hp
  revert hF hFp
  induction p, hp1 using Nat.le_induction with
  | base =>
    intro hF hFp
    have h := integral_unit_bernoulliFun_smul 0 (hF 0 (by omega)) hFp
    have e1 : bernoulliFun 1 1 = 1 / 2 := by rw [bernoulliFun_one]; norm_num
    have e0 : bernoulliFun 1 0 = -(1 / 2) := by rw [bernoulliFun_one]; norm_num
    simp only [bernoulliFun_zero, one_smul, zero_add, Nat.cast_zero, inv_one, e1, e0] at h
    have hc : (-1 : ℝ) ^ (0 + 1) * ((bernoulli (0 + 1) : ℚ) : ℝ) / ((0 + 1)! : ℝ) = 1 / 2 := by
      norm_num [bernoulli_one]
    have hc' : (-1 : ℝ) ^ (1 + 1) / (1 ! : ℝ) = 1 := by norm_num
    rw [Finset.sum_range_one, hc, hc', one_smul]
    linear_combination (norm := module) (-1 : ℝ) • h
  | succ p hp ih =>
    intro hF hFp
    have hcp : ContinuousOn (F p) (Set.Icc m (m + 1)) := fun x hx ↦
      (hF p (Nat.lt_succ_self p) x hx).continuousWithinAt
    have h1 := ih (fun k hk x hx ↦ hF k (by omega) x hx)
      (hcp.intervalIntegrable_of_Icc (by linarith))
    have h2 := integral_unit_bernoulliFun_smul p (hF p (Nat.lt_succ_self p)) hFp
    rw [bernoulliFun_endpoints_eq_of_ne_one (by omega : p + 1 ≠ 1), bernoulliFun_eval_zero] at h2
    rw [h2] at h1
    have hfac : (((p + 1)! : ℕ) : ℝ) = ((p : ℝ) + 1) * ((p ! : ℕ) : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hne : ((p ! : ℕ) : ℝ) ≠ 0 := by positivity
    have hA : (-1 : ℝ) ^ (p + 1) * ((bernoulli (p + 1) : ℚ) : ℝ) / (((p + 1)! : ℕ) : ℝ) =
        (-1 : ℝ) ^ (p + 1) / (p ! : ℝ) * ((p : ℝ) + 1)⁻¹ * ((bernoulli (p + 1) : ℚ) : ℝ) := by
      rw [hfac]
      field_simp
    have hB : (-1 : ℝ) ^ (p + 1 + 1) / (((p + 1)! : ℕ) : ℝ) =
        -((-1 : ℝ) ^ (p + 1) / (p ! : ℝ) * ((p : ℝ) + 1)⁻¹) := by
      rw [hfac, pow_succ]
      field_simp
    rw [Finset.sum_range_succ, hA, hB]
    linear_combination (norm := module) h1

omit [CompleteSpace E] in
/-- For an integer `m`, the integral over `[m, m + 1]` of the periodic Bernoulli function times `g`
is the integral against the translated Bernoulli polynomial: the two functions differ only at
`m + 1`. -/
private theorem integral_periodizedBernoulli_smul_intCast_add_one (p : ℕ) (g : ℝ → E) (m : ℤ) :
    ∫ t in (m : ℝ)..(m : ℝ) + 1, periodizedBernoulli p t • g t =
      ∫ t in (m : ℝ)..(m : ℝ) + 1, bernoulliFun p (t - m) • g t := by
  refine intervalIntegral.integral_congr_uIoo fun t ht ↦ ?_
  rw [Set.uIoo_of_le (by linarith)] at ht
  simp only [periodizedBernoulli_coe_of_mem_Ico_intCast (Set.Ioo_subset_Ico_self ht)]

/-- **The Euler-Maclaurin summation formula over `Finset.Ioc`**, for a family `F : ℕ → ℝ → E` of
successive derivatives.  Let `a ≤ b` be integers, `p ≥ 1`, and suppose that for `k < p` the function
`F k` has derivative `F (k + 1)` within `[a, b]`, and that `F p` is interval integrable on
`[a, b]`.  Then `∑ i ∈ Finset.Ioc a b, F 0 i` equals
$$\int_a^b F_0 + \sum_{k < p} \frac{(-1)^{k + 1} B_{k + 1}}{(k + 1)!} (F_k(b) - F_k(a))
  + \frac{(-1)^{p + 1}}{p!} \int_a^b P_p F_p,$$
where `P_p = periodizedBernoulli p`. -/
theorem sum_Ioc_eq_integral_add_of_hasDerivWithinAt {p : ℕ} (hp : p ≠ 0) {F : ℕ → ℝ → E}
    {a b : ℤ} (hab : a ≤ b)
    (hF : ∀ k < p, ∀ x ∈ Set.Icc (a : ℝ) b,
      HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc (a : ℝ) b) x)
    (hFp : IntervalIntegrable (F p) volume (a : ℝ) b) :
    ∑ i ∈ Finset.Ioc a b, F 0 (i : ℝ) =
      (∫ t in (a : ℝ)..b, F 0 t) +
        ∑ k ∈ Finset.range p,
          ((-1 : ℝ) ^ (k + 1) * ((bernoulli (k + 1) : ℚ) : ℝ) / ((k + 1)! : ℝ)) •
            (F k b - F k a) +
        ((-1 : ℝ) ^ (p + 1) / p !) • ∫ t in (a : ℝ)..b, periodizedBernoulli p t • F p t := by
  revert hF hFp
  induction b, hab using Int.leInduction with
  | base =>
    intro _ _
    simp
  | succ b hb ih =>
    intro hF hFp
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hb
    simp only [Int.cast_add, Int.cast_one] at hF hFp ⊢
    have hsub1 : Set.Icc (a : ℝ) b ⊆ Set.Icc (a : ℝ) (b + 1) :=
      Set.Icc_subset_Icc_right (by linarith)
    have hsub2 : Set.Icc (b : ℝ) (b + 1) ⊆ Set.Icc (a : ℝ) (b + 1) :=
      Set.Icc_subset_Icc_left hab'
    have hmem : (b : ℝ) ∈ Set.uIcc (a : ℝ) (b + 1) := Set.mem_uIcc_of_le hab' (by linarith)
    have hFp1 : IntervalIntegrable (F p) volume (a : ℝ) b :=
      hFp.mono_set (Set.uIcc_subset_uIcc_left hmem)
    have hFp2 : IntervalIntegrable (F p) volume (b : ℝ) (b + 1) :=
      hFp.mono_set (Set.uIcc_subset_uIcc_right hmem)
    have hc0 : ContinuousOn (F 0) (Set.Icc (a : ℝ) (b + 1)) := fun x hx ↦
      (hF 0 (Nat.pos_of_ne_zero hp) x hx).continuousWithinAt
    have hI1 : IntervalIntegrable (F 0) volume (a : ℝ) b :=
      (hc0.mono hsub1).intervalIntegrable_of_Icc hab'
    have hI2 : IntervalIntegrable (F 0) volume (b : ℝ) (b + 1) :=
      (hc0.mono hsub2).intervalIntegrable_of_Icc (by linarith)
    have ih' := ih (fun k hk x hx ↦ (hF k hk x (hsub1 hx)).mono hsub1) hFp1
    have hunit := unit_formula hp (m := (b : ℝ))
      (fun k hk x hx ↦ (hF k hk x (hsub2 hx)).mono hsub2) hFp2
    rw [← integral_periodizedBernoulli_smul_intCast_add_one p (F p) b] at hunit
    have hrem : ((-1 : ℝ) ^ (p + 1) / p !) •
          ∫ t in (a : ℝ)..b + 1, periodizedBernoulli p t • F p t =
        ((-1 : ℝ) ^ (p + 1) / p !) • (∫ t in (a : ℝ)..b, periodizedBernoulli p t • F p t) +
        ((-1 : ℝ) ^ (p + 1) / p !) • ∫ t in (b : ℝ)..b + 1, periodizedBernoulli p t • F p t := by
      rw [← smul_add, intervalIntegral.integral_add_adjacent_intervals
        hFp1.periodizedBernoulli_smul hFp2.periodizedBernoulli_smul]
    have hbd : ∑ k ∈ Finset.range p,
          ((-1 : ℝ) ^ (k + 1) * ((bernoulli (k + 1) : ℚ) : ℝ) / ((k + 1)! : ℝ)) •
            (F k (b + 1) - F k a) =
        ∑ k ∈ Finset.range p,
          ((-1 : ℝ) ^ (k + 1) * ((bernoulli (k + 1) : ℚ) : ℝ) / ((k + 1)! : ℝ)) •
            (F k b - F k a) +
        ∑ k ∈ Finset.range p,
          ((-1 : ℝ) ^ (k + 1) * ((bernoulli (k + 1) : ℚ) : ℝ) / ((k + 1)! : ℝ)) •
            (F k (b + 1) - F k b) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [← smul_add]
      congr 1
      abel
    rw [← Finset.insert_Ioc_right_eq_Ioc_add_one hb, Finset.sum_insert (by simp),
      ← intervalIntegral.integral_add_adjacent_intervals hI1 hI2, hrem, hbd]
    push_cast
    linear_combination (norm := module) ih' + hunit

/-- Regrouping the coefficients `(-1)^(k + 1) B_{k+1} / (k + 1)!`, `k < p`: since `B_n = 0` for odd
`n ≥ 3`, only `k = 0`, with coefficient `1 / 2`, and the odd values `k = 2j + 1` survive, with
coefficient `B_{2j + 2} / (2j + 2)!`. -/
private theorem sum_range_split {G : Type*} [AddCommGroup G] [Module ℝ G] {p : ℕ} (hp : p ≠ 0)
    (c : ℕ → G) :
    ∑ k ∈ Finset.range p,
        ((-1 : ℝ) ^ (k + 1) * ((bernoulli (k + 1) : ℚ) : ℝ) / ((k + 1)! : ℝ)) • c k =
      (1 / 2 : ℝ) • c 0 + ∑ j ∈ Finset.range (p / 2),
        (((bernoulli (2 * j + 2) : ℚ) : ℝ) / ((2 * j + 2)! : ℝ)) • c (2 * j + 1) := by
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp
  induction p, hp1 using Nat.le_induction with
  | base =>
    norm_num [bernoulli_one]
  | succ p hp ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' p
    · have hodd : bernoulli (2 * r + 1) = 0 :=
        bernoulli_eq_zero_of_odd ⟨r, rfl⟩ (by omega)
      have hdiv : (2 * r + 1) / 2 = 2 * r / 2 := by omega
      rw [hdiv]
      simp [hodd]
    · have h1 : (2 * r + 1 + 1) / 2 = r + 1 := by omega
      have h2 : (2 * r + 1) / 2 = r := by omega
      have h3 : 2 * r + 1 + 1 = 2 * r + 2 := rfl
      have h5 : (-1 : ℝ) ^ (2 * r + 1 + 1) = 1 := Even.neg_one_pow ⟨r + 1, by ring⟩
      rw [h1, h2, Finset.sum_range_succ, h5, h3]
      module

/-- **The Euler-Maclaurin summation formula over `Finset.Icc`**, for a family `F : ℕ → ℝ → E` of
successive derivatives.  Let `a ≤ b` be integers, `p ≥ 1`, and suppose that for `k < p` the function
`F k` has derivative `F (k + 1)` within `[a, b]`, and that `F p` is interval integrable on
`[a, b]`.  Then `∑ i ∈ Finset.Icc a b, F 0 i` equals
$$\int_a^b F_0 + \frac{F_0(a) + F_0(b)}{2}
  + \sum_{j < \lfloor p / 2 \rfloor} \frac{B_{2j + 2}}{(2j + 2)!} (F_{2j + 1}(b) - F_{2j + 1}(a))
  + \frac{(-1)^{p + 1}}{p!} \int_a^b P_p F_p,$$
where `P_p = periodizedBernoulli p`.  It is `sum_Ioc_eq_integral_add_of_hasDerivWithinAt` with the
boundary terms regrouped. -/
theorem sum_Icc_eq_integral_add_of_hasDerivWithinAt {p : ℕ} (hp : p ≠ 0) {F : ℕ → ℝ → E}
    {a b : ℤ} (hab : a ≤ b)
    (hF : ∀ k < p, ∀ x ∈ Set.Icc (a : ℝ) b,
      HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc (a : ℝ) b) x)
    (hFp : IntervalIntegrable (F p) volume (a : ℝ) b) :
    ∑ i ∈ Finset.Icc a b, F 0 (i : ℝ) =
      (∫ t in (a : ℝ)..b, F 0 t) + (1 / 2 : ℝ) • (F 0 a + F 0 b) +
        ∑ j ∈ Finset.range (p / 2), (((bernoulli (2 * j + 2) : ℚ) : ℝ) / ((2 * j + 2)! : ℝ)) •
          (F (2 * j + 1) b - F (2 * j + 1) a) +
        ((-1 : ℝ) ^ (p + 1) / p !) • ∫ t in (a : ℝ)..b, periodizedBernoulli p t • F p t := by
  have h := sum_Ioc_eq_integral_add_of_hasDerivWithinAt hp hab hF hFp
  rw [sum_range_split hp (fun k ↦ F k b - F k a)] at h
  rw [Finset.Icc_eq_cons_Ioc hab, Finset.sum_cons]
  linear_combination (norm := module) h

/-- **The Euler-Maclaurin summation formula over `Finset.Ioc`** for a `C^p` function.  Let
`a ≤ b` be integers and `p ≥ 1`.  If `f` is `C^p` on `[a, b]`, then `∑ i ∈ Finset.Ioc a b, f i`
equals
$$\int_a^b f + \sum_{k < p} \frac{(-1)^{k + 1} B_{k + 1}}{(k + 1)!} (f^{(k)}(b) - f^{(k)}(a))
  + \frac{(-1)^{p + 1}}{p!} \int_a^b P_p f^{(p)},$$
where `P_p = periodizedBernoulli p` and the derivatives `f^(k)` are `iteratedDerivWithin` on
`[a, b]`. -/
theorem sum_Ioc_eq_integral_add {f : ℝ → E} {p : ℕ} (hp : p ≠ 0) {a b : ℤ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ p f (Set.Icc (a : ℝ) b)) :
    ∑ i ∈ Finset.Ioc a b, f (i : ℝ) =
      (∫ t in (a : ℝ)..b, f t) +
        ∑ k ∈ Finset.range p,
          ((-1 : ℝ) ^ (k + 1) * ((bernoulli (k + 1) : ℚ) : ℝ) / ((k + 1)! : ℝ)) •
            (iteratedDerivWithin k f (Set.Icc (a : ℝ) b) b -
              iteratedDerivWithin k f (Set.Icc (a : ℝ) b) a) +
        ((-1 : ℝ) ^ (p + 1) / p !) • ∫ t in (a : ℝ)..b,
          periodizedBernoulli p t • iteratedDerivWithin p f (Set.Icc (a : ℝ) b) t := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  · have hU : UniqueDiffOn ℝ (Set.Icc (a : ℝ) b) := uniqueDiffOn_Icc (by exact_mod_cast hlt)
    have h := sum_Ioc_eq_integral_add_of_hasDerivWithinAt
      (F := fun k ↦ iteratedDerivWithin k f (Set.Icc (a : ℝ) b)) hp hab
      (fun k hk x hx ↦ by
        rw [iteratedDerivWithin_succ]
        exact ((hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hk) hU) x hx
          ).hasDerivWithinAt)
      ((hf.continuousOn_iteratedDerivWithin le_rfl hU).intervalIntegrable_of_Icc
        (by exact_mod_cast hab))
    simpa only [iteratedDerivWithin_zero] using h

/-- **The Euler-Maclaurin summation formula over `Finset.Icc`** for a `C^p` function.  Let
`a ≤ b` be integers and `p ≥ 1`.  If `f` is `C^p` on `[a, b]`, then `∑ i ∈ Finset.Icc a b, f i`
equals
$$\int_a^b f + \frac{f(a) + f(b)}{2}
  + \sum_{j < \lfloor p / 2 \rfloor} \frac{B_{2j + 2}}{(2j + 2)!}
    (f^{(2j + 1)}(b) - f^{(2j + 1)}(a))
  + \frac{(-1)^{p + 1}}{p!} \int_a^b P_p f^{(p)},$$
where `P_p = periodizedBernoulli p` and the derivatives `f^(k)` are `iteratedDerivWithin` on
`[a, b]`. -/
theorem sum_Icc_eq_integral_add {f : ℝ → E} {p : ℕ} (hp : p ≠ 0) {a b : ℤ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ p f (Set.Icc (a : ℝ) b)) :
    ∑ i ∈ Finset.Icc a b, f (i : ℝ) =
      (∫ t in (a : ℝ)..b, f t) + (1 / 2 : ℝ) • (f a + f b) +
        ∑ j ∈ Finset.range (p / 2), (((bernoulli (2 * j + 2) : ℚ) : ℝ) / ((2 * j + 2)! : ℝ)) •
          (iteratedDerivWithin (2 * j + 1) f (Set.Icc (a : ℝ) b) b -
            iteratedDerivWithin (2 * j + 1) f (Set.Icc (a : ℝ) b) a) +
        ((-1 : ℝ) ^ (p + 1) / p !) • ∫ t in (a : ℝ)..b,
          periodizedBernoulli p t • iteratedDerivWithin p f (Set.Icc (a : ℝ) b) t := by
  have h := sum_Ioc_eq_integral_add hp hab hf
  rw [sum_range_split hp (fun k ↦ iteratedDerivWithin k f (Set.Icc (a : ℝ) b) b -
    iteratedDerivWithin k f (Set.Icc (a : ℝ) b) a)] at h
  simp only [iteratedDerivWithin_zero] at h
  rw [Finset.Icc_eq_cons_Ioc hab, Finset.sum_cons]
  linear_combination (norm := module) h

/-- **The Euler-Maclaurin summation formula** for a sum over natural numbers: the case of
`EulerMaclaurin.sum_Icc_eq_integral_add` with end points `a ≤ b` in `ℕ`. -/
theorem sum_Icc_nat_eq_integral_add {f : ℝ → E} {p : ℕ} (hp : p ≠ 0) {a b : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ p f (Set.Icc (a : ℝ) b)) :
    ∑ i ∈ Finset.Icc a b, f (i : ℝ) =
      (∫ t in (a : ℝ)..b, f t) + (1 / 2 : ℝ) • (f a + f b) +
        ∑ j ∈ Finset.range (p / 2), (((bernoulli (2 * j + 2) : ℚ) : ℝ) / ((2 * j + 2)! : ℝ)) •
          (iteratedDerivWithin (2 * j + 1) f (Set.Icc (a : ℝ) b) b -
            iteratedDerivWithin (2 * j + 1) f (Set.Icc (a : ℝ) b) a) +
        ((-1 : ℝ) ^ (p + 1) / p !) • ∫ t in (a : ℝ)..b,
          periodizedBernoulli p t • iteratedDerivWithin p f (Set.Icc (a : ℝ) b) t := by
  have h := sum_Icc_eq_integral_add hp (a := (a : ℤ)) (b := (b : ℤ)) (by exact_mod_cast hab)
    (by simpa only [Int.cast_natCast] using hf)
  simp only [Int.cast_natCast] at h
  have himage : Finset.Icc (a : ℤ) b = (Finset.Icc a b).image (Nat.cast : ℕ → ℤ) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨x.toNat, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  rw [himage, Finset.sum_image (fun x _ y _ hxy ↦ by exact_mod_cast hxy)] at h
  simpa only [Int.cast_natCast] using h

end EulerMaclaurin
