/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import EulerMaclaurin.PeriodicBernoulli
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The Euler-Maclaurin summation formula

Let `E` be a complete real normed space, let `a ≤ b` be integers and let `p ≥ 1`.  For a function
`f : ℝ → E` which is `C^p` on `[a, b]`,

  `∑_{i = a}^{b} f(i) = ∫_a^b f + (f(a) + f(b)) / 2
      + ∑_{j = 1}^{⌊p / 2⌋} B_{2j} / (2j)! * (f^{(2j - 1)}(b) - f^{(2j - 1)}(a)) + R_p`,

where `B_{2j}` are the Bernoulli numbers and the remainder is

  `R_p = (-1)^(p + 1) / p! * ∫_a^b P_p(t) * f^{(p)}(t) dt`,

with `P_p = periodicBernoulli p` the periodic Bernoulli function.  Bounds on `R_p` are in
`EulerMaclaurin.RemainderBound`.

This file is meant for Mathlib as `Mathlib/NumberTheory/EulerMaclaurin.lean`.

## Main definitions

* `EulerMaclaurin.remainder p g a b`: the remainder
  `(-1)^(p + 1) / p! • ∫ t in a..b, periodicBernoulli p t • g t`.

## Main results

* `EulerMaclaurin.sum_Icc_eq_integral_add`: the formula for a `C^p` function, written with
  `iteratedDerivWithin`.
* `EulerMaclaurin.sum_Icc_eq_integral_add_of_hasDerivWithinAt`: the formula for a family
  `F : ℕ → ℝ → E` of successive derivatives, where `F (k + 1)` is a derivative of `F k` within
  `[a, b]` for `k < p` and `F p` is only interval integrable.  Closed forms for the derivatives
  can be used directly, and the `C^p` version above is a corollary.
* `EulerMaclaurin.sum_Icc_nat_eq_integral_add`: the `C^p` version with end points in `ℕ`.
* `EulerMaclaurin.integral_bernoulliFun_sub_smul`: integration by parts for a Bernoulli
  polynomial on a unit interval, the step that drives the induction on the order.

## Implementation notes

The order `p` must be positive: the term `(f a + f b) / 2` comes from the integration by parts that
raises the order from `0` to `1`.  Every order `p ≥ 1` is covered, odd and even.

The proof integrates by parts on one unit interval `[m, m + 1]` against the polynomial
`t ↦ B_{k + 1}(t - m) / (k + 1)`, which is smooth, so the corners of the periodic function at the
integers play no role.  The unit interval formula is then summed by induction on the right end
point.  On a unit interval the periodic Bernoulli function agrees with the polynomial except at the
right end point, a null set.

Only one-sided derivatives are required at the end points `a` and `b`, as in
`trapezoidal_error_le` in `Mathlib/MeasureTheory/Integral/IntervalIntegral/TrapezoidalRule.lean`.

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The remainder term of the Euler-Maclaurin formula of order `p` for the function `g`, which in
the formula is the `p`-th derivative:
`(-1)^(p + 1) / p! • ∫ t in a..b, periodicBernoulli p t • g t`. -/
@[expose] noncomputable def remainder (p : ℕ) (g : ℝ → E) (a b : ℝ) : E :=
  ((-1 : ℝ) ^ (p + 1) / p !) • ∫ t in a..b, periodicBernoulli p t • g t

variable [CompleteSpace E]

/-- **Integration by parts against a Bernoulli polynomial on a unit interval.**  If `f` has
derivative `f'` within `[m, m + 1]`, with `f'` interval integrable, then
`∫ B_n(t - m) • f(t) dt = (n + 1)⁻¹ • (B_{n+1}(1) • f(m + 1) - B_{n+1}(0) • f(m)
  - ∫ B_{n+1}(t - m) • f'(t) dt)`. -/
theorem integral_bernoulliFun_sub_smul (n : ℕ) {f f' : ℝ → E} {m : ℝ}
    (hf : ∀ x ∈ Set.Icc m (m + 1), HasDerivWithinAt f (f' x) (Set.Icc m (m + 1)) x)
    (hf' : IntervalIntegrable f' volume m (m + 1)) :
    ∫ t in m..m + 1, bernoulliFun n (t - m) • f t =
      ((n : ℝ) + 1)⁻¹ • (bernoulliFun (n + 1) 1 • f (m + 1) - bernoulliFun (n + 1) 0 • f m -
        ∫ t in m..m + 1, bernoulliFun (n + 1) (t - m) • f' t) := by
  have hle : m ≤ m + 1 := by linarith
  have hu : ∀ x : ℝ, HasDerivAt (fun t : ℝ ↦ bernoulliFun (n + 1) (t - m) / ((n : ℝ) + 1))
      (bernoulliFun n (x - m)) x := fun x ↦
    HasDerivAt.comp_sub_const x m (antideriv_bernoulliFun n (x - m))
  have hibp := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt
    (a := m) (b := m + 1) (u := fun t : ℝ ↦ bernoulliFun (n + 1) (t - m) / ((n : ℝ) + 1))
    (u' := fun t : ℝ ↦ bernoulliFun n (t - m)) (v := f) (v' := f')
    (fun x _ ↦ (hu x).hasDerivWithinAt) (by rwa [Set.uIcc_of_le hle])
    (((continuous_bernoulliFun n).comp (continuous_sub_right m)).intervalIntegrable _ _) hf'
  simp only [add_sub_cancel_left, sub_self] at hibp
  have hscal : ∫ t in m..m + 1, (bernoulliFun (n + 1) (t - m) / ((n : ℝ) + 1)) • f' t =
      ((n : ℝ) + 1)⁻¹ • ∫ t in m..m + 1, bernoulliFun (n + 1) (t - m) • f' t := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    simp only [smul_smul, div_eq_inv_mul]
  rw [hscal] at hibp
  linear_combination (norm := module) hibp

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
    have h := integral_bernoulliFun_sub_smul 0 (hF 0 (by omega)) hFp
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
    have h2 := integral_bernoulliFun_sub_smul p (hF p (Nat.lt_succ_self p)) hFp
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
/-- For an integer `m`, the remainder over `[m, m + 1]` is the integral against the translated
Bernoulli polynomial: the periodic Bernoulli function differs from it only at `m + 1`. -/
private theorem remainder_intCast_add_one (p : ℕ) (g : ℝ → E) (m : ℤ) :
    remainder p g m (m + 1) =
      ((-1 : ℝ) ^ (p + 1) / p !) • ∫ t in (m : ℝ)..(m : ℝ) + 1, bernoulliFun p (t - m) • g t := by
  rw [remainder]
  congr 1
  refine intervalIntegral.integral_congr_uIoo fun t ht ↦ ?_
  rw [Set.uIoo_of_le (by linarith)] at ht
  simp only [periodicBernoulli_of_mem_Ico_intCast (Set.Ioo_subset_Ico_self ht)]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Interval integrability on a sub-interval. -/
private theorem intervalIntegrable_of_Icc_subset {g : ℝ → E} {a b c d : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    IntervalIntegrable g volume c d :=
  hg.mono_set (by rw [Set.uIcc_of_le hab, Set.uIcc_of_le hcd]; exact Set.Icc_subset_Icc hac hdb)

/-- The Euler-Maclaurin formula for the sum over `Finset.Ioc a b`, with coefficients
`(-1)^(k + 1) B_{k+1} / (k + 1)!` for all `k < p`, obtained by induction on `b` from
`unit_formula`. -/
private theorem sum_Ioc_sub_integral_eq {p : ℕ} (hp : p ≠ 0) {F : ℕ → ℝ → E} {a b : ℤ}
    (hab : a ≤ b)
    (hF : ∀ k < p, ∀ x ∈ Set.Icc (a : ℝ) b,
      HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc (a : ℝ) b) x)
    (hFp : IntervalIntegrable (F p) volume (a : ℝ) b) :
    ∑ i ∈ Finset.Ioc a b, F 0 (i : ℝ) - ∫ t in (a : ℝ)..b, F 0 t =
      ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) * ((bernoulli (k + 1) : ℚ) : ℝ) / ((k + 1)! : ℝ)) •
          (F k b - F k a) +
        remainder p (F p) a b := by
  revert hF hFp
  induction b, hab using Int.leInduction with
  | base =>
    intro _ _
    simp [remainder]
  | succ b hb ih =>
    intro hF hFp
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hb
    simp only [Int.cast_add, Int.cast_one] at hF hFp ⊢
    have hsub1 : Set.Icc (a : ℝ) b ⊆ Set.Icc (a : ℝ) (b + 1) :=
      Set.Icc_subset_Icc_right (by linarith)
    have hsub2 : Set.Icc (b : ℝ) (b + 1) ⊆ Set.Icc (a : ℝ) (b + 1) :=
      Set.Icc_subset_Icc_left hab'
    have hFp1 : IntervalIntegrable (F p) volume (a : ℝ) b :=
      intervalIntegrable_of_Icc_subset (by linarith) hFp le_rfl hab' (by linarith)
    have hFp2 : IntervalIntegrable (F p) volume (b : ℝ) (b + 1) :=
      intervalIntegrable_of_Icc_subset (by linarith) hFp hab' (by linarith) le_rfl
    have hc0 : ContinuousOn (F 0) (Set.Icc (a : ℝ) (b + 1)) := fun x hx ↦
      (hF 0 (Nat.pos_of_ne_zero hp) x hx).continuousWithinAt
    have hI1 : IntervalIntegrable (F 0) volume (a : ℝ) b :=
      (hc0.mono hsub1).intervalIntegrable_of_Icc hab'
    have hI2 : IntervalIntegrable (F 0) volume (b : ℝ) (b + 1) :=
      (hc0.mono hsub2).intervalIntegrable_of_Icc (by linarith)
    have ih' := ih (fun k hk x hx ↦ (hF k hk x (hsub1 hx)).mono hsub1) hFp1
    have hunit := unit_formula hp (m := (b : ℝ))
      (fun k hk x hx ↦ (hF k hk x (hsub2 hx)).mono hsub2) hFp2
    rw [← remainder_intCast_add_one p (F p) b] at hunit
    have hrem : remainder p (F p) a (b + 1) =
        remainder p (F p) a b + remainder p (F p) b (b + 1) := by
      rw [remainder, remainder, remainder, ← smul_add,
        intervalIntegral.integral_add_adjacent_intervals hFp1.periodicBernoulli_smul
          hFp2.periodicBernoulli_smul]
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
`n ≥ 3`, only `k = 0`, with coefficient `1 / 2`, and the odd values `k = 2j - 1` survive. -/
private theorem sum_range_split {G : Type*} [AddCommGroup G] [Module ℝ G] {p : ℕ} (hp : p ≠ 0)
    (c : ℕ → G) :
    ∑ k ∈ Finset.range p,
        ((-1 : ℝ) ^ (k + 1) * ((bernoulli (k + 1) : ℚ) : ℝ) / ((k + 1)! : ℝ)) • c k =
      (1 / 2 : ℝ) • c 0 + ∑ j ∈ Finset.Icc 1 (p / 2),
        (((bernoulli (2 * j) : ℚ) : ℝ) / ((2 * j)! : ℝ)) • c (2 * j - 1) := by
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
      have h3 : 2 * (r + 1) = 2 * r + 1 + 1 := by ring
      have h5 : (-1 : ℝ) ^ (2 * r + 1 + 1) = 1 := Even.neg_one_pow ⟨r + 1, by ring⟩
      rw [h1, h2, Finset.sum_Icc_succ_top (by omega), h3, Nat.add_sub_cancel, h5]
      module

/-- **The Euler-Maclaurin summation formula**, for a family `F : ℕ → ℝ → E` of successive
derivatives.  Let `a ≤ b` be integers, `p ≥ 1`, and suppose that for `k < p` the function `F k`
has derivative `F (k + 1)` within `[a, b]`, and that `F p` is interval integrable on `[a, b]`.
Then `∑_{i = a}^{b} F 0 i` equals
`∫_a^b F 0 + (F 0 a + F 0 b) / 2`
`+ ∑_{j = 1}^{⌊p / 2⌋} B_{2j} / (2j)! • (F (2j - 1) b - F (2j - 1) a)`
plus the remainder `EulerMaclaurin.remainder p (F p) a b`. -/
theorem sum_Icc_eq_integral_add_of_hasDerivWithinAt {p : ℕ} (hp : p ≠ 0) {F : ℕ → ℝ → E}
    {a b : ℤ} (hab : a ≤ b)
    (hF : ∀ k < p, ∀ x ∈ Set.Icc (a : ℝ) b,
      HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc (a : ℝ) b) x)
    (hFp : IntervalIntegrable (F p) volume (a : ℝ) b) :
    ∑ i ∈ Finset.Icc a b, F 0 (i : ℝ) =
      (∫ t in (a : ℝ)..b, F 0 t) + (1 / 2 : ℝ) • (F 0 a + F 0 b) +
        ∑ j ∈ Finset.Icc 1 (p / 2), (((bernoulli (2 * j) : ℚ) : ℝ) / ((2 * j)! : ℝ)) •
          (F (2 * j - 1) b - F (2 * j - 1) a) +
        remainder p (F p) a b := by
  have h := sum_Ioc_sub_integral_eq hp hab hF hFp
  rw [sum_range_split hp (fun k ↦ F k b - F k a)] at h
  rw [Finset.Icc_eq_cons_Ioc hab, Finset.sum_cons]
  linear_combination (norm := module) h

/-- **The Euler-Maclaurin summation formula** for a `C^p` function.  Let `a ≤ b` be integers and
`p ≥ 1`.  If `f` is `C^p` on `[a, b]`, then `∑_{i = a}^{b} f i` equals
`∫_a^b f + (f a + f b) / 2`
`+ ∑_{j = 1}^{⌊p / 2⌋} B_{2j} / (2j)! • (f^{(2j - 1)} b - f^{(2j - 1)} a)`
plus the remainder `EulerMaclaurin.remainder p (f^{(p)}) a b`, where the derivatives are
`iteratedDerivWithin` on `[a, b]`. -/
theorem sum_Icc_eq_integral_add {f : ℝ → E} {p : ℕ} (hp : p ≠ 0) {a b : ℤ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ p f (Set.Icc (a : ℝ) b)) :
    ∑ i ∈ Finset.Icc a b, f (i : ℝ) =
      (∫ t in (a : ℝ)..b, f t) + (1 / 2 : ℝ) • (f a + f b) +
        ∑ j ∈ Finset.Icc 1 (p / 2), (((bernoulli (2 * j) : ℚ) : ℝ) / ((2 * j)! : ℝ)) •
          (iteratedDerivWithin (2 * j - 1) f (Set.Icc (a : ℝ) b) b -
            iteratedDerivWithin (2 * j - 1) f (Set.Icc (a : ℝ) b) a) +
        remainder p (iteratedDerivWithin p f (Set.Icc (a : ℝ) b)) a b := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp only [Finset.Icc_self, Finset.sum_singleton, intervalIntegral.integral_same, sub_self,
      smul_zero, Finset.sum_const_zero, add_zero, remainder]
    module
  · have hU : UniqueDiffOn ℝ (Set.Icc (a : ℝ) b) := uniqueDiffOn_Icc (by exact_mod_cast hlt)
    have h := sum_Icc_eq_integral_add_of_hasDerivWithinAt
      (F := fun k ↦ iteratedDerivWithin k f (Set.Icc (a : ℝ) b)) hp hab
      (fun k hk x hx ↦ by
        rw [iteratedDerivWithin_succ]
        exact ((hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hk) hU) x hx
          ).hasDerivWithinAt)
      ((hf.continuousOn_iteratedDerivWithin le_rfl hU).intervalIntegrable_of_Icc
        (by exact_mod_cast hab))
    simpa only [iteratedDerivWithin_zero] using h

/-- **The Euler-Maclaurin summation formula** for a sum over natural numbers: the case of
`EulerMaclaurin.sum_Icc_eq_integral_add` with endpoints `a ≤ b` in `ℕ`. -/
theorem sum_Icc_nat_eq_integral_add {f : ℝ → E} {p : ℕ} (hp : p ≠ 0) {a b : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ p f (Set.Icc (a : ℝ) b)) :
    ∑ i ∈ Finset.Icc a b, f (i : ℝ) =
      (∫ t in (a : ℝ)..b, f t) + (1 / 2 : ℝ) • (f a + f b) +
        ∑ j ∈ Finset.Icc 1 (p / 2), (((bernoulli (2 * j) : ℚ) : ℝ) / ((2 * j)! : ℝ)) •
          (iteratedDerivWithin (2 * j - 1) f (Set.Icc (a : ℝ) b) b -
            iteratedDerivWithin (2 * j - 1) f (Set.Icc (a : ℝ) b) a) +
        remainder p (iteratedDerivWithin p f (Set.Icc (a : ℝ) b)) a b := by
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
