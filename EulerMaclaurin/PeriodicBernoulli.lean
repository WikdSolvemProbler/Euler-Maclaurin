/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.ZetaValues

/-!
# Periodic Bernoulli functions on the real line

Mathlib has the Bernoulli polynomial as a real function, `bernoulliFun k : ℝ → ℝ`, and its
periodization to the unit circle, `periodizedBernoulli k : UnitAddCircle → ℝ`.  Summation formulas
are stated with the periodic function on `ℝ` itself, which is what this file provides:

  `periodicBernoulli k x = bernoulliFun k (Int.fract x)`.

It is the `1`-periodic function that agrees with `bernoulliFun k` on `[0, 1)`.  For `k = 1` it is
the sawtooth `Int.fract x - 1 / 2`, which jumps at the integers; for `k ≠ 1` it is continuous.

This file is meant for Mathlib as `Mathlib/NumberTheory/PeriodicBernoulli.lean`.

## Main definitions

* `periodicBernoulli k`: the `1`-periodic extension of `bernoulliFun k` from `[0, 1)` to `ℝ`.

## Main results

* `periodicBernoulli_periodic`: periodicity.
* `periodicBernoulli_of_mem_Ico_intCast`: on `[m, m + 1)` it is `x ↦ bernoulliFun k (x - m)`.
* `periodicBernoulli_eq_periodizedBernoulli`: it is the pullback of `periodizedBernoulli k` along
  the quotient map `ℝ → UnitAddCircle`.
* `continuous_periodicBernoulli`: continuity for `k ≠ 1`.
* `measurable_periodicBernoulli`: measurability for every `k`.
* `IntervalIntegrable.periodicBernoulli_smul`: the product of `periodicBernoulli k` with an
  interval integrable function valued in a real normed space is interval integrable.

## Tags

Bernoulli polynomial, periodic function, sawtooth
-/

public section

open MeasureTheory Set

/-- The `k`-th periodic Bernoulli function on `ℝ`: the `1`-periodic function that agrees with the
Bernoulli polynomial `bernoulliFun k` on `[0, 1)`. -/
@[expose] noncomputable def periodicBernoulli (k : ℕ) (x : ℝ) : ℝ :=
  bernoulliFun k (Int.fract x)

theorem periodicBernoulli_periodic (k : ℕ) : Function.Periodic (periodicBernoulli k) 1 := fun x ↦ by
  simp only [periodicBernoulli, Int.fract_add_one]

theorem periodicBernoulli_of_mem_Ico {k : ℕ} {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    periodicBernoulli k x = bernoulliFun k x := by
  rw [periodicBernoulli, Int.fract_eq_self.2 hx]

/-- On `[m, m + 1)`, for an integer `m`, the periodic Bernoulli function is the translate
`x ↦ bernoulliFun k (x - m)` of the Bernoulli polynomial. -/
theorem periodicBernoulli_of_mem_Ico_intCast {k : ℕ} {m : ℤ} {x : ℝ}
    (hx : x ∈ Ico (m : ℝ) (m + 1)) : periodicBernoulli k x = bernoulliFun k (x - m) := by
  rw [periodicBernoulli, ← Int.self_sub_floor, Int.floor_eq_iff.2 ⟨hx.1, hx.2⟩]

@[simp]
theorem periodicBernoulli_intCast (k : ℕ) (m : ℤ) :
    periodicBernoulli k m = bernoulli k := by
  rw [periodicBernoulli, Int.fract_intCast, bernoulliFun_eval_zero]

@[simp]
theorem periodicBernoulli_zero (x : ℝ) : periodicBernoulli 0 x = 1 := by
  simp [periodicBernoulli]

@[simp]
theorem periodicBernoulli_one (x : ℝ) : periodicBernoulli 1 x = Int.fract x - 1 / 2 := by
  simp [periodicBernoulli]

/-- `periodicBernoulli k` is the pullback of Mathlib's `periodizedBernoulli k` along the quotient
map `ℝ → UnitAddCircle`. -/
theorem periodicBernoulli_eq_periodizedBernoulli (k : ℕ) (x : ℝ) :
    periodicBernoulli k x = periodizedBernoulli k (x : UnitAddCircle) := by
  rw [periodicBernoulli, periodizedBernoulli, ← AddCircle.coe_fract x,
    AddCircle.liftIco_coe_apply (a := (0 : ℝ)) (p := (1 : ℝ))
      (show Int.fract x ∈ Ico (0 : ℝ) (0 + 1) by
        rw [zero_add]
        exact ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩)]

/-- The periodic Bernoulli function is continuous for `k ≠ 1`.  For `k = 1` it jumps by `1` at
every integer. -/
theorem continuous_periodicBernoulli {k : ℕ} (hk : k ≠ 1) : Continuous (periodicBernoulli k) := by
  have h : periodicBernoulli k = periodizedBernoulli k ∘ (fun x : ℝ ↦ (x : UnitAddCircle)) :=
    funext (periodicBernoulli_eq_periodizedBernoulli k)
  rw [h]
  exact (periodizedBernoulli.continuous hk).comp continuous_quotient_mk'

/-- Every periodic Bernoulli function is measurable, including the discontinuous case `k = 1`. -/
@[fun_prop]
theorem measurable_periodicBernoulli (k : ℕ) : Measurable (periodicBernoulli k) :=
  (continuous_bernoulliFun k).measurable.comp measurable_fract

/-- Every periodic Bernoulli function is bounded.  The bound is the maximum of the continuous
function `bernoulliFun k` on the compact interval `[0, 1]`. -/
theorem exists_forall_abs_periodicBernoulli_le (k : ℕ) :
    ∃ C : ℝ, ∀ x, |periodicBernoulli k x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_bernoulliFun k).continuousOn
  refine ⟨C, fun x ↦ ?_⟩
  rw [periodicBernoulli, ← Real.norm_eq_abs]
  exact hC _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The product of a periodic Bernoulli function with an interval integrable function is interval
integrable.  No continuity is needed: the periodic Bernoulli function is measurable and bounded. -/
theorem IntervalIntegrable.periodicBernoulli_smul {k : ℕ} {g : ℝ → E} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun t ↦ periodicBernoulli k t • g t) volume a b := by
  obtain ⟨C, hC⟩ := exists_forall_abs_periodicBernoulli_le k
  rw [intervalIntegrable_iff] at hg ⊢
  exact hg.bdd_smul C (measurable_periodicBernoulli k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ (Real.norm_eq_abs _).trans_le (hC x))
