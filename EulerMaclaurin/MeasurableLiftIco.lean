/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Measurability of `AddCircle.liftIco`

For a measurable function `f : ℝ → β`, the function `AddCircle.liftIco T a f` on the circle
`AddCircle T`, which agrees with `f` on `[a, a + T)`, is measurable.  This holds although
`AddCircle.liftIco T a f` need not be continuous, even if `f` is, since it jumps at the class of
`a`.  It is the composite of `f` with the measurable equivalence `AddCircle.measurableEquivIco`.

## Main results

* `AddCircle.measurable_liftIco`: measurability of `AddCircle.liftIco T a f`.

## Tags

circle, periodic function, measurable
-/

public section

namespace AddCircle

variable {T : ℝ} [Fact (0 < T)] {β : Type*} [MeasurableSpace β] {a : ℝ} {f : ℝ → β}

/-- The periodization `AddCircle.liftIco T a f` of a measurable function `f : ℝ → β` is measurable.
-/
theorem measurable_liftIco (hf : Measurable f) : Measurable (AddCircle.liftIco T a f) :=
  (hf.comp measurable_subtype_coe).comp (measurableEquivIco T a).measurable

end AddCircle
