/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Measurability of `AddCircle.liftIco` and `AddCircle.liftIoc`

For a measurable function `f : ℝ → β`, the functions `AddCircle.liftIco T a f` and
`AddCircle.liftIoc T a f` on the circle `AddCircle T`, which agree with `f` on `[a, a + T)` and on
`(a, a + T]` respectively, are measurable.  This holds although they need not be continuous, even if
`f` is, since they jump at the class of `a`.  Each is the composite of `f` with the measurable
equivalence `AddCircle.measurableEquivIco` or `AddCircle.measurableEquivIoc`.  Both lemmas are
tagged `@[fun_prop]`, so that `fun_prop` proves measurability through the periodization.

## Main results

* `AddCircle.measurable_liftIco`: measurability of `AddCircle.liftIco T a f`.
* `AddCircle.measurable_liftIoc`: measurability of `AddCircle.liftIoc T a f`.

## Tags

circle, periodic function, measurable
-/

public section

namespace AddCircle

variable {T : ℝ} [Fact (0 < T)] {β : Type*} [MeasurableSpace β] {a : ℝ} {f : ℝ → β}

/-- The periodization `AddCircle.liftIco T a f` of a measurable function `f : ℝ → β`, which agrees
with `f` on `[a, a + T)`, is measurable. -/
@[fun_prop]
theorem measurable_liftIco (hf : Measurable f) : Measurable (AddCircle.liftIco T a f) :=
  (hf.comp measurable_subtype_coe).comp (measurableEquivIco T a).measurable

/-- The periodization `AddCircle.liftIoc T a f` of a measurable function `f : ℝ → β`, which agrees
with `f` on `(a, a + T]`, is measurable. -/
@[fun_prop]
theorem measurable_liftIoc (hf : Measurable f) : Measurable (AddCircle.liftIoc T a f) :=
  (hf.comp measurable_subtype_coe).comp (measurableEquivIoc T a).measurable

end AddCircle
