/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# The derivative of an iterated derivative within a set

On a set with unique derivatives, the iterated derivative `iteratedDerivWithin m f s` of a `C^n`
function, `m < n`, has derivative `iteratedDerivWithin (m + 1) f s x` within `s` at a point `x` of
`s`.  This is the form of `ContDiffWithinAt.differentiableWithinAt_iteratedDerivWithin` in which
the derivative is named, and it comes in the same two forms: pointwise, as
`ContDiffWithinAt.hasDerivWithinAt_iteratedDerivWithin`, and on a set, as
`ContDiffOn.hasDerivWithinAt_iteratedDerivWithin`.

## Tags

iterated derivative, derivative within a set
-/

public section

open scoped ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : 𝕜 → F} {s : Set 𝕜} {x : 𝕜}

/-- On a set with unique derivatives, the `m`-th iterated derivative of a function which is `C^n`
within the set at `x`, `m < n`, has the `(m + 1)`-th iterated derivative as its derivative within
the set at `x`. -/
theorem ContDiffWithinAt.hasDerivWithinAt_iteratedDerivWithin {n : ℕ∞ω} {m : ℕ}
    (h : ContDiffWithinAt 𝕜 n f s x) (hmn : m < n) (hs : UniqueDiffOn 𝕜 (insert x s)) :
    HasDerivWithinAt (iteratedDerivWithin m f s) (iteratedDerivWithin (m + 1) f s x) s x := by
  rw [iteratedDerivWithin_succ]
  exact (h.differentiableWithinAt_iteratedDerivWithin hmn hs).hasDerivWithinAt

/-- On a set with unique derivatives, the `m`-th iterated derivative of a `C^n` function, `m < n`,
has the `(m + 1)`-th iterated derivative as its derivative within the set at every point of the
set. -/
theorem ContDiffOn.hasDerivWithinAt_iteratedDerivWithin {n : ℕ∞ω} {m : ℕ}
    (h : ContDiffOn 𝕜 n f s) (hmn : m < n) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    HasDerivWithinAt (iteratedDerivWithin m f s) (iteratedDerivWithin (m + 1) f s x) s x :=
  (h x hx).hasDerivWithinAt_iteratedDerivWithin hmn <| by rwa [Set.insert_eq_of_mem hx]
