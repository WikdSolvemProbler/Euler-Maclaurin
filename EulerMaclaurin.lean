/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import EulerMaclaurin.Bernoulli
public import EulerMaclaurin.Formula
public import EulerMaclaurin.IteratedDeriv
public import EulerMaclaurin.RemainderBound

/-!
# The Euler-Maclaurin summation formula

This file imports the development of the Euler-Maclaurin formula at every order:

* `EulerMaclaurin.Bernoulli`: explicit bounds for the Bernoulli polynomials on $[0, 1]$, the
  periodic Bernoulli function as `periodizedBernoulli` on the unit circle, and integration by
  parts against a Bernoulli polynomial.
* `EulerMaclaurin.IteratedDeriv`: the derivative of an iterated derivative within a set, for a
  `C^n` function.
* `EulerMaclaurin.Formula`: the formula for real end points, with the remainder as an explicit
  integral, and its forms for sums over `ℕ`, for integer end points and for `Finset.Icc`.
* `EulerMaclaurin.RemainderBound`: bounds for the remainder integral, a rational bound for the
  Bernoulli polynomials, and the error bound for the formula.
-/
