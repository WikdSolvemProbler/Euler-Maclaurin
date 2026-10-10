/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import EulerMaclaurin.BernoulliBounds
public import EulerMaclaurin.Formula
public import EulerMaclaurin.PeriodicBernoulli
public import EulerMaclaurin.RemainderBound

/-!
# The Euler-Maclaurin summation formula

This file imports the development of the Euler-Maclaurin formula at every order:

* `EulerMaclaurin.PeriodicBernoulli`: the periodic Bernoulli functions `periodicBernoulli k`.
* `EulerMaclaurin.BernoulliBounds`: explicit bounds for the Bernoulli polynomials on `[0, 1]`.
* `EulerMaclaurin.Formula`: the formula, with the remainder as an explicit integral.
* `EulerMaclaurin.RemainderBound`: bounds for the remainder.
-/
