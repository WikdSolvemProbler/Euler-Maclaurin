# Euler-Maclaurin

The Euler-Maclaurin summation formula at every order, in Lean 4 with Mathlib, written to Mathlib's
standards with a view to contributing it upstream. The development is checked against Lean `v4.34.1`
and Mathlib `v4.34.1`.

## The result

Let `E` be a complete real normed space, `a ≤ b` integers, `p ≥ 1`, and `f : ℝ → E` a `C^p`
function on `[a, b]`. Then

```
∑_{i = a}^{b} f i = ∫_a^b f + (f a + f b) / 2
    + ∑_{j = 1}^{⌊p / 2⌋} B_{2j} / (2j)! • (f^{(2j-1)} b - f^{(2j-1)} a) + R_p
```

where `B_{2j}` are the Bernoulli numbers and the remainder is the explicit integral

```
R_p = (-1)^(p + 1) / p! • ∫_a^b P_p(t) • f^{(p)}(t) dt,    P_p = periodicBernoulli p.
```

The theorem is `EulerMaclaurin.sum_Icc_eq_integral_add`. Two companions have the same conclusion:

* `EulerMaclaurin.sum_Icc_eq_integral_add_of_hasDerivWithinAt` takes a family of derivatives
  `F : ℕ → ℝ → E`, with `F (k + 1)` a derivative of `F k` within `[a, b]` for `k < p` and `F p` only
  interval integrable. This is the weakest hypothesis, and it lets one use closed forms for the
  derivatives.
* `EulerMaclaurin.sum_Icc_nat_eq_integral_add` is the statement for endpoints in `ℕ`.

The remainder is bounded explicitly. For `p ≥ 2` and `g` interval integrable on `[a, b]`,

```
‖R_p(g)‖ ≤ 2 ζ(p) / (2 π)^p * ∫_a^b ‖g‖ ≤ 4 / 6^p * ∫_a^b ‖g‖,
```

and for `p = 1` the constant is `1 / 2`. These rest on the bound
`|B_k(x)| ≤ 2 ζ(k) * k! / (2 π)^k` for the Bernoulli polynomials on `[0, 1]`, proved from the
Fourier expansion in Mathlib, which for even `k` reads `|B_k(x)| ≤ |B_k|`.

## Layout

| Module | Content | Intended Mathlib file |
| --- | --- | --- |
| `EulerMaclaurin.PeriodicBernoulli` | `periodicBernoulli k`, the periodic Bernoulli function on `ℝ` | `Mathlib/NumberTheory/PeriodicBernoulli.lean` |
| `EulerMaclaurin.BernoulliBounds` | explicit bounds for `bernoulliFun k` on `[0, 1]` | `Mathlib/NumberTheory/ZetaValues.lean` or a sibling file |
| `EulerMaclaurin.Formula` | the formula, with the remainder as an integral | `Mathlib/NumberTheory/EulerMaclaurin.lean` |
| `EulerMaclaurin.RemainderBound` | bounds for the remainder | the same file, or a sibling file |

The library `EulerMaclaurinTest` holds examples that check the theorems on concrete data, among
them Faulhaber's formula for `∑ i ^ 2`. It is kept apart so that `EulerMaclaurin` contains only
declarations meant for Mathlib.

## Building

```
lake build
```

builds both libraries. Warnings are errors, and Mathlib's standard linters are enabled.

## Related formalizations

* Geoffrey Irving's `interval` repository has a development of the formula for `C^k` functions,
  with the sum written as a trapezoid sum.
* The `PrimeNumberTheoremAnd` project has the first order formula.

## References

* T. M. Apostol, *An elementary view of Euler's summation formula*, Amer. Math. Monthly 106 (1999),
  409-418.
* R. L. Graham, D. E. Knuth, O. Patashnik, *Concrete Mathematics*, 2nd edition, Section 9.5.
* NIST Digital Library of Mathematical Functions, Section 2.10(i).
