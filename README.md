# Euler-Maclaurin

The Euler-Maclaurin summation formula at every order, in Lean 4 with Mathlib, written to Mathlib's
standards with a view to contributing it upstream. The development is checked against Lean `v4.34.1`
and Mathlib `v4.34.1`.

## The result

Let `E` be a complete real normed space, `a ≤ b` real numbers, `p ≥ 1`, and `f : ℝ → E` a `C^p`
function on `[a, b]`. Write `P_n t = B_n({t})` for the periodic Bernoulli function, which in Lean is
`periodizedBernoulli n` evaluated at the class of the real number `t`. Then

```
∑_{a < i ≤ b} f i = ∫_a^b f
    + ∑_{k = 0}^{p-1} (-1)^(k+1) / (k+1)! • (P_{k+1}(b) • f^{(k)} b - P_{k+1}(a) • f^{(k)} a)
    + (-1)^(p+1) / p! • ∫_a^b P_p(t) • f^{(p)}(t) dt,
```

where the sum is over the integers in `(a, b]`, written `Finset.Ioc ⌊a⌋ ⌊b⌋`. This is
`EulerMaclaurin.sum_Ioc_eq_integral_add`. The coefficients are uniform, there is no case
distinction on the parity of `p`, and the formula is additive over adjacent intervals. For `p = 1`
it is the first order formula
`∑_{a < i ≤ b} f i = ∫_a^b f + ∫_a^b P_1 • f' + P_1(a) • f a - P_1(b) • f b`.

Each statement has a companion for a family `F : ℕ → ℝ → E` of successive derivatives, with
`F (k + 1)` a derivative of `F k` within `[a, b]` for `k < p` and `F p` only interval integrable
(`..._of_hasDerivWithinAt`). This is the weakest hypothesis, and it lets one use closed forms for
the derivatives.

For `0 ≤ a`, the same two statements with the sum over `Finset.Ioc ⌊a⌋₊ ⌊b⌋₊` in `ℕ` are
`EulerMaclaurin.sum_Ioc_nat_eq_integral_add` and
`EulerMaclaurin.sum_Ioc_nat_eq_integral_add_of_hasDerivWithinAt`.

For integer end points `a ≤ b`, `P_n a = P_n b = B_n`, and with `B'_n = (-1)^n B_n` (`bernoulli'`)
the formula reads

```
∑_{i = a+1}^{b} f i = ∫_a^b f
    + ∑_{k = 0}^{p-1} B'_{k+1} / (k+1)! • (f^{(k)} b - f^{(k)} a)
    + (-1)^(p+1) / p! • ∫_a^b P_p(t) • f^{(p)}(t) dt,
```

which is `EulerMaclaurin.sum_Ioc_int_eq_integral_add` (and
`EulerMaclaurin.sum_Ioc_int_eq_integral_add_of_hasDerivWithinAt`). Since `B'_1 = 1/2` and `B'_n = 0`
for odd `n ≥ 3`, the sum over `Finset.Icc a b` is

```
∑_{i = a}^{b} f i = ∫_a^b f + (f a + f b) / 2
    + ∑_{j = 0}^{⌊p/2⌋ - 1} B_{2j+2} / (2j+2)! • (f^{(2j+1)} b - f^{(2j+1)} a)
    + (-1)^(p+1) / p! • ∫_a^b P_p(t) • f^{(p)}(t) dt,
```

which is `EulerMaclaurin.sum_Icc_int_eq_integral_add`; the case of end points in `ℕ` is
`EulerMaclaurin.sum_Icc_nat_eq_integral_add`.

The remainder integral is bounded explicitly. For `g` interval integrable on `[a, b]`,

```
‖∫_a^b P_p • g‖ ≤ 2 ζ(p) p! / (2 π)^p * ∫_a^b ‖g‖   (p ≥ 2, with ζ(p) = ∑ 1 / n^p)
‖∫_a^b P_p • g‖ ≤ 4 p! / 6^p * ∫_a^b ‖g‖             (every p)
‖∫_a^b P_1 • g‖ ≤ 1 / 2 * ∫_a^b ‖g‖
‖∫_a^b P_{2m} • g‖ ≤ |B_{2m}| * ∫_a^b ‖g‖
```

and dividing the rational bound by `p!` gives the error bound
`‖∑_{a < i ≤ b} F 0 i - ∫_a^b F 0 - (boundary terms of order p)‖ ≤ 4 / 6^p * ∫_a^b ‖F p‖`
(`EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le`).

These rest on the bound `|B_k(x)| ≤ 2 ζ(k) * k! / (2 π)^k` for the Bernoulli polynomials on
`[0, 1]`, proved from the Fourier expansion in Mathlib and stated with the real series
`∑ 1 / n^k`, so that no zeta function is imported. For even `k` it reads `|B_k(x)| ≤ |B_k|`.

## Layout

| Module | Content | Intended Mathlib file |
| --- | --- | --- |
| `EulerMaclaurin.Bernoulli` | bounds for `bernoulliFun k` on `[0, 1]`, the periodic function as `periodizedBernoulli` composed with the quotient map, integration by parts against a Bernoulli polynomial | `Mathlib/NumberTheory/ZetaValues.lean` |
| `EulerMaclaurin.Formula` | the formula, with the remainder as an integral | `Mathlib/NumberTheory/EulerMaclaurin.lean` |
| `EulerMaclaurin.RemainderBound` | the rational bound for the Bernoulli polynomials, bounds for the remainder integral, and the error bound | the same file |

Every import of `EulerMaclaurin.Bernoulli` lies in the import closure of
`Mathlib/NumberTheory/ZetaValues.lean`. The rational bound for the Bernoulli polynomials needs
`Mathlib/Analysis/Real/Pi/Bounds.lean` and is therefore in `EulerMaclaurin.RemainderBound`. A form of
the bound on `bernoulliFun k` with `riemannZeta k` is a one-line consequence and belongs in
`Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean`.

The library `EulerMaclaurinTest` holds examples that check the theorems on concrete data, among
them Faulhaber's formula for `∑ i ^ 2`, the formula of order `2` for the exponential function, and
the case `p = 1` for real end points in the shape used for sums over `ℕ`. It is kept apart so that
`EulerMaclaurin` contains only declarations meant for Mathlib.

## Building

```
lake build
```

builds both libraries. Warnings are errors, and Mathlib's standard linters are enabled.

## Related formalizations

* Geoffrey Irving's `interval` repository has a development of the formula for `C^k` functions,
  with the sum written as a trapezoid sum.
* The `PrimeNumberTheoremAnd` project has the first order formula, for `0 ≤ a ≤ b` and a sum over
  `Finset.Ioc ⌊a⌋₊ ⌊b⌋₊`.
* `Mathlib/NumberTheory/AbelSummation.lean` has the first order Abel summation formula with real
  end points.

## References

* T. M. Apostol, *An elementary view of Euler's summation formula*, Amer. Math. Monthly 106 (1999),
  409-418, [doi:10.1080/00029890.1999.12005063](https://doi.org/10.1080/00029890.1999.12005063).
* R. L. Graham, D. E. Knuth, O. Patashnik, *Concrete Mathematics*, 2nd edition, Section 9.5.
* NIST Digital Library of Mathematical Functions, Section 2.10(i), <https://dlmf.nist.gov/2.10>.
