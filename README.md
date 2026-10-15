# Euler-Maclaurin

> **Archived.** The core of this development is part of Geoffrey Irving's
> [`interval`](https://github.com/girving/interval) library since 13OCT2026
> ([girving/interval#34](https://github.com/girving/interval/pull/34), commit `2c89204`), in the
> modules `Interval/EulerMaclaurin/PeriodizedBernoulli.lean`, `Formula.lean` and
> `RemainderBound.lean`. This repository is kept read-only for reference. It also contains forms of
> the formula and bounds that are not part of `interval`: the sums over `ℕ` with real end points,
> the `Finset.Icc` forms, the regrouping into even Bernoulli numbers, and further bounds for the
> remainder integral.

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

There are five statements: for real end points, for real end points with the floor in `ℕ`, for
integer end points, and for `Finset.Icc` with end points in `ℤ` and in `ℕ`. Each comes in two forms:
the `C^p` form, and a companion for a family `F : ℕ → ℝ → E` of successive derivatives, with
`F (k + 1)` a derivative of `F k` within `[a, b]` for `k < p` and `F p` only interval integrable
(`..._of_hasDerivWithinAt`). The family form is the weakest hypothesis, and it lets one use closed
forms for the derivatives. The same convention is used for the error bounds below: the statement for
a `C^p` function has no suffix, and the statement for a family of derivatives has the suffix
`_of_hasDerivWithinAt`.

For `0 ≤ a`, the same two statements with the sum over `Finset.Ioc ⌊a⌋₊ ⌊b⌋₊` in `ℕ` are
`EulerMaclaurin.sum_Ioc_natFloor_eq_integral_add` and
`EulerMaclaurin.sum_Ioc_natFloor_eq_integral_add_of_hasDerivWithinAt`. The infix of a name records
the type of the end points: none for real end points with the floor in `ℤ`, `natFloor` for real
end points with the floor in `ℕ`, and `int` and `nat` for end points in `ℤ` and in `ℕ`.

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

which is `EulerMaclaurin.sum_Icc_int_eq_integral_add` (and
`EulerMaclaurin.sum_Icc_int_eq_integral_add_of_hasDerivWithinAt`); the case of end points in `ℕ` is
`EulerMaclaurin.sum_Icc_nat_eq_integral_add` (and
`EulerMaclaurin.sum_Icc_nat_eq_integral_add_of_hasDerivWithinAt`). The regrouping of the
coefficients `B'_{k+1} / (k+1)!` is `sum_range_bernoulli'_div_factorial_smul`, a statement about
Bernoulli numbers alone, for a field of characteristic zero acting on a module.

The remainder integral is bounded explicitly. For `g` interval integrable on `[a, b]`,
`‖∫_a^b P_p • g‖ ≤ D * ∫_a^b ‖g‖` whenever `|B_p(x)| ≤ D` for `x ∈ [0, 1]`
(`EulerMaclaurin.norm_integral_periodizedBernoulli_smul_le`), and the choices of `D` are

```
D = 2 ζ(p) p! / (2 π)^p   (p ≥ 2, with ζ(p) = ∑ 1 / n^p)
D = 4 p! / 6^p            (every p)
D = 1 / 2                 (p = 1)
D = |B_{2m}|              (p = 2m)
```

Dividing by `p!` gives the error bound for the formula: for any such `D` and a `C^p` function `f`,
`‖∑_{a < i ≤ b} f i - ∫_a^b f - (boundary terms of order p)‖ ≤ D / p! * ∫_a^b ‖f^{(p)}‖`
(`EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le`), where
`f^{(p)} = iteratedDerivWithin p f (Set.Icc a b)`, and for a family `F` of derivatives the same
bound with `F 0` and `F p` in place of `f` and `f^{(p)}`
(`EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le_of_hasDerivWithinAt`). The
rational constant gives `4 / 6^p * ∫_a^b ‖f^{(p)}‖`
(`EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le` and
`EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_of_hasDerivWithinAt`), and the even order `2m`
gives the classical `|B_{2m}| / (2m)! * ∫_a^b ‖F (2m)‖` for a family of derivatives
(`EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_two_mul_of_hasDerivWithinAt`).
These statements are for the sum over `Finset.Ioc ⌊a⌋ ⌊b⌋`. The remainder term with its coefficient
is bounded directly: `‖(-1)^(p+1) / p! • ∫_a^b P_p • g‖ ≤ D / p! * ∫_a^b ‖g‖` whenever
`|B_p(x)| ≤ D` for `x ∈ [0, 1]` (`EulerMaclaurin.norm_smul_integral_periodizedBernoulli_smul_le`).
It is the remainder term of every form of the formula, so it gives the error bound for the
`Finset.Icc`, `int` and `nat` forms as well: rewrite with the formula and apply it, as in the
example for `Finset.Icc` with end points in `ℕ` in `EulerMaclaurinTest/Examples.lean`.

These rest on the bound `|B_k(x)| ≤ 2 ζ(k) * k! / (2 π)^k` for the Bernoulli polynomials on
`[0, 1]`, proved from the Fourier expansion in Mathlib and stated with the real series
`∑ 1 / n^k`, so that no zeta function is imported. For even `k` it reads `|B_k(x)| ≤ |B_k|`.

## Layout

| Module | Content | Intended Mathlib file |
| --- | --- | --- |
| `EulerMaclaurin.MeasurableLift` | `AddCircle.measurable_liftIco` and `AddCircle.measurable_liftIoc`, measurability of the periodization of a measurable function on `[a, a + T)` and on `(a, a + T]`, both tagged `@[fun_prop]` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean` |
| `EulerMaclaurin.IteratedDeriv` | `ContDiffWithinAt.hasDerivWithinAt_iteratedDerivWithin` and `ContDiffOn.hasDerivWithinAt_iteratedDerivWithin`, the derivative of an iterated derivative within a set, in the pointwise and the set-wise form | `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean` |
| `EulerMaclaurin.BernoulliSum` | `sum_range_bernoulli'_div_factorial_smul`, the regrouping of the coefficients `B'_{k+1} / (k+1)!` into the even Bernoulli numbers | `Mathlib/NumberTheory/Bernoulli.lean` |
| `EulerMaclaurin.Bernoulli` | bounds for `bernoulliFun k` on `[0, 1]`, the periodic function as `periodizedBernoulli` composed with the quotient map, its values at integers, natural numbers, numerals, `0` and `1` (all `simp` lemmas), integration by parts against a Bernoulli polynomial | `Mathlib/NumberTheory/ZetaValues.lean` |
| `EulerMaclaurin.Formula` | the formula, with the remainder as an integral | `Mathlib/NumberTheory/EulerMaclaurin.lean` |
| `EulerMaclaurin.RemainderBound` | the rational bound for the Bernoulli polynomials, bounds for the remainder integral, and the error bounds | the same file |

Each of `EulerMaclaurin.MeasurableLift`, `EulerMaclaurin.IteratedDeriv` and
`EulerMaclaurin.BernoulliSum` imports only the Mathlib file it is meant for.
`EulerMaclaurin.Bernoulli` uses `EulerMaclaurin.MeasurableLift`, and every Mathlib import of it
lies in the import closure of `Mathlib/NumberTheory/ZetaValues.lean`.

The two pointwise bounds `4 k! / 6^k`, `abs_bernoulliFun_le_four_mul_factorial_div_six_pow` and
`abs_periodizedBernoulli_le_four_mul_factorial_div_six_pow`, are about `bernoulliFun` and
`periodizedBernoulli`, so they are in the root namespace. They are in
`EulerMaclaurin.RemainderBound` and not in `EulerMaclaurin.Bernoulli`, because they need
`Mathlib/Analysis/Real/Pi/Bounds.lean`. A form of the bound on `bernoulliFun k` with `riemannZeta k`
is a one-line consequence and belongs in `Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean`.

The library `EulerMaclaurinTest` holds examples that check the theorems on concrete data, among
them Faulhaber's formula for `∑ i ^ 2` over `Finset.Ioc` and over `Finset.Icc`, the formula of order
`2` for the exponential function, and the case `p = 1` for real end points in the shape used for
sums over `ℕ`. It is kept apart so that `EulerMaclaurin` contains only declarations meant for
Mathlib.

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
* Manuel Eberl's entry *The Euler-MacLaurin Formula* in the Isabelle Archive of Formal Proofs
  (2017) proves the formula for functions from the reals to a Banach space, in the textbook form
  and in the variant of *Concrete Mathematics*, <https://isa-afp.org/entries/Euler_MacLaurin.html>.

## References

* T. M. Apostol, *An elementary view of Euler's summation formula*, Amer. Math. Monthly 106 (1999),
  409-418, [doi:10.1080/00029890.1999.12005063](https://doi.org/10.1080/00029890.1999.12005063).
* R. L. Graham, D. E. Knuth, O. Patashnik, *Concrete Mathematics*, 2nd edition, Section 9.5.
* NIST Digital Library of Mathematical Functions, Section 2.10(i), <https://dlmf.nist.gov/2.10>.
