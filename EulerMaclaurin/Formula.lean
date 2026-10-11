/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import EulerMaclaurin.Bernoulli
public import EulerMaclaurin.BernoulliSum
public import EulerMaclaurin.IteratedDeriv
public import Mathlib.Data.Nat.Cast.SetInterval

/-!
# The Euler-Maclaurin summation formula

Let $E$ be a complete real normed space, let $a \le b$ be real numbers and let $p \ge 1$.  Let
$P_n(t) = B_n(\{t\})$ be the periodic Bernoulli function, which in Lean is
`periodizedBernoulli n`, evaluated at the class of the real number $t$.  For a function
$f : \mathbb{R} \to E$ which is $C^p$ on $[a, b]$,
$$\sum_{a < i \le b} f(i) = \int_a^b f(t) \, dt
  + \sum_{k = 0}^{p - 1} \frac{(-1)^{k + 1}}{(k + 1)!}
    \bigl( P_{k + 1}(b) f^{(k)}(b) - P_{k + 1}(a) f^{(k)}(a) \bigr)
  + \frac{(-1)^{p + 1}}{p!} \int_a^b P_p(t) f^{(p)}(t) \, dt.$$
The sum is over the integers in $(a, b]$, written `Finset.Ioc ⌊a⌋ ⌊b⌋`.  The formula is additive
over adjacent intervals, like the Abel summation formula, and has uniform coefficients with no
case distinction on the parity of $p$.  For $p = 1$ it is the first order formula
$\sum_{a < i \le b} f(i) = \int_a^b f + \int_a^b P_1 f' + P_1(a) f(a) - P_1(b) f(b)$.

If $a$ and $b$ are integers, then $P_n(a) = B_n$ and $P_n(b) = B_n$, and with
$B'_n = (-1)^n B_n$ the formula reads
$$\sum_{i = a + 1}^{b} f(i) = \int_a^b f(t) \, dt
  + \sum_{k = 0}^{p - 1} \frac{B'_{k + 1}}{(k + 1)!} \bigl( f^{(k)}(b) - f^{(k)}(a) \bigr)
  + \frac{(-1)^{p + 1}}{p!} \int_a^b P_p(t) f^{(p)}(t) \, dt.$$
Since $B'_1 = 1/2$ and $B'_n = 0$ for odd $n \ge 3$ (`sum_range_bernoulli'_div_factorial_smul`), the
sum over `Finset.Icc a b` is
$$\sum_{i = a}^{b} f(i) = \int_a^b f(t) \, dt + \frac{f(a) + f(b)}{2}
  + \sum_{j = 0}^{\lfloor p / 2 \rfloor - 1} \frac{B_{2j + 2}}{(2j + 2)!}
    \bigl( f^{(2j + 1)}(b) - f^{(2j + 1)}(a) \bigr)
  + \frac{(-1)^{p + 1}}{p!} \int_a^b P_p(t) f^{(p)}(t) \, dt.$$
The error of the formula, that is, the remainder term with its coefficient, is bounded in
`EulerMaclaurin.RemainderBound`: by
`EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le` in terms of any uniform
bound for $B_p$ on $[0, 1]$, and by `EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le` with the
constant $4 / 6^p$.  For the other forms of the formula the remainder term is bounded by
`EulerMaclaurin.norm_smul_integral_periodizedBernoulli_smul_le`.

## Main results

The infix of a name records the type of the end points `a` and `b`: no infix for real end points
with the floor in `ℤ`, `natFloor` for real end points with the floor in `ℕ`, and `int` and `nat` for
end points in `ℤ` and in `ℕ`.  The statement for a $C^p$ function has no suffix, and the statement
for a family of derivatives has the suffix `_of_hasDerivWithinAt`, as in
`EulerMaclaurin.RemainderBound`.

* `EulerMaclaurin.sum_Ioc_eq_integral_add`: the formula for real end points and a $C^p$ function,
  with the derivatives written as `iteratedDerivWithin`.
* `EulerMaclaurin.sum_Ioc_eq_integral_add_of_hasDerivWithinAt`: the same formula for a family
  `F : ℕ → ℝ → E` of successive derivatives, where `F (k + 1)` is a derivative of `F k` within
  $[a, b]$ for $k < p$ and `F p` is only interval integrable.  Closed forms for the derivatives can
  be used directly, and the $C^p$ version is a corollary.
* `EulerMaclaurin.sum_Ioc_natFloor_eq_integral_add` and
  `EulerMaclaurin.sum_Ioc_natFloor_eq_integral_add_of_hasDerivWithinAt`: the same two statements
  for $0 \le a$, with the sum over `Finset.Ioc ⌊a⌋₊ ⌊b⌋₊` in `ℕ`.
* `EulerMaclaurin.sum_Ioc_int_eq_integral_add` and
  `EulerMaclaurin.sum_Ioc_int_eq_integral_add_of_hasDerivWithinAt`: the two statements for integer
  end points, in which the periodic Bernoulli function does not occur in the boundary terms.
* `EulerMaclaurin.sum_Icc_int_eq_integral_add` and
  `EulerMaclaurin.sum_Icc_int_eq_integral_add_of_hasDerivWithinAt`, and
  `EulerMaclaurin.sum_Icc_nat_eq_integral_add` and
  `EulerMaclaurin.sum_Icc_nat_eq_integral_add_of_hasDerivWithinAt`: the two statements for
  `Finset.Icc` with end points in `ℤ` and in `ℕ`.  They are the Ioc statements for integer end
  points with the odd Bernoulli numbers removed.
* `sum_range_bernoulli'_div_factorial_smul`, in `EulerMaclaurin.BernoulliSum`: the regrouping of the
  coefficients $B'_{k + 1} / (k + 1)!$ used for this, which is a fact about Bernoulli numbers and
  does not involve analysis.

## Implementation notes

The order $p$ must be positive: the term with $k = 0$ comes from the integration by parts that
raises the order from $0$ to $1$.  Every order $p \ge 1$ is covered, odd and even.

The proof integrates by parts against the polynomial $t \mapsto B_{k + 1}(t - c) / (k + 1)$, which
is smooth, so the corners of the periodic function at the integers play no role
(`integral_bernoulliFun_comp_sub_right_smul`).  Iterating gives an identity on any interval, with
the polynomial $B_p(t - c)$ in place of $P_p$ in the remainder.  If $x \le y$ both lie in
$[m, m + 1)$ for an integer $m$, then $P_n = B_n(\cdot - m)$ on $[x, y]$, and the identity says
that the right-hand side of the formula over $[x, y]$ vanishes, in agreement with the empty sum.
If $x \in [m, m + 1)$ and the right end point is the integer $m + 1$, then $P_n(m + 1) = B_n(0)$
differs from $B_n(1)$ by $1$ for $n = 1$ and by $0$ otherwise (`bernoulliFun_eval_one`); this
produces the single term $f(m + 1)$ of the sum.  The general formula follows by induction on the
number of integers in $(a, b]$: the first integer $m + 1 > a$ is split off, and the rest is the same
statement for the interval $[m + 1, b]$.

Only one-sided derivatives are required at the end points $a$ and $b$, as in
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Repeated integration by parts** against the translated Bernoulli polynomials
`B_{k+1}(t - c)`: the formula of order `p` over `[x, y]`, with the polynomial `B_p(t - c)` in the
remainder in place of the periodic Bernoulli function, and with no sum over the integers. -/
private theorem integral_add_sum_add_integral_bernoulliFun_eq_zero {F : ℕ → ℝ → E} {x y c : ℝ}
    (p : ℕ) (hF : ∀ k < p, ∀ t ∈ Set.uIcc x y,
      HasDerivWithinAt (F k) (F (k + 1) t) (Set.uIcc x y) t)
    (hFp : IntervalIntegrable (F p) volume x y) :
    (∫ t in x..y, F 0 t) +
      ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
        (bernoulliFun (k + 1) (y - c) • F k y - bernoulliFun (k + 1) (x - c) • F k x) +
      ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • ∫ t in x..y, bernoulliFun p (t - c) • F p t = 0 := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hcp : ContinuousOn (F p) (Set.uIcc x y) := fun t ht ↦
      (hF p (Nat.lt_add_one p) t ht).continuousWithinAt
    have h1 := ih (fun k hk t ht ↦ hF k (by omega) t ht) hcp.intervalIntegrable
    have h2 := integral_bernoulliFun_comp_sub_right_smul p (c := c)
      (hF p (Nat.lt_add_one p)) hFp
    have hfac : (((p + 1)! : ℕ) : ℝ) = ((p : ℝ) + 1) * (p ! : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hne : ((p ! : ℕ) : ℝ) ≠ 0 := by positivity
    have hA : (-1 : ℝ) ^ (p + 1) / (((p + 1)! : ℕ) : ℝ) =
        (-1 : ℝ) ^ (p + 1) / (p ! : ℝ) * ((p : ℝ) + 1)⁻¹ := by
      rw [hfac]
      field_simp
    have hB : (-1 : ℝ) ^ (p + 1 + 1) / (((p + 1)! : ℕ) : ℝ) =
        -((-1 : ℝ) ^ (p + 1) / (p ! : ℝ) * ((p : ℝ) + 1)⁻¹) := by
      rw [hfac, pow_succ]
      field_simp
    rw [h2] at h1
    rw [Finset.sum_range_succ, hA, hB]
    linear_combination (norm := module) h1

/-- If `x ≤ y` have the same integer part, the right-hand side of the Euler-Maclaurin formula over
`[x, y]` is zero: there is no integer in `(x, y]`, and the periodic Bernoulli function is a
translate of the Bernoulli polynomial on `[x, y]`. -/
private theorem rhs_eq_zero {p : ℕ} {F : ℕ → ℝ → E} {x y : ℝ} (hxy : x ≤ y) (hfl : ⌊x⌋ = ⌊y⌋)
    (hF : ∀ k < p, ∀ t ∈ Set.Icc x y, HasDerivWithinAt (F k) (F (k + 1) t) (Set.Icc x y) t)
    (hFp : IntervalIntegrable (F p) volume x y) :
    (∫ t in x..y, F 0 t) +
      ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
        (periodizedBernoulli (k + 1) y • F k y - periodizedBernoulli (k + 1) x • F k x) +
      ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • ∫ t in x..y, periodizedBernoulli p t • F p t = 0 := by
  have hx : x ∈ Set.Ico (⌊x⌋ : ℝ) (⌊x⌋ + 1) := ⟨Int.floor_le x, Int.lt_floor_add_one x⟩
  have hy : y ∈ Set.Ico (⌊x⌋ : ℝ) (⌊x⌋ + 1) := by
    rw [hfl]
    exact ⟨Int.floor_le y, Int.lt_floor_add_one y⟩
  have hmem : ∀ t ∈ Set.Icc x y, t ∈ Set.Ico (⌊x⌋ : ℝ) (⌊x⌋ + 1) := fun t ht ↦
    ⟨hx.1.trans ht.1, ht.2.trans_lt hy.2⟩
  have hint : ∫ t in x..y, periodizedBernoulli p t • F p t =
      ∫ t in x..y, bernoulliFun p (t - ⌊x⌋) • F p t := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hxy] at ht
    rw [periodizedBernoulli_coe_of_mem_Ico_intCast (hmem t ht)]
  have h := integral_add_sum_add_integral_bernoulliFun_eq_zero (c := (⌊x⌋ : ℝ)) p
    (by rw [Set.uIcc_of_le hxy]; exact hF) hFp
  rw [hint]
  simp only [periodizedBernoulli_coe_of_mem_Ico_intCast hx,
    periodizedBernoulli_coe_of_mem_Ico_intCast hy]
  exact h

/-- If `x` lies in `[m, m + 1)` and `n = m + 1`, the right-hand side of the Euler-Maclaurin formula
over `[x, n]` is `F 0 n`, the value at the one integer in `(x, n]`.  The periodic Bernoulli
function at the integer `n` is `B_k(0)`, which differs from `B_k(1)` by `1` for `k = 1` and by `0`
otherwise (`bernoulliFun_eval_one`). -/
private theorem rhs_eq_of_floor_add_one {p : ℕ} (hp : p ≠ 0) {F : ℕ → ℝ → E} {x : ℝ} {n : ℤ}
    (hn : ⌊x⌋ + 1 = n)
    (hF : ∀ k < p, ∀ t ∈ Set.Icc x (n : ℝ),
      HasDerivWithinAt (F k) (F (k + 1) t) (Set.Icc x (n : ℝ)) t)
    (hFp : IntervalIntegrable (F p) volume x (n : ℝ)) :
    (∫ t in x..(n : ℝ), F 0 t) +
      ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
        (periodizedBernoulli (k + 1) (n : ℝ) • F k n - periodizedBernoulli (k + 1) x • F k x) +
      ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • ∫ t in x..(n : ℝ), periodizedBernoulli p t • F p t =
    F 0 n := by
  have hx : x ∈ Set.Ico (⌊x⌋ : ℝ) (⌊x⌋ + 1) := ⟨Int.floor_le x, Int.lt_floor_add_one x⟩
  have hn' : (n : ℝ) = ⌊x⌋ + 1 := by exact_mod_cast hn.symm
  have hxn : x ≤ n := by
    rw [hn']
    exact hx.2.le
  have hint : ∫ t in x..(n : ℝ), periodizedBernoulli p t • F p t =
      ∫ t in x..(n : ℝ), bernoulliFun p (t - ⌊x⌋) • F p t := by
    refine intervalIntegral.integral_congr_uIoo fun t ht ↦ ?_
    rw [Set.uIoo_of_le hxn] at ht
    have hmem : t ∈ Set.Ico (⌊x⌋ : ℝ) (⌊x⌋ + 1) := ⟨hx.1.trans ht.1.le, by linarith [ht.2]⟩
    rw [periodizedBernoulli_coe_of_mem_Ico_intCast hmem]
  have h := integral_add_sum_add_integral_bernoulliFun_eq_zero (c := (⌊x⌋ : ℝ)) p
    (by rw [Set.uIcc_of_le hxn]; exact hF) hFp
  have hy1 : (n : ℝ) - ⌊x⌋ = 1 := by
    rw [hn']
    ring
  rw [hy1] at h
  have hjump : ∀ k : ℕ, bernoulliFun (k + 1) 1 =
      (bernoulli (k + 1) : ℝ) + if k = 0 then 1 else 0 := fun k ↦ by
    rw [bernoulliFun_eval_one, bernoulliFun_eval_zero]
    simp
  have hterm : ∀ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
        (bernoulliFun (k + 1) 1 • F k n - bernoulliFun (k + 1) (x - ⌊x⌋) • F k x) =
      ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
        ((bernoulli (k + 1) : ℝ) • F k n - bernoulliFun (k + 1) (x - ⌊x⌋) • F k x) +
      if k = 0 then (-1 : ℝ) • F 0 n else 0 := by
    intro k _
    rw [hjump k]
    by_cases hk : k = 0
    · subst hk
      simp only [↓reduceIte, zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
      module
    · simp [hk]
  have hdelta : ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
        ((bernoulli (k + 1) : ℝ) • F k n - bernoulliFun (k + 1) (x - ⌊x⌋) • F k x) =
      ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
        (bernoulliFun (k + 1) 1 • F k n - bernoulliFun (k + 1) (x - ⌊x⌋) • F k x) + F 0 n := by
    have h0 : 0 ∈ Finset.range p := Finset.mem_range.2 (Nat.pos_of_ne_zero hp)
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [h0, ↓reduceIte]
    module
  rw [hint]
  simp only [periodizedBernoulli_intCast, periodizedBernoulli_coe_of_mem_Ico_intCast hx]
  linear_combination (norm := module) h + hdelta

/-- The Euler-Maclaurin formula for real end points, by induction on the number `N` of integers
in `(a, b]`. -/
private theorem sum_Ioc_floor_aux {p : ℕ} (hp : p ≠ 0) {F : ℕ → ℝ → E} {a b : ℝ} (N : ℕ)
    (hab : a ≤ b) (hN : ⌊b⌋ - ⌊a⌋ = N)
    (hF : ∀ k < p, ∀ x ∈ Set.Icc a b, HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc a b) x)
    (hFp : IntervalIntegrable (F p) volume a b) :
    ∑ i ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, F 0 (i : ℝ) =
      (∫ t in a..b, F 0 t) +
        ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • F k b - periodizedBernoulli (k + 1) a • F k a) +
        ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • ∫ t in a..b, periodizedBernoulli p t • F p t := by
  induction N generalizing a with
  | zero =>
    have hfl : ⌊a⌋ = ⌊b⌋ := by omega
    rw [hfl, Finset.Ioc_self, Finset.sum_empty]
    exact (rhs_eq_zero hab hfl hF hFp).symm
  | succ N ih =>
    obtain ⟨n, hn⟩ : ∃ n : ℤ, ⌊a⌋ + 1 = n := ⟨_, rfl⟩
    have hn_le : n ≤ ⌊b⌋ := by omega
    have hnb : (n : ℝ) ≤ b := by
      have h1 : (n : ℝ) ≤ ⌊b⌋ := by exact_mod_cast hn_le
      linarith [Int.floor_le b]
    have han : a ≤ n := by
      have h : (n : ℝ) = ⌊a⌋ + 1 := by exact_mod_cast hn.symm
      rw [h]
      exact (Int.lt_floor_add_one a).le
    have hfln : ⌊(n : ℝ)⌋ = n := Int.floor_intCast n
    have hsub1 : Set.Icc a (n : ℝ) ⊆ Set.Icc a b := Set.Icc_subset_Icc_right hnb
    have hsub2 : Set.Icc (n : ℝ) b ⊆ Set.Icc a b := Set.Icc_subset_Icc_left han
    have hmem : (n : ℝ) ∈ Set.uIcc a b := Set.mem_uIcc_of_le han hnb
    have hFp1 : IntervalIntegrable (F p) volume a (n : ℝ) :=
      hFp.mono_set (Set.uIcc_subset_uIcc_left hmem)
    have hFp2 : IntervalIntegrable (F p) volume (n : ℝ) b :=
      hFp.mono_set (Set.uIcc_subset_uIcc_right hmem)
    have hc0 : ContinuousOn (F 0) (Set.Icc a b) := fun x hx ↦
      (hF 0 (Nat.pos_of_ne_zero hp) x hx).continuousWithinAt
    have hI1 : IntervalIntegrable (F 0) volume a (n : ℝ) :=
      (hc0.mono hsub1).intervalIntegrable_of_Icc han
    have hI2 : IntervalIntegrable (F 0) volume (n : ℝ) b :=
      (hc0.mono hsub2).intervalIntegrable_of_Icc hnb
    have ih' := ih (a := (n : ℝ)) hnb (by rw [hfln]; omega)
      (fun k hk x hx ↦ (hF k hk x (hsub2 hx)).mono hsub2) hFp2
    have hstep := rhs_eq_of_floor_add_one hp hn
      (fun k hk x hx ↦ (hF k hk x (hsub1 hx)).mono hsub1) hFp1
    have hsplit : Finset.Ioc ⌊a⌋ ⌊b⌋ = insert n (Finset.Ioc n ⌊b⌋) := by
      ext i
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    have hrem : ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • ∫ t in a..b, periodizedBernoulli p t • F p t =
        ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • (∫ t in a..(n : ℝ), periodizedBernoulli p t • F p t) +
        ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • ∫ t in (n : ℝ)..b, periodizedBernoulli p t • F p t := by
      rw [← smul_add, intervalIntegral.integral_add_adjacent_intervals
        hFp1.periodizedBernoulli_smul hFp2.periodizedBernoulli_smul]
    have hbd : ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • F k b - periodizedBernoulli (k + 1) a • F k a) =
        ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • F k b - periodizedBernoulli (k + 1) (n : ℝ) • F k n) +
        ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) (n : ℝ) • F k n -
            periodizedBernoulli (k + 1) a • F k a) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [← smul_add]
      congr 1
      abel
    rw [hfln] at ih'
    rw [hsplit, Finset.sum_insert (by simp),
      ← intervalIntegral.integral_add_adjacent_intervals hI1 hI2, hrem, hbd]
    linear_combination (norm := module) ih' - hstep

/-- **The Euler-Maclaurin summation formula** for real end points, for a family `F : ℕ → ℝ → E` of
successive derivatives.  Let `a ≤ b` be real numbers, `p ≥ 1`, and suppose that for `k < p` the
function `F k` has derivative `F (k + 1)` within `[a, b]`, and that `F p` is interval integrable on
`[a, b]`.  Then the sum of `F 0 i` over the integers `i ∈ (a, b]` equals
$$\int_a^b F_0 + \sum_{k < p} \frac{(-1)^{k + 1}}{(k + 1)!}
  \bigl(P_{k + 1}(b) F_k(b) - P_{k + 1}(a) F_k(a)\bigr)
  + \frac{(-1)^{p + 1}}{p!} \int_a^b P_p F_p,$$
where `P_n = periodizedBernoulli n`, evaluated at the class of a real number. -/
theorem sum_Ioc_eq_integral_add_of_hasDerivWithinAt {p : ℕ} (hp : p ≠ 0) {F : ℕ → ℝ → E}
    {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ k < p, ∀ x ∈ Set.Icc a b, HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc a b) x)
    (hFp : IntervalIntegrable (F p) volume a b) :
    ∑ i ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, F 0 (i : ℝ) =
      (∫ t in a..b, F 0 t) +
        ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • F k b - periodizedBernoulli (k + 1) a • F k a) +
        ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • ∫ t in a..b, periodizedBernoulli p t • F p t :=
  sum_Ioc_floor_aux hp (⌊b⌋ - ⌊a⌋).toNat hab
    (Int.toNat_of_nonneg (sub_nonneg.2 (Int.floor_mono hab))).symm hF hFp

/-- **The Euler-Maclaurin summation formula** for real end points and a `C^p` function.  Let
`a ≤ b` be real numbers and `p ≥ 1`.  If `f` is `C^p` on `[a, b]`, then the sum of `f i` over the
integers `i ∈ (a, b]` equals
$$\int_a^b f + \sum_{k < p} \frac{(-1)^{k + 1}}{(k + 1)!}
  \bigl(P_{k + 1}(b) f^{(k)}(b) - P_{k + 1}(a) f^{(k)}(a)\bigr)
  + \frac{(-1)^{p + 1}}{p!} \int_a^b P_p f^{(p)},$$
where `P_n = periodizedBernoulli n` and the derivatives `f^(k)` are `iteratedDerivWithin` on
`[a, b]`. -/
theorem sum_Ioc_eq_integral_add {f : ℝ → E} {p : ℕ} (hp : p ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ p f (Set.Icc a b)) :
    ∑ i ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, f (i : ℝ) =
      (∫ t in a..b, f t) +
        ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • iteratedDerivWithin k f (Set.Icc a b) b -
            periodizedBernoulli (k + 1) a • iteratedDerivWithin k f (Set.Icc a b) a) +
        ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • ∫ t in a..b,
          periodizedBernoulli p t • iteratedDerivWithin p f (Set.Icc a b) t := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  · have hU : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hlt
    simpa only [iteratedDerivWithin_zero] using
      sum_Ioc_eq_integral_add_of_hasDerivWithinAt
        (F := fun k ↦ iteratedDerivWithin k f (Set.Icc a b)) hp hab
        (fun k hk x hx ↦ hf.hasDerivWithinAt_iteratedDerivWithin (by exact_mod_cast hk) hU hx)
        ((hf.continuousOn_iteratedDerivWithin le_rfl hU).intervalIntegrable_of_Icc hab)

/-- A sum over a finite set `t` of integers is the sum over a finite set `s` of natural numbers if
the cast maps `s` onto `t`.  This reindexes sums over `Finset.Ioc` and `Finset.Icc`, with
`Nat.image_cast_int_Ioc` and `Nat.image_cast_int_Icc`. -/
private theorem sum_intCast_eq_sum {G : Type*} [AddCommMonoid G] (f : ℤ → G) {s : Finset ℕ}
    {t : Finset ℤ} (h : Nat.cast '' (s : Set ℕ) = (t : Set ℤ)) :
    ∑ i ∈ t, f i = ∑ i ∈ s, f i := by
  have ht : t = s.image (Nat.cast : ℕ → ℤ) :=
    Finset.coe_injective (by rw [Finset.coe_image]; exact h.symm)
  rw [ht, Finset.sum_image (fun x _ y _ hxy ↦ by exact_mod_cast hxy)]

/-- **The Euler-Maclaurin summation formula** for a sum over natural numbers, for a family
`F : ℕ → ℝ → E` of successive derivatives: the case of
`EulerMaclaurin.sum_Ioc_eq_integral_add_of_hasDerivWithinAt` with `0 ≤ a`, in which the integers
in `(a, b]` are the natural numbers in `(⌊a⌋₊, ⌊b⌋₊]`. -/
theorem sum_Ioc_natFloor_eq_integral_add_of_hasDerivWithinAt {p : ℕ} (hp : p ≠ 0) {F : ℕ → ℝ → E}
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hF : ∀ k < p, ∀ x ∈ Set.Icc a b, HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc a b) x)
    (hFp : IntervalIntegrable (F p) volume a b) :
    ∑ i ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, F 0 (i : ℝ) =
      (∫ t in a..b, F 0 t) +
        ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • F k b - periodizedBernoulli (k + 1) a • F k a) +
        ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • ∫ t in a..b, periodizedBernoulli p t • F p t := by
  have h := sum_Ioc_eq_integral_add_of_hasDerivWithinAt hp hab hF hFp
  rw [← Int.natCast_floor_eq_floor ha, ← Int.natCast_floor_eq_floor (ha.trans hab),
    sum_intCast_eq_sum (fun i : ℤ ↦ F 0 (i : ℝ))] at h
  · simpa only [Int.cast_natCast] using h
  · simpa only [Finset.coe_Ioc] using Nat.image_cast_int_Ioc _ _

/-- **The Euler-Maclaurin summation formula** for a sum over natural numbers and a `C^p` function:
the case of `EulerMaclaurin.sum_Ioc_eq_integral_add` with `0 ≤ a`, in which the integers in
`(a, b]` are the natural numbers in `(⌊a⌋₊, ⌊b⌋₊]`. -/
theorem sum_Ioc_natFloor_eq_integral_add {f : ℝ → E} {p : ℕ} (hp : p ≠ 0) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hf : ContDiffOn ℝ p f (Set.Icc a b)) :
    ∑ i ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f (i : ℝ) =
      (∫ t in a..b, f t) +
        ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • iteratedDerivWithin k f (Set.Icc a b) b -
            periodizedBernoulli (k + 1) a • iteratedDerivWithin k f (Set.Icc a b) a) +
        ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • ∫ t in a..b,
          periodizedBernoulli p t • iteratedDerivWithin p f (Set.Icc a b) t := by
  have h := sum_Ioc_eq_integral_add hp hab hf
  rw [← Int.natCast_floor_eq_floor ha, ← Int.natCast_floor_eq_floor (ha.trans hab),
    sum_intCast_eq_sum (fun i : ℤ ↦ f (i : ℝ))] at h
  · simpa only [Int.cast_natCast] using h
  · simpa only [Finset.coe_Ioc] using Nat.image_cast_int_Ioc _ _

omit [CompleteSpace E] in
/-- At integer end points the coefficients `(-1)^(k+1) B_{k+1} / (k+1)!` of the boundary terms
are `B'_{k+1} / (k+1)!`, where `B'_n = (-1)^n B_n` is `bernoulli'`. -/
private theorem sum_bernoulli'_smul_sub {p : ℕ} (u v : ℕ → E) :
    ∑ k ∈ Finset.range p, ((bernoulli' (k + 1) : ℝ) / ((k + 1)! : ℝ)) • (u k - v k) =
      ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
        ((bernoulli (k + 1) : ℝ) • u k - (bernoulli (k + 1) : ℝ) • v k) := by
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [bernoulli'_eq_bernoulli]
  push_cast
  module

/-- **The Euler-Maclaurin summation formula** for integer end points, for a family
`F : ℕ → ℝ → E` of successive derivatives.  Let `a ≤ b` be integers, `p ≥ 1`, and suppose that for
`k < p` the function `F k` has derivative `F (k + 1)` within `[a, b]`, and that `F p` is interval
integrable on `[a, b]`.  Then `∑ i ∈ Finset.Ioc a b, F 0 i` equals
$$\int_a^b F_0 + \sum_{k < p} \frac{B'_{k + 1}}{(k + 1)!} (F_k(b) - F_k(a))
  + \frac{(-1)^{p + 1}}{p!} \int_a^b P_p F_p,$$
where `B'_n = bernoulli' n` and `P_p = periodizedBernoulli p`. -/
theorem sum_Ioc_int_eq_integral_add_of_hasDerivWithinAt {p : ℕ} (hp : p ≠ 0) {F : ℕ → ℝ → E}
    {a b : ℤ} (hab : a ≤ b)
    (hF : ∀ k < p, ∀ x ∈ Set.Icc (a : ℝ) b,
      HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc (a : ℝ) b) x)
    (hFp : IntervalIntegrable (F p) volume (a : ℝ) b) :
    ∑ i ∈ Finset.Ioc a b, F 0 (i : ℝ) =
      (∫ t in (a : ℝ)..b, F 0 t) +
        ∑ k ∈ Finset.range p, ((bernoulli' (k + 1) : ℝ) / ((k + 1)! : ℝ)) • (F k b - F k a) +
        ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • ∫ t in (a : ℝ)..b, periodizedBernoulli p t • F p t := by
  have h := sum_Ioc_eq_integral_add_of_hasDerivWithinAt hp (a := (a : ℝ)) (b := (b : ℝ))
    (by exact_mod_cast hab) hF hFp
  simp only [Int.floor_intCast, periodizedBernoulli_intCast] at h
  rw [sum_bernoulli'_smul_sub]
  exact h

/-- **The Euler-Maclaurin summation formula** for integer end points and a `C^p` function.  Let
`a ≤ b` be integers and `p ≥ 1`.  If `f` is `C^p` on `[a, b]`, then `∑ i ∈ Finset.Ioc a b, f i`
equals
$$\int_a^b f + \sum_{k < p} \frac{B'_{k + 1}}{(k + 1)!} (f^{(k)}(b) - f^{(k)}(a))
  + \frac{(-1)^{p + 1}}{p!} \int_a^b P_p f^{(p)},$$
where `B'_n = bernoulli' n`, `P_p = periodizedBernoulli p` and the derivatives `f^(k)` are
`iteratedDerivWithin` on `[a, b]`. -/
theorem sum_Ioc_int_eq_integral_add {f : ℝ → E} {p : ℕ} (hp : p ≠ 0) {a b : ℤ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ p f (Set.Icc (a : ℝ) b)) :
    ∑ i ∈ Finset.Ioc a b, f (i : ℝ) =
      (∫ t in (a : ℝ)..b, f t) +
        ∑ k ∈ Finset.range p, ((bernoulli' (k + 1) : ℝ) / ((k + 1)! : ℝ)) •
          (iteratedDerivWithin k f (Set.Icc (a : ℝ) b) b -
            iteratedDerivWithin k f (Set.Icc (a : ℝ) b) a) +
        ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • ∫ t in (a : ℝ)..b,
          periodizedBernoulli p t • iteratedDerivWithin p f (Set.Icc (a : ℝ) b) t := by
  have h := sum_Ioc_eq_integral_add hp (a := (a : ℝ)) (b := (b : ℝ)) (by exact_mod_cast hab) hf
  simp only [Int.floor_intCast, periodizedBernoulli_intCast] at h
  rw [sum_bernoulli'_smul_sub]
  exact h

/-- **The Euler-Maclaurin summation formula over `Finset.Icc`** for integer end points, for a
family `F : ℕ → ℝ → E` of successive derivatives.  Let `a ≤ b` be integers, `p ≥ 1`, and suppose
that for `k < p` the function `F k` has derivative `F (k + 1)` within `[a, b]`, and that `F p` is
interval integrable on `[a, b]`.  Then `∑ i ∈ Finset.Icc a b, F 0 i` equals
$$\int_a^b F_0 + \frac{F_0(a) + F_0(b)}{2}
  + \sum_{j < \lfloor p / 2 \rfloor} \frac{B_{2j + 2}}{(2j + 2)!}
    (F_{2j + 1}(b) - F_{2j + 1}(a))
  + \frac{(-1)^{p + 1}}{p!} \int_a^b P_p F_p,$$
where `P_p = periodizedBernoulli p`.  The odd Bernoulli numbers have been removed from the
boundary terms of `EulerMaclaurin.sum_Ioc_int_eq_integral_add_of_hasDerivWithinAt` with
`sum_range_bernoulli'_div_factorial_smul`. -/
theorem sum_Icc_int_eq_integral_add_of_hasDerivWithinAt {p : ℕ} (hp : p ≠ 0) {F : ℕ → ℝ → E}
    {a b : ℤ} (hab : a ≤ b)
    (hF : ∀ k < p, ∀ x ∈ Set.Icc (a : ℝ) b,
      HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc (a : ℝ) b) x)
    (hFp : IntervalIntegrable (F p) volume (a : ℝ) b) :
    ∑ i ∈ Finset.Icc a b, F 0 (i : ℝ) =
      (∫ t in (a : ℝ)..b, F 0 t) + (1 / 2 : ℝ) • (F 0 a + F 0 b) +
        ∑ j ∈ Finset.range (p / 2), ((bernoulli (2 * j + 2) : ℝ) / ((2 * j + 2)! : ℝ)) •
          (F (2 * j + 1) b - F (2 * j + 1) a) +
        ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • ∫ t in (a : ℝ)..b, periodizedBernoulli p t • F p t := by
  have h := sum_Ioc_int_eq_integral_add_of_hasDerivWithinAt hp hab hF hFp
  rw [sum_range_bernoulli'_div_factorial_smul hp (fun k ↦ F k b - F k a)] at h
  rw [Finset.Icc_eq_cons_Ioc hab, Finset.sum_cons]
  linear_combination (norm := module) h

/-- **The Euler-Maclaurin summation formula over `Finset.Icc`** for integer end points and a `C^p`
function.  Let `a ≤ b` be integers and `p ≥ 1`.  If `f` is `C^p` on `[a, b]`, then
`∑ i ∈ Finset.Icc a b, f i` equals
$$\int_a^b f + \frac{f(a) + f(b)}{2}
  + \sum_{j < \lfloor p / 2 \rfloor} \frac{B_{2j + 2}}{(2j + 2)!}
    (f^{(2j + 1)}(b) - f^{(2j + 1)}(a))
  + \frac{(-1)^{p + 1}}{p!} \int_a^b P_p f^{(p)},$$
where `P_p = periodizedBernoulli p` and the derivatives `f^(k)` are `iteratedDerivWithin` on
`[a, b]`. -/
theorem sum_Icc_int_eq_integral_add {f : ℝ → E} {p : ℕ} (hp : p ≠ 0) {a b : ℤ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ p f (Set.Icc (a : ℝ) b)) :
    ∑ i ∈ Finset.Icc a b, f (i : ℝ) =
      (∫ t in (a : ℝ)..b, f t) + (1 / 2 : ℝ) • (f a + f b) +
        ∑ j ∈ Finset.range (p / 2), ((bernoulli (2 * j + 2) : ℝ) / ((2 * j + 2)! : ℝ)) •
          (iteratedDerivWithin (2 * j + 1) f (Set.Icc (a : ℝ) b) b -
            iteratedDerivWithin (2 * j + 1) f (Set.Icc (a : ℝ) b) a) +
        ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • ∫ t in (a : ℝ)..b,
          periodizedBernoulli p t • iteratedDerivWithin p f (Set.Icc (a : ℝ) b) t := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp only [Finset.Icc_self, Finset.sum_singleton, intervalIntegral.integral_same, sub_self,
      smul_zero, Finset.sum_const_zero, add_zero, zero_add]
    module
  · have hlt' : (a : ℝ) < b := by exact_mod_cast hlt
    have hU : UniqueDiffOn ℝ (Set.Icc (a : ℝ) b) := uniqueDiffOn_Icc hlt'
    simpa only [iteratedDerivWithin_zero] using
      sum_Icc_int_eq_integral_add_of_hasDerivWithinAt
        (F := fun k ↦ iteratedDerivWithin k f (Set.Icc (a : ℝ) b)) hp hab
        (fun k hk x hx ↦ hf.hasDerivWithinAt_iteratedDerivWithin (by exact_mod_cast hk) hU hx)
        ((hf.continuousOn_iteratedDerivWithin le_rfl hU).intervalIntegrable_of_Icc hlt'.le)

/-- **The Euler-Maclaurin summation formula over `Finset.Icc`** for end points in `ℕ`, for a family
`F : ℕ → ℝ → E` of successive derivatives: the case of
`EulerMaclaurin.sum_Icc_int_eq_integral_add_of_hasDerivWithinAt` with end points `a ≤ b` in `ℕ`. -/
theorem sum_Icc_nat_eq_integral_add_of_hasDerivWithinAt {p : ℕ} (hp : p ≠ 0) {F : ℕ → ℝ → E}
    {a b : ℕ} (hab : a ≤ b)
    (hF : ∀ k < p, ∀ x ∈ Set.Icc (a : ℝ) b,
      HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc (a : ℝ) b) x)
    (hFp : IntervalIntegrable (F p) volume (a : ℝ) b) :
    ∑ i ∈ Finset.Icc a b, F 0 (i : ℝ) =
      (∫ t in (a : ℝ)..b, F 0 t) + (1 / 2 : ℝ) • (F 0 a + F 0 b) +
        ∑ j ∈ Finset.range (p / 2), ((bernoulli (2 * j + 2) : ℝ) / ((2 * j + 2)! : ℝ)) •
          (F (2 * j + 1) b - F (2 * j + 1) a) +
        ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • ∫ t in (a : ℝ)..b, periodizedBernoulli p t • F p t := by
  have h := sum_Icc_int_eq_integral_add_of_hasDerivWithinAt hp (F := F) (a := (a : ℤ))
    (b := (b : ℤ)) (by exact_mod_cast hab) (by simpa only [Int.cast_natCast] using hF)
    (by simpa only [Int.cast_natCast] using hFp)
  simp only [Int.cast_natCast] at h
  rw [sum_intCast_eq_sum (fun i : ℤ ↦ F 0 (i : ℝ))] at h
  · simpa only [Int.cast_natCast] using h
  · simpa only [Finset.coe_Icc] using Nat.image_cast_int_Icc _ _

/-- **The Euler-Maclaurin summation formula over `Finset.Icc`** for end points in `ℕ` and a `C^p`
function: the case of `EulerMaclaurin.sum_Icc_int_eq_integral_add` with end points `a ≤ b` in
`ℕ`. -/
theorem sum_Icc_nat_eq_integral_add {f : ℝ → E} {p : ℕ} (hp : p ≠ 0) {a b : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ p f (Set.Icc (a : ℝ) b)) :
    ∑ i ∈ Finset.Icc a b, f (i : ℝ) =
      (∫ t in (a : ℝ)..b, f t) + (1 / 2 : ℝ) • (f a + f b) +
        ∑ j ∈ Finset.range (p / 2), ((bernoulli (2 * j + 2) : ℝ) / ((2 * j + 2)! : ℝ)) •
          (iteratedDerivWithin (2 * j + 1) f (Set.Icc (a : ℝ) b) b -
            iteratedDerivWithin (2 * j + 1) f (Set.Icc (a : ℝ) b) a) +
        ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • ∫ t in (a : ℝ)..b,
          periodizedBernoulli p t • iteratedDerivWithin p f (Set.Icc (a : ℝ) b) t := by
  have h := sum_Icc_int_eq_integral_add hp (a := (a : ℤ)) (b := (b : ℤ)) (by exact_mod_cast hab)
    (by simpa only [Int.cast_natCast] using hf)
  simp only [Int.cast_natCast] at h
  rw [sum_intCast_eq_sum (fun i : ℤ ↦ f (i : ℝ))] at h
  · simpa only [Int.cast_natCast] using h
  · simpa only [Finset.coe_Icc] using Nat.image_cast_int_Icc _ _

end EulerMaclaurin
