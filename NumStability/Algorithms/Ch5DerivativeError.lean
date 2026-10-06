-- Algorithms/Ch5DerivativeError.lean
--
-- Higham, 2nd ed., Chapter 5, Section 5.2, Algorithm 5.2 (evaluation of a
-- polynomial and its first derivative by the extended Horner / synthetic
-- division scheme) rounding analysis, packaged from the descending-coefficient
-- Horner infrastructure in `Algorithms/Horner.lean`.
--
-- This file is IMPORT-ONLY over the existing Horner development: it does not
-- re-prove the coupled backward/forward analysis but assembles it into the
-- printed-strength statements for Algorithm 5.2, and it proves the sign-pattern
-- corollary of the a-priori forward bound (5.3) for Algorithm 5.1
-- (the collapse `psi(p,x) = 1`), which is not present upstream.

import NumStability.Algorithms.Horner

namespace NumStability

open scoped BigOperators

/-!
## Notation

Coefficients are stored in descending order `[a_n, a_{n-1}, ..., a_0]`, matching
`Horner.lean`.  For such a list `c` of length `n + 1`:

* `polyDesc x c = a_n x^n + ... + a_0` is `p(x)`               (Higham (5.1));
* `polyDescAbs x c = |a_n| |x|^n + ... + |a_0|` is `p~(|x|)`   (Higham (5.3));
* `polyDescDeriv x c = p'(x)` and `polyDescDerivAbs x c = p~'(|x|)`;
* the rounded Algorithm 5.2 output is `fl_hornerDerivativeDesc fp x c`, whose
  first component is the rounded value `fl(p(x))` and whose second component is
  the rounded first derivative.

The relevant "number of operations" constant is `2 n = 2 (c.length - 1)`.
-/

/-! ## Algorithm 5.2: forward/backward error for value and first derivative -/

/-- Higham (5.7), value component.  Algorithm 5.2's rounded value output is the
rounded Horner value, and its forward error is the ordinary `gamma_(2n)` Horner
bound (5.3). -/
theorem ch5deriv_value_forward_error_bound
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |(fl_hornerDerivativeDesc fp x coeffsDesc).1 - polyDesc x coeffsDesc| ≤
      gamma fp (2 * (coeffsDesc.length - 1)) * polyDescAbs x coeffsDesc := by
  rw [fl_hornerDerivativeDesc_fst_eq_fl_hornerDesc]
  exact fl_hornerDesc_forward_error_bound fp x coeffsDesc hvalid

/-- Higham (5.7), first-derivative component.  The rounded Algorithm 5.2
derivative output differs from the exact derivative `p'(x)` by at most
`gamma_(2n) * p~'(|x|)`, keeping the value and derivative recurrences coupled so
that every coefficient perturbation stays inside a single `gamma_(2n)`
envelope. -/
theorem ch5deriv_derivative_forward_error_bound
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |(fl_hornerDerivativeDesc fp x coeffsDesc).2 - polyDescDeriv x coeffsDesc| ≤
      gamma fp (2 * (coeffsDesc.length - 1)) * polyDescDerivAbs x coeffsDesc :=
  fl_hornerDerivativeDesc_snd_forward_error_bound_coupled fp x coeffsDesc hvalid

/-- Higham (5.7), coefficientwise backward-error form for the first derivative.
The rounded Algorithm 5.2 derivative output is the exact formal derivative of a
polynomial whose coefficients are each perturbed by a relative factor of size at
most `gamma_(2n)`. -/
theorem ch5deriv_derivative_backward_error_coefficients
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    ∃ pairs : List (ℝ × ℝ),
      pairs.map Prod.fst = coeffsDesc ∧
      (∀ p ∈ pairs, |p.2| ≤ gamma fp (2 * (coeffsDesc.length - 1))) ∧
      (fl_hornerDerivativeDesc fp x coeffsDesc).2 =
        polyDescPairsDerivPerturbed x pairs :=
  fl_hornerDerivativeDesc_snd_backward_error_coefficients_coupled
    fp x coeffsDesc hvalid

/-- Full Algorithm 5.2 (value and first derivative) forward-error theorem: both
outputs of the coupled rounded extended-Horner recurrence are simultaneously
bounded by their respective `gamma_(2n)` absolute-coefficient majorants.  This
is the packaged printed-strength statement of the §5.2 rounding analysis. -/
theorem ch5deriv_pair_forward_error_bound
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |(fl_hornerDerivativeDesc fp x coeffsDesc).1 - polyDesc x coeffsDesc| ≤
        gamma fp (2 * (coeffsDesc.length - 1)) * polyDescAbs x coeffsDesc ∧
      |(fl_hornerDerivativeDesc fp x coeffsDesc).2 -
          polyDescDeriv x coeffsDesc| ≤
        gamma fp (2 * (coeffsDesc.length - 1)) *
          polyDescDerivAbs x coeffsDesc :=
  ⟨ch5deriv_value_forward_error_bound fp x coeffsDesc hvalid,
    ch5deriv_derivative_forward_error_bound fp x coeffsDesc hvalid⟩

/-- Higham (5.7), first-order display of the derivative bound.  The leading
term is the printed `2 n u * p~'(|x|)`; the explicit quadratic-and-higher
remainder is `((2 n u)^2 / (1 - 2 n u)) * p~'(|x|)` and vanishes when `u = 0`. -/
theorem ch5deriv_derivative_first_order_error_bound
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |(fl_hornerDerivativeDesc fp x coeffsDesc).2 - polyDescDeriv x coeffsDesc| ≤
      (((2 * (coeffsDesc.length - 1) : ℕ) : ℝ) * fp.u) *
          polyDescDerivAbs x coeffsDesc +
        fl_hornerDerivativeDescFirstOrderRemainder fp x coeffsDesc :=
  fl_hornerDerivativeDesc_first_derivative_error_bound fp x coeffsDesc hvalid

/-! ## Section 5.1 / equation (5.3): the sign-pattern corollary `psi(p,x) = 1`

Higham (5.3) bounds the relative error of Horner's method (Algorithm 5.1) by
`gamma_(2n) * psi(p,x)`, where `psi(p,x) = p~(|x|) / |p(x)|` can be arbitrarily
large.  The book notes that `psi(p,x) = 1` — perfect relative accuracy up to
`gamma_(2n)` — precisely when `a_i >= 0` for all `i` and `x >= 0`, or when
`(-1)^i a_i >= 0` for all `i` and `x <= 0`.  We formalize both sign patterns and
derive the collapsed relative bound `|fl(p(x)) - p(x)| <= gamma_(2n) |p(x)|`. -/

/-- Nonnegative-coefficient sign pattern: with `x >= 0` and every coefficient
nonnegative, every monomial `a_i x^i` equals `|a_i| |x|^i`, so the exact value
already equals its absolute-coefficient majorant. -/
theorem ch5psi_polyDesc_eq_polyDescAbs_of_nonneg
    (x : ℝ) (hx : 0 ≤ x) :
    ∀ coeffsDesc : List ℝ, (∀ a ∈ coeffsDesc, 0 ≤ a) →
      polyDesc x coeffsDesc = polyDescAbs x coeffsDesc := by
  intro coeffsDesc
  induction coeffsDesc with
  | nil =>
      intro _
      simp [polyDesc, polyDescAbs]
  | cons a rest ih =>
      intro hcoeff
      have ha : 0 ≤ a := hcoeff a (by simp)
      have hrest : ∀ b ∈ rest, 0 ≤ b := fun b hb => hcoeff b (by simp [hb])
      have hterm :
          a * x ^ rest.length = |a| * |x| ^ rest.length := by
        rw [abs_of_nonneg ha, abs_of_nonneg hx]
      simp only [polyDesc, polyDescAbs]
      rw [hterm, ih hrest]

/-- Alternating sign pattern, structural form for descending coefficients: the
head coefficient `a` (the coefficient of `x^(rest.length)`) satisfies
`(-1)^(rest.length) a >= 0`, and the tail alternates recursively.  This encodes
Higham's `(-1)^i a_i >= 0` in descending-list order. -/
def ch5psi_AlternatingSignDesc : List ℝ → Prop
  | [] => True
  | a :: rest =>
      0 ≤ (-1 : ℝ) ^ rest.length * a ∧ ch5psi_AlternatingSignDesc rest

/-- Alternating-coefficient sign pattern: with `x <= 0` and `(-1)^i a_i >= 0`,
every monomial `a_i x^i` again equals `|a_i| |x|^i`, so the exact value equals
its absolute-coefficient majorant. -/
theorem ch5psi_polyDesc_eq_polyDescAbs_of_alternating
    (x : ℝ) (hx : x ≤ 0) :
    ∀ coeffsDesc : List ℝ, ch5psi_AlternatingSignDesc coeffsDesc →
      polyDesc x coeffsDesc = polyDescAbs x coeffsDesc := by
  intro coeffsDesc
  induction coeffsDesc with
  | nil =>
      intro _
      simp [polyDesc, polyDescAbs]
  | cons a rest ih =>
      intro halt
      obtain ⟨hhead, htail⟩ := halt
      -- `|x|^k = (-1)^k x^k` since `x ≤ 0`.
      have hxabs : |x| = (-1 : ℝ) * x := by
        rw [abs_of_nonpos hx]; ring
      have hxpow :
          |x| ^ rest.length = (-1 : ℝ) ^ rest.length * x ^ rest.length := by
        rw [hxabs, mul_pow]
      -- `|a| = (-1)^k a` from `(-1)^k a ≥ 0`.
      have hsign_abs : |(-1 : ℝ) ^ rest.length * a| = (-1 : ℝ) ^ rest.length * a :=
        abs_of_nonneg hhead
      have habs_pow : |(-1 : ℝ) ^ rest.length| = 1 := by
        rw [abs_pow, abs_neg, abs_one, one_pow]
      have haabs : |a| = (-1 : ℝ) ^ rest.length * a := by
        rw [abs_mul, habs_pow, one_mul] at hsign_abs
        exact hsign_abs
      have hsq : (-1 : ℝ) ^ rest.length * (-1 : ℝ) ^ rest.length = 1 := by
        rw [← mul_pow]
        simp
      have hterm :
          a * x ^ rest.length = |a| * |x| ^ rest.length := by
        rw [haabs, hxpow]
        calc
          a * x ^ rest.length
              = 1 * (a * x ^ rest.length) := by ring
          _ = ((-1 : ℝ) ^ rest.length * (-1 : ℝ) ^ rest.length) *
                (a * x ^ rest.length) := by rw [hsq]
          _ = (-1 : ℝ) ^ rest.length * a *
                ((-1 : ℝ) ^ rest.length * x ^ rest.length) := by ring
      simp only [polyDesc, polyDescAbs]
      rw [hterm, ih htail]

/-- Under either favorable sign pattern the exact value is nonnegative and its
magnitude equals the absolute-coefficient majorant: `p~(|x|) = |p(x)|`, i.e.
`psi(p,x) = 1`. -/
theorem ch5psi_polyDescAbs_eq_abs_polyDesc_of_nonneg
    (x : ℝ) (hx : 0 ≤ x) (coeffsDesc : List ℝ)
    (hcoeff : ∀ a ∈ coeffsDesc, 0 ≤ a) :
    polyDescAbs x coeffsDesc = |polyDesc x coeffsDesc| := by
  have heq := ch5psi_polyDesc_eq_polyDescAbs_of_nonneg x hx coeffsDesc hcoeff
  rw [heq, abs_of_nonneg (polyDescAbs_nonneg x coeffsDesc)]

theorem ch5psi_polyDescAbs_eq_abs_polyDesc_of_alternating
    (x : ℝ) (hx : x ≤ 0) (coeffsDesc : List ℝ)
    (halt : ch5psi_AlternatingSignDesc coeffsDesc) :
    polyDescAbs x coeffsDesc = |polyDesc x coeffsDesc| := by
  have heq := ch5psi_polyDesc_eq_polyDescAbs_of_alternating x hx coeffsDesc halt
  rw [heq, abs_of_nonneg (polyDescAbs_nonneg x coeffsDesc)]

/-- Higham (5.3), nonnegative-coefficient corollary.  When `a_i >= 0` for all `i`
and `x >= 0`, the a-priori forward bound collapses to a relative bound with
factor exactly `gamma_(2n)` (perfect relative accuracy, `psi = 1`):
`|fl(p(x)) - p(x)| <= gamma_(2n) |p(x)|`. -/
theorem ch5psi_hornerDesc_relative_error_of_nonneg
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) (hx : 0 ≤ x)
    (hcoeff : ∀ a ∈ coeffsDesc, 0 ≤ a)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |fl_hornerDesc fp x coeffsDesc - polyDesc x coeffsDesc| ≤
      gamma fp (2 * (coeffsDesc.length - 1)) * |polyDesc x coeffsDesc| := by
  have hbound := fl_hornerDesc_forward_error_bound fp x coeffsDesc hvalid
  rwa [ch5psi_polyDescAbs_eq_abs_polyDesc_of_nonneg x hx coeffsDesc hcoeff]
    at hbound

/-- Higham (5.3), alternating-coefficient corollary.  When `(-1)^i a_i >= 0` for
all `i` and `x <= 0`, the a-priori forward bound again collapses to
`|fl(p(x)) - p(x)| <= gamma_(2n) |p(x)|` (`psi = 1`). -/
theorem ch5psi_hornerDesc_relative_error_of_alternating
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) (hx : x ≤ 0)
    (halt : ch5psi_AlternatingSignDesc coeffsDesc)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |fl_hornerDesc fp x coeffsDesc - polyDesc x coeffsDesc| ≤
      gamma fp (2 * (coeffsDesc.length - 1)) * |polyDesc x coeffsDesc| := by
  have hbound := fl_hornerDesc_forward_error_bound fp x coeffsDesc hvalid
  rwa [ch5psi_polyDescAbs_eq_abs_polyDesc_of_alternating x hx coeffsDesc halt]
    at hbound

/-- Explicit relative-error form of the nonnegative-coefficient corollary: when
`p(x) > 0` the relative error is bounded by `gamma_(2n)` (i.e. `psi = 1`). -/
theorem ch5psi_hornerDesc_relative_error_div_of_nonneg
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ) (hx : 0 ≤ x)
    (hcoeff : ∀ a ∈ coeffsDesc, 0 ≤ a)
    (hpos : 0 < polyDesc x coeffsDesc)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |fl_hornerDesc fp x coeffsDesc - polyDesc x coeffsDesc| /
        |polyDesc x coeffsDesc| ≤
      gamma fp (2 * (coeffsDesc.length - 1)) := by
  have hbound :=
    ch5psi_hornerDesc_relative_error_of_nonneg fp x coeffsDesc hx hcoeff hvalid
  have hposabs : 0 < |polyDesc x coeffsDesc| := by
    rw [abs_of_pos hpos]; exact hpos
  rw [div_le_iff₀ hposabs]
  linarith [hbound]

end NumStability
