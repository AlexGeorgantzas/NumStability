import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter05.Problem01.DifferentiatedHorner.Basic
import NumStability.Source.Higham.Chapter05.Section01.Horner.Basic

/-!
# Chapter05 Section02 DerivativeError Basic

Canonical destination for material split out of
`NumStability.Algorithms.Ch5DerivativeError` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

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
