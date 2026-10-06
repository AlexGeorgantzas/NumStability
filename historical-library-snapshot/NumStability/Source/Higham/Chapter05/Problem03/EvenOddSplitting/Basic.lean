import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.PolynomialEvaluation.ElementaryErrorBounds
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter05.Section01.Horner.Basic

/-!
# Chapter05 Problem03 EvenOddSplitting Basic

Canonical destination for material split out of
`NumStability.Algorithms.Horner` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

mutual
  /-- Even-indexed coefficients from an ascending coefficient list. -/
  def evenCoeffsAsc : List ℝ → List ℝ
    | [] => []
    | a :: rest => a :: oddCoeffsAsc rest

  /-- Odd-indexed coefficients from an ascending coefficient list. -/
  def oddCoeffsAsc : List ℝ → List ℝ
    | [] => []
    | _a :: rest => evenCoeffsAsc rest
end

/-- Higham, 2nd ed., Problem 5.3: exact even/odd decomposition
`p(x) = p_even(x^2) + x*p_odd(x^2)`, for ascending coefficients. -/
theorem polyAsc_evenOdd_split (x : ℝ) :
    ∀ coeffsAsc : List ℝ,
      polyAsc x coeffsAsc =
        polyAsc (x * x) (evenCoeffsAsc coeffsAsc) +
          x * polyAsc (x * x) (oddCoeffsAsc coeffsAsc) := by
  intro coeffsAsc
  induction coeffsAsc with
  | nil =>
      simp [polyAsc, evenCoeffsAsc, oddCoeffsAsc]
  | cons a rest ih =>
      simp only [polyAsc, evenCoeffsAsc, oddCoeffsAsc]
      rw [ih]
      ring

/-- Exact even/odd split evaluator. -/
noncomputable def evenOddSplitEvalAsc (x : ℝ) (coeffsAsc : List ℝ) : ℝ :=
  polyAsc (x * x) (evenCoeffsAsc coeffsAsc) +
    x * polyAsc (x * x) (oddCoeffsAsc coeffsAsc)

theorem evenOddSplitEvalAsc_eq_polyAsc
    (x : ℝ) (coeffsAsc : List ℝ) :
    evenOddSplitEvalAsc x coeffsAsc = polyAsc x coeffsAsc := by
  unfold evenOddSplitEvalAsc
  rw [← polyAsc_evenOdd_split x coeffsAsc]

/-- Rounded even/odd split evaluation: form `yhat = fl(x*x)`, evaluate the even
and odd coefficient lists by Horner at `yhat`, then compute
`fl(even + fl(x*odd))`. -/
noncomputable def fl_evenOddSplitHornerEvalAsc
    (fp : FPModel) (x : ℝ) (coeffsAsc : List ℝ) : ℝ :=
  let yhat := fp.fl_mul x x
  let evenHat := fl_hornerAsc fp yhat (evenCoeffsAsc coeffsAsc)
  let oddHat := fl_hornerAsc fp yhat (oddCoeffsAsc coeffsAsc)
  fp.fl_add evenHat (fp.fl_mul x oddHat)

/-- Finite forward-error budget for the rounded even/odd split evaluator. -/
noncomputable def evenOddSplitForwardBudget
    (fp : FPModel) (x : ℝ) (coeffsAsc : List ℝ) : ℝ :=
  let yhat := fp.fl_mul x x
  let y := x * x
  let epsY := fp.u * |x * x|
  let even := evenCoeffsAsc coeffsAsc
  let odd := oddCoeffsAsc coeffsAsc
  let evenHat := fl_hornerAsc fp yhat even
  let oddHat := fl_hornerAsc fp yhat odd
  let epsEven :=
    hornerAscForwardBudget fp yhat even +
      polyAscArgErrorBudget yhat y even epsY
  let epsOdd :=
    hornerAscForwardBudget fp yhat odd +
      polyAscArgErrorBudget yhat y odd epsY
  let prodHat := fp.fl_mul x oddHat
  let epsProd := fp.u * |x * oddHat| + |x| * epsOdd
  fp.u * |evenHat + prodHat| + epsEven + epsProd

/-- Higham, 2nd ed., Problem 5.3: finite forward-error analysis for the
even/odd split evaluator, with the computed `y = fl(x*x)` included in the
budget. -/
theorem fl_evenOddSplitHornerEvalAsc_forward_error_bound
    (fp : FPModel) (x : ℝ) (coeffsAsc : List ℝ) :
    |fl_evenOddSplitHornerEvalAsc fp x coeffsAsc -
        polyAsc x coeffsAsc| ≤
      evenOddSplitForwardBudget fp x coeffsAsc := by
  let yhat : ℝ := fp.fl_mul x x
  let y : ℝ := x * x
  let epsY : ℝ := fp.u * |x * x|
  let even : List ℝ := evenCoeffsAsc coeffsAsc
  let odd : List ℝ := oddCoeffsAsc coeffsAsc
  let evenHat : ℝ := fl_hornerAsc fp yhat even
  let oddHat : ℝ := fl_hornerAsc fp yhat odd
  let epsEvenRound : ℝ := hornerAscForwardBudget fp yhat even
  let epsOddRound : ℝ := hornerAscForwardBudget fp yhat odd
  let epsEvenArg : ℝ := polyAscArgErrorBudget yhat y even epsY
  let epsOddArg : ℝ := polyAscArgErrorBudget yhat y odd epsY
  let epsEven : ℝ := epsEvenRound + epsEvenArg
  let epsOdd : ℝ := epsOddRound + epsOddArg
  let prodHat : ℝ := fp.fl_mul x oddHat
  let prod : ℝ := x * polyAsc y odd
  let epsProd : ℝ := fp.u * |x * oddHat| + |x| * epsOdd
  have hy : |yhat - y| ≤ epsY := by
    simpa [yhat, y, epsY] using fl_mul_abs_error_bound fp x x
  have hevenRound :
      |evenHat - polyAsc yhat even| ≤ epsEvenRound := by
    simpa [evenHat, epsEvenRound] using
      fl_hornerAsc_forward_error_bound fp yhat even
  have hoddRound :
      |oddHat - polyAsc yhat odd| ≤ epsOddRound := by
    simpa [oddHat, epsOddRound] using
      fl_hornerAsc_forward_error_bound fp yhat odd
  have hevenArg :
      |polyAsc yhat even - polyAsc y even| ≤ epsEvenArg := by
    simpa [epsEvenArg] using
      polyAsc_arg_error_bound yhat y epsY even hy
  have hoddArg :
      |polyAsc yhat odd - polyAsc y odd| ≤ epsOddArg := by
    simpa [epsOddArg] using
      polyAsc_arg_error_bound yhat y epsY odd hy
  have heven : |evenHat - polyAsc y even| ≤ epsEven := by
    have hdecomp :
        evenHat - polyAsc y even =
          (evenHat - polyAsc yhat even) +
            (polyAsc yhat even - polyAsc y even) := by
      ring
    calc
      |evenHat - polyAsc y even|
          = |(evenHat - polyAsc yhat even) +
              (polyAsc yhat even - polyAsc y even)| := by
            rw [hdecomp]
      _ ≤ |evenHat - polyAsc yhat even| +
            |polyAsc yhat even - polyAsc y even| :=
          abs_add_le _ _
      _ ≤ epsEvenRound + epsEvenArg :=
          add_le_add hevenRound hevenArg
      _ = epsEven := rfl
  have hodd : |oddHat - polyAsc y odd| ≤ epsOdd := by
    have hdecomp :
        oddHat - polyAsc y odd =
          (oddHat - polyAsc yhat odd) +
            (polyAsc yhat odd - polyAsc y odd) := by
      ring
    calc
      |oddHat - polyAsc y odd|
          = |(oddHat - polyAsc yhat odd) +
              (polyAsc yhat odd - polyAsc y odd)| := by
            rw [hdecomp]
      _ ≤ |oddHat - polyAsc yhat odd| +
            |polyAsc yhat odd - polyAsc y odd| :=
          abs_add_le _ _
      _ ≤ epsOddRound + epsOddArg :=
          add_le_add hoddRound hoddArg
      _ = epsOdd := rfl
  have hprod : |prodHat - prod| ≤ epsProd := by
    simpa [prodHat, prod, epsProd] using
      fl_mul_error_of_operand_error fp x oddHat (polyAsc y odd) epsOdd hodd
  have hadd :
      |fp.fl_add evenHat prodHat -
          (polyAsc y even + prod)| ≤
        fp.u * |evenHat + prodHat| + epsEven + epsProd :=
    fl_add_error_of_operand_errors fp evenHat (polyAsc y even)
      prodHat prod epsEven epsProd heven hprod
  have htarget :
      fp.fl_add evenHat prodHat - polyAsc x coeffsAsc =
        fp.fl_add evenHat prodHat - (polyAsc y even + prod) := by
    rw [polyAsc_evenOdd_split x coeffsAsc]
  calc
    |fl_evenOddSplitHornerEvalAsc fp x coeffsAsc -
        polyAsc x coeffsAsc|
        = |fp.fl_add evenHat prodHat - polyAsc x coeffsAsc| := by
          simp [fl_evenOddSplitHornerEvalAsc, yhat, even, odd,
            evenHat, oddHat, prodHat]
    _ = |fp.fl_add evenHat prodHat - (polyAsc y even + prod)| := by
          rw [htarget]
    _ ≤ fp.u * |evenHat + prodHat| + epsEven + epsProd := hadd
    _ = evenOddSplitForwardBudget fp x coeffsAsc := by
          simp [evenOddSplitForwardBudget, yhat, y, epsY, even, odd,
            evenHat, oddHat, epsEvenRound, epsOddRound, epsEvenArg,
            epsOddArg, epsEven, epsOdd, prodHat, epsProd]

end NumStability
