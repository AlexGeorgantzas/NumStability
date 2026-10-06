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
# Chapter05 Problem02 PowerBuilding Basic

Canonical destination for material split out of
`NumStability.Algorithms.Horner` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Tail contribution for the beginner power-building loop.  If the current
stored power is `y`, the next coefficient is multiplied by `x*y`. -/
noncomputable def beginnerPowerTail (x : ℝ) :
    List ℝ → ℝ → ℝ
  | [], _y => 0
  | a :: rest, y =>
      let y' := x * y
      a * y' + beginnerPowerTail x rest y'

/-- Higham, 2nd ed., Problem 5.2: one exact step of the beginner algorithm
`y <- x*y; q <- q + a_i*y`, with state `(q,y)`. -/
def beginnerPowerStep (x : ℝ) (state : ℝ × ℝ) (a : ℝ) : ℝ × ℝ :=
  let y' := x * state.2
  (state.1 + a * y', y')

/-- Exact beginner power-building evaluation from ascending coefficients. -/
noncomputable def beginnerPowerEvalAsc (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | a0 :: rest => (rest.foldl (beginnerPowerStep x) (a0, 1)).1

lemma beginnerPowerFold_fst_eq_add_tail (x : ℝ) :
    ∀ (coeffsAscTail : List ℝ) (q y : ℝ),
      (coeffsAscTail.foldl (beginnerPowerStep x) (q, y)).1 =
        q + beginnerPowerTail x coeffsAscTail y := by
  intro coeffsAscTail
  induction coeffsAscTail with
  | nil =>
      intro q y
      simp [beginnerPowerTail]
  | cons a rest ih =>
      intro q y
      simp [List.foldl, beginnerPowerStep, beginnerPowerTail, ih]
      ring

lemma beginnerPowerTail_eq_mul_x_polyAsc (x : ℝ) :
    ∀ (coeffsAscTail : List ℝ) (y : ℝ),
      beginnerPowerTail x coeffsAscTail y =
        y * x * polyAsc x coeffsAscTail := by
  intro coeffsAscTail
  induction coeffsAscTail with
  | nil =>
      intro y
      simp [beginnerPowerTail, polyAsc]
  | cons a rest ih =>
      intro y
      simp [beginnerPowerTail, polyAsc, ih]
      ring

/-- The exact beginner power-building loop evaluates the same ascending
polynomial as the displayed monomial formula. -/
theorem beginnerPowerEvalAsc_eq_polyAsc
    (x : ℝ) (coeffsAsc : List ℝ) :
    beginnerPowerEvalAsc x coeffsAsc = polyAsc x coeffsAsc := by
  cases coeffsAsc with
  | nil =>
      rfl
  | cons a0 rest =>
      have hfold := beginnerPowerFold_fst_eq_add_tail x rest a0 1
      have htail := beginnerPowerTail_eq_mul_x_polyAsc x rest 1
      calc
        beginnerPowerEvalAsc x (a0 :: rest)
            = a0 + beginnerPowerTail x rest 1 := by
              simpa [beginnerPowerEvalAsc] using hfold
        _ = a0 + x * polyAsc x rest := by
              rw [htail]
              ring
        _ = polyAsc x (a0 :: rest) := by
              simp [polyAsc]

/-- Rounded beginner power-building step.  The modeled implementation rounds
the power update, the coefficient-times-power product, and the accumulation. -/
noncomputable def fl_beginnerPowerStep
    (fp : FPModel) (x : ℝ) (state : ℝ × ℝ) (a : ℝ) : ℝ × ℝ :=
  let y' := fp.fl_mul x state.2
  let t := fp.fl_mul a y'
  (fp.fl_add state.1 t, y')

/-- Rounded beginner power-building evaluation from ascending coefficients. -/
noncomputable def fl_beginnerPowerEvalAsc
    (fp : FPModel) (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | a0 :: rest => (rest.foldl (fl_beginnerPowerStep fp x) (a0, 1)).1

/-- Recursive forward-error budget for the beginner power-building loop,
starting from rounded/exact states `(qhat,yhat)` and `(q,y)` with current error
budgets `epsQ` and `epsY`. -/
noncomputable def beginnerPowerForwardBudgetFrom
    (fp : FPModel) (x : ℝ) :
    List ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
  | [], _qhat, _q, _yhat, _y, epsQ, _epsY => epsQ
  | a :: rest, qhat, q, yhat, y, epsQ, epsY =>
      let yhat' := fp.fl_mul x yhat
      let y' := x * y
      let epsY' := fp.u * |x * yhat| + |x| * epsY
      let termhat := fp.fl_mul a yhat'
      let term := a * y'
      let epsTerm := fp.u * |a * yhat'| + |a| * epsY'
      let qhat' := fp.fl_add qhat termhat
      let q' := q + term
      let epsQ' := fp.u * |qhat + termhat| + epsQ + epsTerm
      beginnerPowerForwardBudgetFrom fp x rest qhat' q' yhat' y' epsQ' epsY'

/-- Top-level recursive forward-error budget for Problem 5.2. -/
noncomputable def beginnerPowerForwardBudget
    (fp : FPModel) (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | a0 :: rest =>
      beginnerPowerForwardBudgetFrom fp x rest a0 a0 1 1 0 0

theorem fl_beginnerPowerFold_forward_error_bound_from
    (fp : FPModel) (x : ℝ) :
    ∀ (coeffsAscTail : List ℝ)
      (qhat q yhat y epsQ epsY : ℝ),
      |qhat - q| ≤ epsQ →
      |yhat - y| ≤ epsY →
      |(coeffsAscTail.foldl (fl_beginnerPowerStep fp x)
          (qhat, yhat)).1 -
        (coeffsAscTail.foldl (beginnerPowerStep x) (q, y)).1| ≤
        beginnerPowerForwardBudgetFrom fp x coeffsAscTail
          qhat q yhat y epsQ epsY := by
  intro coeffsAscTail
  induction coeffsAscTail with
  | nil =>
      intro qhat q yhat y epsQ epsY hq _hy
      simpa [beginnerPowerForwardBudgetFrom] using hq
  | cons a rest ih =>
      intro qhat q yhat y epsQ epsY hq hy
      let yhat' : ℝ := fp.fl_mul x yhat
      let y' : ℝ := x * y
      let epsY' : ℝ := fp.u * |x * yhat| + |x| * epsY
      let termhat : ℝ := fp.fl_mul a yhat'
      let term : ℝ := a * y'
      let epsTerm : ℝ := fp.u * |a * yhat'| + |a| * epsY'
      let qhat' : ℝ := fp.fl_add qhat termhat
      let q' : ℝ := q + term
      let epsQ' : ℝ := fp.u * |qhat + termhat| + epsQ + epsTerm
      have hy' : |yhat' - y'| ≤ epsY' := by
        simpa [yhat', y', epsY'] using
          fl_mul_error_of_operand_error fp x yhat y epsY hy
      have hterm : |termhat - term| ≤ epsTerm := by
        simpa [termhat, term, epsTerm] using
          fl_mul_error_of_operand_error fp a yhat' y' epsY' hy'
      have hq' : |qhat' - q'| ≤ epsQ' := by
        simpa [qhat', q', termhat, term, epsQ'] using
          fl_add_error_of_operand_errors fp qhat q termhat term epsQ epsTerm
            hq hterm
      simpa [List.foldl, fl_beginnerPowerStep, beginnerPowerStep,
        beginnerPowerForwardBudgetFrom, yhat', y', epsY',
        termhat, term, epsTerm, qhat', q', epsQ'] using
          ih qhat' q' yhat' y' epsQ' epsY' hq' hy'

/-- Higham, 2nd ed., Problem 5.2: finite forward-error analysis of the beginner
power-building evaluator.  The budget exposes all modeled rounded operations:
one multiplication for the next power, one multiplication by the coefficient,
and one addition into the accumulated sum for each nonconstant coefficient. -/
theorem fl_beginnerPowerEvalAsc_forward_error_bound
    (fp : FPModel) (x : ℝ) (coeffsAsc : List ℝ) :
    |fl_beginnerPowerEvalAsc fp x coeffsAsc -
        beginnerPowerEvalAsc x coeffsAsc| ≤
      beginnerPowerForwardBudget fp x coeffsAsc := by
  cases coeffsAsc with
  | nil =>
      simp [fl_beginnerPowerEvalAsc, beginnerPowerEvalAsc,
        beginnerPowerForwardBudget]
  | cons a0 rest =>
      have h :=
        fl_beginnerPowerFold_forward_error_bound_from fp x
          rest a0 a0 1 1 0 0 (by simp) (by simp)
      simpa [fl_beginnerPowerEvalAsc, beginnerPowerEvalAsc,
        beginnerPowerForwardBudget] using h

theorem fl_beginnerPowerEvalAsc_forward_error_bound_poly
    (fp : FPModel) (x : ℝ) (coeffsAsc : List ℝ) :
    |fl_beginnerPowerEvalAsc fp x coeffsAsc -
        polyAsc x coeffsAsc| ≤
      beginnerPowerForwardBudget fp x coeffsAsc := by
  simpa [beginnerPowerEvalAsc_eq_polyAsc x coeffsAsc] using
    fl_beginnerPowerEvalAsc_forward_error_bound fp x coeffsAsc

end NumStability
