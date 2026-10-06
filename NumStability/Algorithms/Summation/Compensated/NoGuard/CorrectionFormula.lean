import NumStability.Analysis.Error
import NumStability.Algorithms.Summation.Compensated.CorrectionFormula

namespace NumStability

/-!
# No-guard local correction formula

Reusable traces and operation-witness identities for the local correction
formula evaluated in a no-guard floating-point model.
-/

/-- Source-level local correction trace under the no-guard model.  The extra
field `aMinusS` records the rounded intermediate subtraction in the displayed
evaluation order: `s = fl(a+b)`, `aMinusS = fl(a-s)`, `e = fl(aMinusS+b)`. -/
structure NoGuardCorrectionFormulaTrace where
  s : ℝ
  aMinusS : ℝ
  e : ℝ

namespace NoGuardCorrectionFormulaTrace

/-- The source exactness conclusion analogous to Higham equation (4.7). -/
def exact (a b : ℝ) (t : NoGuardCorrectionFormulaTrace) : Prop :=
  a + b = t.s + t.e

/-- The underlying no-guard local-operation witnesses for the displayed
correction-formula evaluation order. -/
def model (u a b : ℝ) (t : NoGuardCorrectionFormulaTrace) : Prop :=
  (∃ α β : ℝ, noGuardAddWitness t.s a b u α β) ∧
    (∃ α β : ℝ, noGuardSubWitness t.aMinusS a t.s u α β) ∧
      ∃ α β : ℝ, noGuardAddWitness t.e t.aMinusS b u α β

/-- Forget the no-guard subtraction intermediate and view the trace as the
ordinary correction-formula pair `(s,e)`. -/
def toCorrectionFormulaTrace (t : NoGuardCorrectionFormulaTrace) :
    CorrectionFormulaTrace :=
  { s := t.s, e := t.e }

end NoGuardCorrectionFormulaTrace

/-- The displayed local correction-formula trace evaluated in a supplied
no-guard floating-point model. -/
noncomputable def noGuardCorrectionFormulaTrace
    (fp : NoGuardFPModel) (a b : ℝ) : NoGuardCorrectionFormulaTrace :=
  let s := fp.fl_add a b
  let aMinusS := fp.fl_sub a s
  let e := fp.fl_add aMinusS b
  { s := s, aMinusS := aMinusS, e := e }

/-- The no-guard `s = fl(a+b)` assignment. -/
theorem noGuardCorrectionFormulaTrace_s
    (fp : NoGuardFPModel) (a b : ℝ) :
    (noGuardCorrectionFormulaTrace fp a b).s = fp.fl_add a b := by
  rfl

/-- The no-guard `aMinusS = fl(a-s)` assignment. -/
theorem noGuardCorrectionFormulaTrace_aMinusS
    (fp : NoGuardFPModel) (a b : ℝ) :
    (noGuardCorrectionFormulaTrace fp a b).aMinusS =
      fp.fl_sub a (noGuardCorrectionFormulaTrace fp a b).s := by
  rfl

/-- The no-guard `e = fl(aMinusS+b)` assignment. -/
theorem noGuardCorrectionFormulaTrace_e
    (fp : NoGuardFPModel) (a b : ℝ) :
    (noGuardCorrectionFormulaTrace fp a b).e =
      fp.fl_add (noGuardCorrectionFormulaTrace fp a b).aMinusS b := by
  rfl

/-- A no-guard model supplies exactly the local witnesses recorded by
`NoGuardCorrectionFormulaTrace.model`. -/
theorem noGuardCorrectionFormulaTrace_model
    (fp : NoGuardFPModel) (a b : ℝ) :
    NoGuardCorrectionFormulaTrace.model fp.u a b
      (noGuardCorrectionFormulaTrace fp a b) := by
  dsimp [NoGuardCorrectionFormulaTrace.model, noGuardCorrectionFormulaTrace]
  constructor
  · simpa using fp.model_add a b
  constructor
  · simpa using fp.model_sub a (fp.fl_add a b)
  · simpa using fp.model_add (fp.fl_sub a (fp.fl_add a b)) b

end NumStability
