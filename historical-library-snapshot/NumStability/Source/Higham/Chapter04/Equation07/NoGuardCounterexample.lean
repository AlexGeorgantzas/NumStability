import Mathlib.Tactic.NormNum
import NumStability.Algorithms.Summation.Compensated.CorrectionFormula
import NumStability.Algorithms.Summation.Compensated.NoGuard.CorrectionFormula

namespace NumStability

/-!
# Higham equation (4.7): no-guard counterexample

A concrete local no-guard trace showing that the no-guard operation model
alone does not force the exact correction identity in Higham equation (4.7).
-/

/-- Concrete local no-guard trace showing that the no-guard model alone does
not force Higham equation (4.7).  The numbers have `|1| > |-7/8|`; the two
additions use permitted no-guard input perturbations with `u = 1/4`, while
the intermediate subtraction is exact. -/
noncomputable def noGuardCorrectionFormulaCounterexample :
    NoGuardCorrectionFormulaTrace :=
  { s := 1 / 4, aMinusS := 3 / 4, e := 0 }

/-- The counterexample satisfies the source magnitude precondition
`|a| > |b|`. -/
theorem noGuardCorrectionFormulaCounterexample_abs_order :
    |(-7 / 8 : ℝ)| < |(1 : ℝ)| := by
  norm_num

/-- The counterexample obeys the local no-guard operation model with
`u = 1/4`. -/
theorem noGuardCorrectionFormulaCounterexample_model :
    NoGuardCorrectionFormulaTrace.model (1 / 4 : ℝ) (1 : ℝ) (-7 / 8)
      noGuardCorrectionFormulaCounterexample := by
  dsimp [NoGuardCorrectionFormulaTrace.model,
    noGuardCorrectionFormulaCounterexample]
  constructor
  · refine ⟨0, -1 / 7, ?_, ?_, ?_⟩ <;> norm_num [noGuardAddWitness]
  constructor
  · refine ⟨0, 0, ?_, ?_, ?_⟩ <;> norm_num [noGuardSubWitness]
  · refine ⟨0, -1 / 7, ?_, ?_, ?_⟩ <;> norm_num [noGuardAddWitness]

/-- In that local no-guard trace, the equation `a+b = s+e` is false. -/
theorem noGuardCorrectionFormulaCounterexample_not_exact :
    ¬ NoGuardCorrectionFormulaTrace.exact (1 : ℝ) (-7 / 8)
      noGuardCorrectionFormulaCounterexample := by
  norm_num [NoGuardCorrectionFormulaTrace.exact,
    noGuardCorrectionFormulaCounterexample]

/-- The same counterexample refutes the ordinary `(s,e)` exactness predicate
after forgetting the no-guard intermediate. -/
theorem noGuardCorrectionFormulaCounterexample_toCorrectionFormulaTrace_not_exact :
    ¬ CorrectionFormulaTrace.exact (1 : ℝ) (-7 / 8)
      (NoGuardCorrectionFormulaTrace.toCorrectionFormulaTrace
        noGuardCorrectionFormulaCounterexample) := by
  norm_num [CorrectionFormulaTrace.exact,
    NoGuardCorrectionFormulaTrace.toCorrectionFormulaTrace,
    noGuardCorrectionFormulaCounterexample]

end NumStability
