import Mathlib.Tactic.NormNum
import NumStability.Algorithms.Summation.Compensated.Kahan.Core
import NumStability.Source.Higham.Chapter04.Equation07.AbstractModelCounterexample

namespace NumStability

/-!
# Higham Algorithm 4.2: initialization model limitations

The bare `FPModel` left-zero law does not supply the right-zero coherence
needed for exact ingestion at the first Kahan step.  Concrete finite-format
initialization theorems remain in the reusable finite layer.
-/

/-- Bare `FPModel` does not force the first Algorithm 4.2 step from
`s=0,e=0` to ingest a nonzero input exactly.  This counterexample is the same
coarse abstract model used above for the local correction formula: it satisfies
the model's left-zero addition law, but not the right-zero coherence required
by the source finite-format initialization proof. -/
theorem kahanStepTrace_abstractCounterexample_zero :
    kahanStepTrace correctionFormulaAbstractCounterexampleFPModel
        (1 : ℝ) KahanState.zero =
      { temp := 0, y := 0, s := 0, e := 0 } := by
  norm_num [kahanStepTrace, KahanState.zero,
    correctionFormulaAbstractCounterexampleFPModel]

/-- The abstract standard model alone does not prove the source initialization
fact `kahanStep fp x KahanState.zero = {s := x, e := 0}` for all inputs.  The
finite-format theorem `finiteKahanStep_zero_of_finiteSystem` supplies the
coherence needed for concrete round-to-even formats. -/
theorem not_forall_kahanStep_zero_exact :
    ¬ ∀ (fp : FPModel) (x : ℝ),
      kahanStep fp x KahanState.zero = { s := x, e := 0 } := by
  intro h
  have h1 := h correctionFormulaAbstractCounterexampleFPModel (1 : ℝ)
  norm_num [kahanStep, kahanStepTrace, KahanStepTrace.nextState,
    KahanState.zero, correctionFormulaAbstractCounterexampleFPModel] at h1

/-- Concrete non-exact first-step consequence of
`kahanStepTrace_abstractCounterexample_zero`. -/
theorem kahanStep_abstractCounterexample_zero_ne_exact :
    kahanStep correctionFormulaAbstractCounterexampleFPModel
        (1 : ℝ) KahanState.zero ≠ { s := 1, e := 0 } := by
  intro h
  norm_num [kahanStep, kahanStepTrace, KahanStepTrace.nextState,
    KahanState.zero, correctionFormulaAbstractCounterexampleFPModel] at h

end NumStability
