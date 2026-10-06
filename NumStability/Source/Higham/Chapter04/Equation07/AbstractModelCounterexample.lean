import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Summation.Compensated.CorrectionFormula

namespace NumStability

/-!
# Higham equation (4.7): abstract-model counterexample

The standard relative-error `FPModel` alone does not force the local
correction formula to recover the exact rounding error.  This source leaf
keeps that model-strength limitation separate from reusable algorithms.
-/

/-- A deliberately coarse abstract `FPModel` showing that the standard
relative-error model alone does not imply Higham equation (4.7).  Addition
from zero is exact, as required by `FPModel`; all other primitive operations
may round to zero with unit roundoff `u = 1`. -/
noncomputable def correctionFormulaAbstractCounterexampleFPModel : FPModel where
  u := 1
  u_nonneg := by norm_num
  fl_add := fun x y => if x = 0 then y else 0
  fl_sub := fun _ _ => 0
  fl_mul := fun _ _ => 0
  fl_div := fun _ _ => 0
  fl_sqrt := fun _ => 0
  fl_add_zero := by
    intro x
    simp
  model_add := by
    intro x y
    by_cases hx : x = 0
    · subst x
      refine ⟨0, by norm_num, ?_⟩
      simp
    · refine ⟨-1, by norm_num, ?_⟩
      simp [hx]
  model_sub := by
    intro x y
    refine ⟨-1, by norm_num, ?_⟩
    ring_nf
  model_mul := by
    intro x y
    refine ⟨-1, by norm_num, ?_⟩
    ring_nf
  model_div := by
    intro x y _hy
    refine ⟨-1, by norm_num, ?_⟩
    ring_nf
  model_sqrt := by
    intro x _hx
    refine ⟨-1, by norm_num, ?_⟩
    ring_nf

/-- The counterexample still satisfies the source magnitude precondition
`|a| > |b|`. -/
theorem correctionFormulaAbstractCounterexample_abs_order :
    |(-7 / 8 : ℝ)| < |(1 : ℝ)| := by
  norm_num

/-- Under the abstract standard model alone, the correction formula need not
recover the exact local error.  This separates the closed source-level trace
from the still-open finite base-2 exactness theorem. -/
theorem correctionFormulaAbstractCounterexample_not_exact :
    ¬ CorrectionFormulaTrace.exact (1 : ℝ) (-7 / 8)
      (correctionFormulaTrace correctionFormulaAbstractCounterexampleFPModel
        (1 : ℝ) (-7 / 8)) := by
  norm_num [CorrectionFormulaTrace.exact, correctionFormulaTrace,
    correctionFormulaAbstractCounterexampleFPModel]


end NumStability
