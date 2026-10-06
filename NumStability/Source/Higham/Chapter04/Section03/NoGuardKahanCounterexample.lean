import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.Error
import NumStability.Algorithms.Summation.Compensated.NoGuard.Ordinary

namespace NumStability

/-!
# Higham Section 4.3 ordinary-Kahan no-guard counterexample

The concrete two-term failure behind the printed warning that the no-guard
model does not guarantee the standard compensated-summation bound.
-/

/-- A concrete no-guard model for a two-term compensated-summation failure.
All operations are exact except the two additions used in the second Kahan
step's ordinary correction formula. -/
noncomputable def kahanNoGuardCounterexampleModel : NoGuardFPModel where
  u := 1 / 4
  unit_roundoff_pos := by norm_num
  fl_add := fun x y =>
    if x = 1 ∧ y = -7 / 8 then 1 / 4
    else if x = 3 / 4 ∧ y = -7 / 8 then 0
    else x + y
  fl_sub := fun x y => x - y
  fl_mul := fun x y => x * y
  fl_div := fun x y => x / y
  model_add := by
    intro x y
    by_cases hbad₁ : x = 1 ∧ y = -7 / 8
    · refine ⟨0, -1 / 7, ?_, ?_, ?_⟩
      · norm_num
      · norm_num
      · rcases hbad₁ with ⟨rfl, rfl⟩
        norm_num [noGuardAddWitness]
    · by_cases hbad₂ : x = 3 / 4 ∧ y = -7 / 8
      · refine ⟨0, -1 / 7, ?_, ?_, ?_⟩
        · norm_num
        · norm_num
        · rcases hbad₂ with ⟨rfl, rfl⟩
          norm_num [hbad₁, noGuardAddWitness]
          rfl
      · refine ⟨0, 0, ?_, ?_, ?_⟩
        · norm_num
        · norm_num
        · simp [hbad₁, hbad₂]
  model_sub := by
    intro x y
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · simp
  model_mul := by
    intro x y
    refine ⟨0, ?_, ?_⟩
    · norm_num
    · unfold signedRelErrorWitness
      ring
  model_div := by
    intro x y _hy
    refine ⟨0, ?_, ?_⟩
    · norm_num
    · unfold signedRelErrorWitness
      ring

/-- The two-term input used by the ordinary no-guard Kahan counterexample. -/
noncomputable def kahanNoGuardCounterexampleInput : Fin 2 → ℝ :=
  fun i => if i.val = 0 then 1 else -7 / 8

/-- The ordinary no-guard Kahan counterexample finishes with `s = 1/4` and
zero correction, although the exact sum is `1/8`. -/
theorem fl_kahanNoGuardCounterexampleState_eq :
    fl_kahanNoGuardState kahanNoGuardCounterexampleModel 2
        kahanNoGuardCounterexampleInput =
      { s := 1 / 4, e := 0 } := by
  norm_num [fl_kahanNoGuardState, kahanNoGuardPrefixState,
    kahanNoGuardStep, kahanNoGuardStepTrace, KahanStepTrace.nextState,
    KahanState.zero, kahanNoGuardCounterexampleModel,
    kahanNoGuardCounterexampleInput, Fin.foldl_succ]

/-- The ordinary no-guard Kahan counterexample returns `1/4`. -/
theorem fl_kahanNoGuardCounterexampleSum_eq :
    fl_kahanNoGuardSum kahanNoGuardCounterexampleModel 2
        kahanNoGuardCounterexampleInput = 1 / 4 := by
  have hstate := fl_kahanNoGuardCounterexampleState_eq
  simpa [fl_kahanNoGuardSum] using congrArg KahanState.s hstate

/-- The ordinary no-guard Kahan counterexample retains zero correction. -/
theorem fl_kahanNoGuardCounterexampleCorrection_eq :
    fl_kahanNoGuardCorrection kahanNoGuardCounterexampleModel 2
        kahanNoGuardCounterexampleInput = 0 := by
  have hstate := fl_kahanNoGuardCounterexampleState_eq
  simpa [fl_kahanNoGuardCorrection] using congrArg KahanState.e hstate

/-- The exact sum of the no-guard Kahan counterexample input is `1/8`. -/
theorem kahanNoGuardCounterexample_exactSum_eq :
    (∑ i : Fin 2, kahanNoGuardCounterexampleInput i) = 1 / 8 := by
  norm_num [kahanNoGuardCounterexampleInput, Fin.sum_univ_two]

/-- Ordinary Kahan compensated summation can have relative error exactly one
under the no-guard model.  This records the algorithm-level failure mode behind
Higham's §4.3 (printed p. 86) warning that the no-guard model does not guarantee the
standard compensated-summation bound. -/
theorem kahanNoGuardCounterexample_relError_eq_one :
    relError
        (fl_kahanNoGuardSum kahanNoGuardCounterexampleModel 2
          kahanNoGuardCounterexampleInput)
        (∑ i : Fin 2, kahanNoGuardCounterexampleInput i) = 1 := by
  rw [fl_kahanNoGuardCounterexampleSum_eq,
    kahanNoGuardCounterexample_exactSum_eq]
  simpa using noGuardBinaryT3_truncated_relError_eq_one

end NumStability
