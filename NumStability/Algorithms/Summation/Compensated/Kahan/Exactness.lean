-- Algorithms/Summation/Compensated/Kahan/Exactness.lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Summation.Compensated.CorrectionFormula
import NumStability.Algorithms.Summation.Compensated.Kahan.Core

namespace NumStability

/-!
# Kahan compensated summation: exactness invariants

This module develops the source-independent local, prefix, and final exactness
invariants for Kahan summation, including the appended final-correction
variant.
-/

/-- The local correction pair inside one Kahan step is exactly the Chapter 4
equation-(4.7) correction-formula trace applied to `temp` and `y`. -/
theorem kahanStepTrace_correctionFormulaTrace
    (fp : FPModel) (x : ℝ) (state : KahanState) :
    ({ s := (kahanStepTrace fp x state).s,
       e := (kahanStepTrace fp x state).e } : CorrectionFormulaTrace) =
      correctionFormulaTrace fp
        (kahanStepTrace fp x state).temp
        (kahanStepTrace fp x state).y := by
  simp [kahanStepTrace, correctionFormulaTrace]

/-- If the `y = x + e` add and the local correction formula are exact for one
Kahan step, then the compensated total `s + e` after the step equals the
previous compensated total plus the new input. -/
theorem kahanStepTrace_compensated_total_eq_of_exact_y_and_correction
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (hy : (kahanStepTrace fp x state).y = x + state.e)
    (hcorr :
      CorrectionFormulaTrace.exact state.s (kahanStepTrace fp x state).y
        ({ s := (kahanStepTrace fp x state).s,
           e := (kahanStepTrace fp x state).e } : CorrectionFormulaTrace)) :
    (kahanStepTrace fp x state).s + (kahanStepTrace fp x state).e =
      state.s + x + state.e := by
  have hcorr' := hcorr
  dsimp [CorrectionFormulaTrace.exact] at hcorr'
  rw [← hcorr', hy]
  ring

/-- Persistent-state version of
`kahanStepTrace_compensated_total_eq_of_exact_y_and_correction`. -/
theorem kahanStep_compensated_total_eq_of_exact_y_and_correction
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (hy : (kahanStepTrace fp x state).y = x + state.e)
    (hcorr :
      CorrectionFormulaTrace.exact state.s (kahanStepTrace fp x state).y
        ({ s := (kahanStepTrace fp x state).s,
           e := (kahanStepTrace fp x state).e } : CorrectionFormulaTrace)) :
    (kahanStep fp x state).s + (kahanStep fp x state).e =
      state.s + x + state.e := by
  simpa [kahanStep, KahanStepTrace.nextState] using
    kahanStepTrace_compensated_total_eq_of_exact_y_and_correction
      fp x state hy hcorr

/-- Prefix invariant for Algorithm 4.2 from exact local correction.

If every processed Kahan step has exact `y = x + e` and its equation-(4.7)
local correction formula is exact, then the compensated total `s + e` after
the first `k` steps is the exact sum of the first `k` source inputs.  This is
the loop-level algebraic bridge from the local correction formula to Kahan's
persistent compensated state; it does not instantiate the cited backward-error
constants from Higham equations (4.8)--(4.9). -/
theorem kahanPrefixState_compensated_total_eq_sum_of_exact_steps
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      (∀ i : Fin k,
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        let state :=
          kahanPrefixState fp v i.val
            (Nat.le_trans (Nat.le_of_lt i.isLt) hk)
        let trace := kahanStepTrace fp (v idx) state
        trace.y = v idx + state.e ∧
          CorrectionFormulaTrace.exact state.s trace.y
            ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace)) →
      (kahanPrefixState fp v k hk).s +
          (kahanPrefixState fp v k hk).e =
        ∑ i : Fin k, v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  | 0, hk, _hexact => by
      simp [kahanPrefixState, KahanState.zero]
  | k + 1, hk, hexact => by
      have hprev_le : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let prev := kahanPrefixState fp v k hprev_le
      let idx : Fin n :=
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let trace := kahanStepTrace fp (v idx) prev
      have hfold :
          kahanPrefixState fp v (k + 1) hk =
            kahanStep fp (v idx) prev := by
        unfold kahanPrefixState
        rw [Fin.foldl_succ_last]
        rfl
      have hprev :
          prev.s + prev.e =
            ∑ i : Fin k, v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hprev_le⟩ := by
        apply kahanPrefixState_compensated_total_eq_sum_of_exact_steps fp v
        intro i
        simpa [prev, idx, trace] using hexact i.castSucc
      have hlocal := hexact (Fin.last k)
      have hstep :
          (kahanStep fp (v idx) prev).s +
              (kahanStep fp (v idx) prev).e =
            prev.s + v idx + prev.e := by
        exact kahanStep_compensated_total_eq_of_exact_y_and_correction
          fp (v idx) prev hlocal.1 hlocal.2
      rw [hfold, hstep]
      calc
        prev.s + v idx + prev.e = (prev.s + prev.e) + v idx := by ring
        _ = (∑ i : Fin k,
              v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hprev_le⟩) + v idx := by
            rw [hprev]
        _ = ∑ i : Fin (k + 1),
              v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ := by
            rw [Fin.sum_univ_castSucc]
            rfl

/-- Full-state form of
`kahanPrefixState_compensated_total_eq_sum_of_exact_steps`. -/
theorem fl_kahanState_compensated_total_eq_sum_of_exact_steps
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
        let trace := kahanStepTrace fp (v i) state
        trace.y = v i + state.e ∧
          CorrectionFormulaTrace.exact state.s trace.y
            ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace)) :
    (fl_kahanState fp n v).s + (fl_kahanState fp n v).e =
      ∑ i : Fin n, v i := by
  simpa [fl_kahanState] using
    kahanPrefixState_compensated_total_eq_sum_of_exact_steps
      fp v n (Nat.le_refl n) hexact

/-- Public returned-sum/correction form of the exact-step Kahan invariant. -/
theorem fl_kahanSum_add_correction_eq_sum_of_exact_steps
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
        let trace := kahanStepTrace fp (v i) state
        trace.y = v i + state.e ∧
          CorrectionFormulaTrace.exact state.s trace.y
            ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace)) :
    fl_kahanSum fp n v + fl_kahanCorrection fp n v =
      ∑ i : Fin n, v i := by
  simpa [fl_kahanSum, fl_kahanCorrection] using
    fl_kahanState_compensated_total_eq_sum_of_exact_steps fp n v hexact

/-- Final-correction variant described on printed p. 85: append `s = s + e` after
Algorithm 4.2. -/
noncomputable def fl_kahanFinalCorrectedSum (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  fp.fl_add (fl_kahanSum fp n v) (fl_kahanCorrection fp n v)

/-- The printed p. 85 appended final correction is the rounded add of final `s` and
final `e`. -/
theorem fl_kahanFinalCorrectedSum_eq_add_correction (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) :
    fl_kahanFinalCorrectedSum fp n v =
      fp.fl_add (fl_kahanSum fp n v) (fl_kahanCorrection fp n v) := by
  rfl

/-- If every Kahan step satisfies the exact local correction hypotheses and
the appended final correction add is exact, the final-corrected variant
returns the exact source sum. -/
theorem fl_kahanFinalCorrectedSum_eq_sum_of_exact_steps_and_final_add
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
        let trace := kahanStepTrace fp (v i) state
        trace.y = v i + state.e ∧
          CorrectionFormulaTrace.exact state.s trace.y
            ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hfinal :
      fp.fl_add (fl_kahanSum fp n v) (fl_kahanCorrection fp n v) =
        fl_kahanSum fp n v + fl_kahanCorrection fp n v) :
    fl_kahanFinalCorrectedSum fp n v = ∑ i : Fin n, v i := by
  rw [fl_kahanFinalCorrectedSum_eq_add_correction, hfinal]
  exact fl_kahanSum_add_correction_eq_sum_of_exact_steps fp n v hexact

/-- Under exact arithmetic, Kahan's state after all inputs have been processed
is the exact source sum with zero retained correction. -/
theorem fl_kahanState_exactWithUnitRoundoff (u0 : ℝ) (hu0 : 0 ≤ u0) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      fl_kahanState (FPModel.exactWithUnitRoundoff u0 hu0) n v =
        { s := ∑ i : Fin n, v i, e := 0 }
  | 0, _v => by
      simp [fl_kahanState, kahanPrefixState, KahanState.zero]
  | n + 1, v => by
      let fp := FPModel.exactWithUnitRoundoff u0 hu0
      have hfold :
          fl_kahanState fp (n + 1) v =
            kahanStep fp (v (Fin.last n))
              (fl_kahanState fp n (fun i : Fin n => v i.castSucc)) := by
        unfold fl_kahanState kahanPrefixState
        rw [Fin.foldl_succ_last]
      rw [hfold, fl_kahanState_exactWithUnitRoundoff u0 hu0 n
        (fun i : Fin n => v i.castSucc)]
      simp [fp, kahanStep, kahanStepTrace, KahanStepTrace.nextState,
        FPModel.exactWithUnitRoundoff, Fin.sum_univ_castSucc,
        add_comm]

/-- Under exact arithmetic, Kahan's returned sum is the exact source sum. -/
theorem fl_kahanSum_exactWithUnitRoundoff (u0 : ℝ) (hu0 : 0 ≤ u0)
    (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanSum (FPModel.exactWithUnitRoundoff u0 hu0) n v =
      ∑ i : Fin n, v i := by
  have hstate := fl_kahanState_exactWithUnitRoundoff u0 hu0 n v
  simpa [fl_kahanSum] using congrArg KahanState.s hstate

/-- Under exact arithmetic, Kahan's retained correction is zero. -/
theorem fl_kahanCorrection_exactWithUnitRoundoff (u0 : ℝ) (hu0 : 0 ≤ u0)
    (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanCorrection (FPModel.exactWithUnitRoundoff u0 hu0) n v = 0 := by
  have hstate := fl_kahanState_exactWithUnitRoundoff u0 hu0 n v
  simpa [fl_kahanCorrection] using congrArg KahanState.e hstate

/-- Under exact arithmetic, the printed p. 85 final-correction variant also returns
the exact source sum. -/
theorem fl_kahanFinalCorrectedSum_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanFinalCorrectedSum (FPModel.exactWithUnitRoundoff u0 hu0) n v =
      ∑ i : Fin n, v i := by
  rw [fl_kahanFinalCorrectedSum_eq_add_correction,
    fl_kahanSum_exactWithUnitRoundoff u0 hu0,
    fl_kahanCorrection_exactWithUnitRoundoff u0 hu0]
  simp [FPModel.exactWithUnitRoundoff]

end NumStability
