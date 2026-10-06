import NumStability.Analysis.Error
import NumStability.Algorithms.Summation.Compensated.Kahan.Core

namespace NumStability

/-!
# Ordinary Kahan summation without a guard digit

Reusable execution definitions for the ordinary Kahan algorithm in the
no-guard floating-point model.
-/

/-! ## Ordinary Kahan summation under the no-guard model -/

/-- One ordinary Kahan compensated-summation step evaluated in the no-guard
model.  This is the unmodified Algorithm 4.2 trace, not Kahan's later
machine-dependent no-guard correction. -/
noncomputable def kahanNoGuardStepTrace (fp : NoGuardFPModel) (x : ℝ)
    (state : KahanState) : KahanStepTrace :=
  let temp := state.s
  let y := fp.fl_add x state.e
  let s := fp.fl_add temp y
  let e := fp.fl_add (fp.fl_sub temp s) y
  { temp := temp, y := y, s := s, e := e }

/-- Persistent-state update induced by one ordinary no-guard Kahan step. -/
noncomputable def kahanNoGuardStep (fp : NoGuardFPModel) (x : ℝ)
    (state : KahanState) : KahanState :=
  (kahanNoGuardStepTrace fp x state).nextState

/-- The `temp` assignment in ordinary no-guard Kahan summation. -/
theorem kahanNoGuardStepTrace_temp
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanNoGuardStepTrace fp x state).temp = state.s := by
  rfl

/-- The `y = x_i + e` assignment in ordinary no-guard Kahan summation. -/
theorem kahanNoGuardStepTrace_y
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanNoGuardStepTrace fp x state).y = fp.fl_add x state.e := by
  rfl

/-- The `s = temp + y` assignment in ordinary no-guard Kahan summation. -/
theorem kahanNoGuardStepTrace_s
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanNoGuardStepTrace fp x state).s =
      fp.fl_add (kahanNoGuardStepTrace fp x state).temp
        (kahanNoGuardStepTrace fp x state).y := by
  rfl

/-- The `e = (temp - s) + y` assignment in ordinary no-guard Kahan summation. -/
theorem kahanNoGuardStepTrace_e
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanNoGuardStepTrace fp x state).e =
      fp.fl_add
        (fp.fl_sub (kahanNoGuardStepTrace fp x state).temp
          (kahanNoGuardStepTrace fp x state).s)
        (kahanNoGuardStepTrace fp x state).y := by
  rfl

/-- State after the first `k` ordinary no-guard Kahan steps. -/
noncomputable def kahanNoGuardPrefixState
    (fp : NoGuardFPModel) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : KahanState :=
  Fin.foldl k
    (fun state i =>
      kahanNoGuardStep fp
        (v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) state)
    KahanState.zero

/-- The per-index ordinary no-guard Kahan trace. -/
noncomputable def kahanNoGuardTrace
    (fp : NoGuardFPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) : KahanStepTrace :=
  kahanNoGuardStepTrace fp (v i)
    (kahanNoGuardPrefixState fp v i.val (Nat.le_of_lt i.isLt))

/-- Final ordinary no-guard Kahan state after all inputs. -/
noncomputable def fl_kahanNoGuardState
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) : KahanState :=
  kahanNoGuardPrefixState fp v n (Nat.le_refl n)

/-- Final sum returned by ordinary Kahan summation in the no-guard model. -/
noncomputable def fl_kahanNoGuardSum
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  (fl_kahanNoGuardState fp n v).s

/-- Final correction retained by ordinary Kahan summation in the no-guard model. -/
noncomputable def fl_kahanNoGuardCorrection
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  (fl_kahanNoGuardState fp n v).e

/-- The final ordinary no-guard state is the explicit prefix state. -/
theorem fl_kahanNoGuardState_eq_prefixState
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanNoGuardState fp n v =
      kahanNoGuardPrefixState fp v n (Nat.le_refl n) := by
  rfl

/-- The ordinary no-guard returned sum is the `s` field of the final state. -/
theorem fl_kahanNoGuardSum_eq_state_s
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanNoGuardSum fp n v =
      (fl_kahanNoGuardState fp n v).s := by
  rfl

/-- The ordinary no-guard retained correction is the `e` field of the final state. -/
theorem fl_kahanNoGuardCorrection_eq_state_e
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanNoGuardCorrection fp n v =
      (fl_kahanNoGuardState fp n v).e := by
  rfl

end NumStability
