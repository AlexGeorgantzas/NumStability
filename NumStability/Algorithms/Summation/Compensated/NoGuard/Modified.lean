import Mathlib.Algebra.BigOperators.Fin
import NumStability.Analysis.Error
import NumStability.Algorithms.Summation.Compensated.Kahan.Core

namespace NumStability

/-!
# Kahan's modified no-guard correction

Reusable execution and exact-arithmetic results for Kahan's machine-dependent
modified algorithm in the no-guard floating-point model.
-/

/-! ## Kahan's modified no-guard correction -/

/-- Source-shaped predicate for `sign(x) = sign(y)` with the usual real sign
trichotomy: both negative, both zero, or both positive. -/
def kahanSameSign (x y : ℝ) : Prop :=
  (x < 0 ∧ y < 0) ∨ (x = 0 ∧ y = 0) ∨ (0 < x ∧ 0 < y)

noncomputable instance kahanSameSignDecidable (x y : ℝ) :
    Decidable (kahanSameSign x y) :=
  Classical.dec _

/-- One source-level step of Kahan's no-guard-digit modified compensated
summation trace.  The field `f0` records the explicit source assignment
`f = 0`; `f` records the value after the optional same-sign branch. -/
structure KahanModifiedNoGuardStepTrace where
  temp : ℝ
  y : ℝ
  s : ℝ
  f0 : ℝ
  f : ℝ
  e : ℝ

namespace KahanModifiedNoGuardStepTrace

/-- The persistent state after a modified no-guard Kahan step trace. -/
def nextState (t : KahanModifiedNoGuardStepTrace) : KahanState :=
  { s := t.s, e := t.e }

end KahanModifiedNoGuardStepTrace

/-- One rounded step of Kahan's modified compensated summation for the
no-guard-digit model. -/
noncomputable def kahanModifiedNoGuardStepTrace
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    KahanModifiedNoGuardStepTrace :=
  let temp := state.s
  let y := fp.fl_add x state.e
  let s := fp.fl_add temp y
  let f0 := 0
  let f :=
    if kahanSameSign temp y then
      fp.fl_add (fp.fl_sub (fp.fl_mul ((46 : ℝ) / 100) s) s) s
    else
      f0
  let e := fp.fl_add (fp.fl_sub (fp.fl_sub temp f) (fp.fl_sub s f)) y
  { temp := temp, y := y, s := s, f0 := f0, f := f, e := e }

/-- Persistent-state update induced by one modified no-guard Kahan step. -/
noncomputable def kahanModifiedNoGuardStep
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) : KahanState :=
  (kahanModifiedNoGuardStepTrace fp x state).nextState

/-- The `temp` assignment in the modified no-guard Kahan variant. -/
theorem kahanModifiedNoGuardStepTrace_temp
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanModifiedNoGuardStepTrace fp x state).temp = state.s := by
  rfl

/-- The `y = x_i + e` assignment in the modified no-guard Kahan variant. -/
theorem kahanModifiedNoGuardStepTrace_y
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanModifiedNoGuardStepTrace fp x state).y = fp.fl_add x state.e := by
  rfl

/-- The `s = temp + y` assignment in the modified no-guard Kahan variant. -/
theorem kahanModifiedNoGuardStepTrace_s
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanModifiedNoGuardStepTrace fp x state).s =
      fp.fl_add (kahanModifiedNoGuardStepTrace fp x state).temp
        (kahanModifiedNoGuardStepTrace fp x state).y := by
  rfl

/-- The explicit `f = 0` assignment before the same-sign branch. -/
theorem kahanModifiedNoGuardStepTrace_f0
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanModifiedNoGuardStepTrace fp x state).f0 = 0 := by
  rfl

/-- The same-sign branch
`if sign(temp) = sign(y), f = (0.46 * s - s) + s, end`. -/
theorem kahanModifiedNoGuardStepTrace_f
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanModifiedNoGuardStepTrace fp x state).f =
      if kahanSameSign
          (kahanModifiedNoGuardStepTrace fp x state).temp
          (kahanModifiedNoGuardStepTrace fp x state).y then
        fp.fl_add
          (fp.fl_sub
            (fp.fl_mul ((46 : ℝ) / 100)
              (kahanModifiedNoGuardStepTrace fp x state).s)
            (kahanModifiedNoGuardStepTrace fp x state).s)
          (kahanModifiedNoGuardStepTrace fp x state).s
      else
        (kahanModifiedNoGuardStepTrace fp x state).f0 := by
  rfl

/-- The modified correction assignment
`e = ((temp - f) - (s - f)) + y`, in the displayed evaluation order. -/
theorem kahanModifiedNoGuardStepTrace_e
    (fp : NoGuardFPModel) (x : ℝ) (state : KahanState) :
    (kahanModifiedNoGuardStepTrace fp x state).e =
      fp.fl_add
        (fp.fl_sub
          (fp.fl_sub (kahanModifiedNoGuardStepTrace fp x state).temp
            (kahanModifiedNoGuardStepTrace fp x state).f)
          (fp.fl_sub (kahanModifiedNoGuardStepTrace fp x state).s
            (kahanModifiedNoGuardStepTrace fp x state).f))
        (kahanModifiedNoGuardStepTrace fp x state).y := by
  rfl

/-- State after the first `k` modified no-guard Kahan steps over a
length-`n` input. -/
noncomputable def kahanModifiedNoGuardPrefixState
    (fp : NoGuardFPModel) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : KahanState :=
  Fin.foldl k
    (fun state i =>
      kahanModifiedNoGuardStep fp
        (v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) state)
    KahanState.zero

/-- The per-index modified no-guard Kahan step trace, with the input state
obtained by running all earlier steps. -/
noncomputable def kahanModifiedNoGuardTrace
    (fp : NoGuardFPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) : KahanModifiedNoGuardStepTrace :=
  kahanModifiedNoGuardStepTrace fp (v i)
    (kahanModifiedNoGuardPrefixState fp v i.val (Nat.le_of_lt i.isLt))

/-- Final modified no-guard Kahan state after processing all `n` inputs. -/
noncomputable def fl_kahanModifiedNoGuardState
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) : KahanState :=
  kahanModifiedNoGuardPrefixState fp v n (Nat.le_refl n)

/-- Final sum returned by the modified no-guard Kahan variant. -/
noncomputable def fl_kahanModifiedNoGuardSum
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  (fl_kahanModifiedNoGuardState fp n v).s

/-- Final correction term retained by the modified no-guard Kahan variant. -/
noncomputable def fl_kahanModifiedNoGuardCorrection
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  (fl_kahanModifiedNoGuardState fp n v).e

/-- The final modified no-guard state is the explicit `n`-step prefix state. -/
theorem fl_kahanModifiedNoGuardState_eq_prefixState
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanModifiedNoGuardState fp n v =
      kahanModifiedNoGuardPrefixState fp v n (Nat.le_refl n) := by
  rfl

/-- The returned modified no-guard sum is the `s` field of the final state. -/
theorem fl_kahanModifiedNoGuardSum_eq_state_s
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanModifiedNoGuardSum fp n v =
      (fl_kahanModifiedNoGuardState fp n v).s := by
  rfl

/-- The retained modified no-guard correction is the `e` field of the final
state. -/
theorem fl_kahanModifiedNoGuardCorrection_eq_state_e
    (fp : NoGuardFPModel) (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanModifiedNoGuardCorrection fp n v =
      (fl_kahanModifiedNoGuardState fp n v).e := by
  rfl

/-- In exact arithmetic, one modified no-guard Kahan step adds the new input
to the running sum and leaves a zero correction.  The same-sign branch may
compute a nonzero auxiliary `f`, but it cancels algebraically in the correction
assignment. -/
theorem kahanModifiedNoGuardStep_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 < u0) (x sum : ℝ) :
    kahanModifiedNoGuardStep
        (NoGuardFPModel.exactWithUnitRoundoff u0 hu0) x
        { s := sum, e := 0 } =
      { s := sum + x, e := 0 } := by
  by_cases hsame : kahanSameSign sum x
  · simp [kahanModifiedNoGuardStep, kahanModifiedNoGuardStepTrace,
      KahanModifiedNoGuardStepTrace.nextState,
      NoGuardFPModel.exactWithUnitRoundoff, hsame]
  · simp [kahanModifiedNoGuardStep, kahanModifiedNoGuardStepTrace,
      KahanModifiedNoGuardStepTrace.nextState,
      NoGuardFPModel.exactWithUnitRoundoff, hsame]

/-- Under exact arithmetic, Kahan's modified no-guard state is the exact source
sum with zero retained correction. -/
theorem fl_kahanModifiedNoGuardState_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 < u0) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      fl_kahanModifiedNoGuardState
          (NoGuardFPModel.exactWithUnitRoundoff u0 hu0) n v =
        { s := ∑ i : Fin n, v i, e := 0 }
  | 0, _v => by
      simp [fl_kahanModifiedNoGuardState, kahanModifiedNoGuardPrefixState,
        KahanState.zero]
  | n + 1, v => by
      let fp := NoGuardFPModel.exactWithUnitRoundoff u0 hu0
      have hfold :
          fl_kahanModifiedNoGuardState fp (n + 1) v =
            kahanModifiedNoGuardStep fp (v (Fin.last n))
              (fl_kahanModifiedNoGuardState fp n
                (fun i : Fin n => v i.castSucc)) := by
        unfold fl_kahanModifiedNoGuardState kahanModifiedNoGuardPrefixState
        rw [Fin.foldl_succ_last]
      rw [hfold, fl_kahanModifiedNoGuardState_exactWithUnitRoundoff u0 hu0 n
        (fun i : Fin n => v i.castSucc)]
      rw [kahanModifiedNoGuardStep_exactWithUnitRoundoff]
      simp [Fin.sum_univ_castSucc, add_comm]

/-- Under exact arithmetic, the modified no-guard Kahan variant returns the
exact source sum. -/
theorem fl_kahanModifiedNoGuardSum_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 < u0) (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanModifiedNoGuardSum
        (NoGuardFPModel.exactWithUnitRoundoff u0 hu0) n v =
      ∑ i : Fin n, v i := by
  have hstate :=
    fl_kahanModifiedNoGuardState_exactWithUnitRoundoff u0 hu0 n v
  simpa [fl_kahanModifiedNoGuardSum] using congrArg KahanState.s hstate

/-- Under exact arithmetic, the modified no-guard Kahan variant retains zero
correction. -/
theorem fl_kahanModifiedNoGuardCorrection_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 < u0) (n : ℕ) (v : Fin n → ℝ) :
    fl_kahanModifiedNoGuardCorrection
        (NoGuardFPModel.exactWithUnitRoundoff u0 hu0) n v = 0 := by
  have hstate :=
    fl_kahanModifiedNoGuardState_exactWithUnitRoundoff u0 hu0 n v
  simpa [fl_kahanModifiedNoGuardCorrection] using congrArg KahanState.e hstate

end NumStability
