-- Algorithms/Summation/Compensated/Kahan/Core.lean

import NumStability.FloatingPoint.Model

namespace NumStability

/-!
# Kahan compensated summation: core execution

This module defines the reusable state, one-step trace, prefix execution, and
final projections for Kahan compensated summation.  Finite-format refinements,
error analysis, source-facing results, and abstract counterexamples live in
higher-level modules.
-/

/-- Persistent state of Kahan compensated summation: the current sum `s` and
the correction `e`. -/
structure KahanState where
  s : ℝ
  e : ℝ

namespace KahanState

/-- Initial state `s = 0; e = 0`. -/
def zero : KahanState :=
  { s := 0, e := 0 }

/-- Extensionality for Kahan stored-sum/correction states. -/
@[ext]
theorem ext_state {a b : KahanState} (hs : a.s = b.s) (he : a.e = b.e) :
    a = b := by
  cases a
  cases b
  simp at hs he
  simp [hs, he]

/-- Componentwise addition of stored-sum/correction states. -/
def add (a b : KahanState) : KahanState :=
  { s := a.s + b.s, e := a.e + b.e }

/-- Scalar multiplication of stored-sum/correction states. -/
def smul (c : ℝ) (a : KahanState) : KahanState :=
  { s := c * a.s, e := c * a.e }

/-- Reinterpret a stored-sum/correction pair as the paired
`(compensated total, retained correction)` coordinates used by the
Goldberg-style coefficient recursion. -/
def totalCorrection (a : KahanState) : KahanState :=
  { s := a.s + a.e, e := a.e }

/-- Recover the stored-sum coordinate from a paired
`(compensated total, retained correction)` coefficient state. -/
def returnedFromTotalCorrection (a : KahanState) : ℝ :=
  a.s - a.e

/-- Changing to `(s+e,e)` coordinates and then recovering the returned
stored-sum coordinate gives the original stored sum. -/
theorem returnedFromTotalCorrection_totalCorrection (a : KahanState) :
    returnedFromTotalCorrection (totalCorrection a) = a.s := by
  dsimp [returnedFromTotalCorrection, totalCorrection]
  ring

end KahanState

/-- One source-level Kahan loop trace, including the intermediate `temp` and
`y` values and the updated `s` and `e`. -/
structure KahanStepTrace where
  temp : ℝ
  y : ℝ
  s : ℝ
  e : ℝ

namespace KahanStepTrace

/-- The persistent state after a Kahan step trace. -/
def nextState (t : KahanStepTrace) : KahanState :=
  { s := t.s, e := t.e }

end KahanStepTrace

/-- One rounded Kahan compensated-summation step for input `x`. -/
noncomputable def kahanStepTrace (fp : FPModel) (x : ℝ)
    (state : KahanState) : KahanStepTrace :=
  let temp := state.s
  let y := fp.fl_add x state.e
  let s := fp.fl_add temp y
  let e := fp.fl_add (fp.fl_sub temp s) y
  { temp := temp, y := y, s := s, e := e }

/-- Persistent-state update induced by one Kahan step. -/
noncomputable def kahanStep (fp : FPModel) (x : ℝ)
    (state : KahanState) : KahanState :=
  (kahanStepTrace fp x state).nextState

/-- Abstract exact-zero-path bridge for the first Algorithm 4.2 step.

The theorem isolates the exact coherence needed to start Kahan's recurrence
from `s=0,e=0`: right-zero addition for the incoming input, exact subtraction
`0-x`, and exact cancellation `(-x)+x`.  Concrete finite round-to-even formats
provide these facts via representability lemmas; bare `FPModel` does not. -/
theorem kahanStepTrace_zero_of_exact_zero_path
    (fp : FPModel) {x : ℝ}
    (haddRight : fp.fl_add x 0 = x)
    (hsub : fp.fl_sub 0 x = -x)
    (hcancel : fp.fl_add (-x) x = 0) :
    kahanStepTrace fp x KahanState.zero =
      { temp := 0, y := x, s := x, e := 0 } := by
  simp [kahanStepTrace, KahanState.zero, haddRight, fp.fl_add_zero,
    hsub, hcancel]

/-- Persistent-state form of `kahanStepTrace_zero_of_exact_zero_path`. -/
theorem kahanStep_zero_of_exact_zero_path
    (fp : FPModel) {x : ℝ}
    (haddRight : fp.fl_add x 0 = x)
    (hsub : fp.fl_sub 0 x = -x)
    (hcancel : fp.fl_add (-x) x = 0) :
    kahanStep fp x KahanState.zero = { s := x, e := 0 } := by
  have htrace :=
    kahanStepTrace_zero_of_exact_zero_path
      fp haddRight hsub hcancel
  simpa [kahanStep, KahanStepTrace.nextState] using
    congrArg KahanStepTrace.nextState htrace

/-- The `temp` assignment in Algorithm 4.2. -/
theorem kahanStepTrace_temp (fp : FPModel) (x : ℝ) (state : KahanState) :
    (kahanStepTrace fp x state).temp = state.s := by
  rfl

/-- The `y = x_i + e` assignment in Algorithm 4.2. -/
theorem kahanStepTrace_y (fp : FPModel) (x : ℝ) (state : KahanState) :
    (kahanStepTrace fp x state).y = fp.fl_add x state.e := by
  rfl

/-- The `s = temp + y` assignment in Algorithm 4.2. -/
theorem kahanStepTrace_s (fp : FPModel) (x : ℝ) (state : KahanState) :
    (kahanStepTrace fp x state).s =
      fp.fl_add (kahanStepTrace fp x state).temp
        (kahanStepTrace fp x state).y := by
  rfl

/-- The `e = (temp - s) + y` assignment in Algorithm 4.2, in the displayed
evaluation order. -/
theorem kahanStepTrace_e (fp : FPModel) (x : ℝ) (state : KahanState) :
    (kahanStepTrace fp x state).e =
      fp.fl_add
        (fp.fl_sub (kahanStepTrace fp x state).temp
          (kahanStepTrace fp x state).s)
        (kahanStepTrace fp x state).y := by
  rfl

/-- State after the first `k` Kahan steps over a length-`n` input. -/
noncomputable def kahanPrefixState (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : KahanState :=
  Fin.foldl k
    (fun state i =>
      kahanStep fp (v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) state)
    KahanState.zero

/-- One-element abstract Kahan prefix state under the explicit exact-zero-path
hypotheses from `kahanStep_zero_of_exact_zero_path`. -/
theorem kahanPrefixState_one_of_exact_zero_path
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (hn : 1 ≤ n)
    (haddRight :
      fp.fl_add (v ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩) 0 =
        v ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩)
    (hsub :
      fp.fl_sub 0 (v ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩) =
        -(v ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩))
    (hcancel :
      fp.fl_add (-(v ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩))
          (v ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩) =
        0) :
    kahanPrefixState fp v 1 hn =
      { s := v ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩, e := 0 } := by
  rw [kahanPrefixState, Fin.foldl_succ]
  simpa using
    kahanStep_zero_of_exact_zero_path
      fp haddRight hsub hcancel

/-- The per-index Kahan step trace, with the input state obtained by running
all earlier steps. -/
noncomputable def kahanTrace (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) : KahanStepTrace :=
  kahanStepTrace fp (v i)
    (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))

/-- Final Kahan state after processing all `n` inputs. -/
noncomputable def fl_kahanState (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) : KahanState :=
  kahanPrefixState fp v n (Nat.le_refl n)

/-- Final compensated-summation value returned by Algorithm 4.2. -/
noncomputable def fl_kahanSum (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  (fl_kahanState fp n v).s

/-- Final correction term retained by Algorithm 4.2. -/
noncomputable def fl_kahanCorrection (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  (fl_kahanState fp n v).e

/-- The final state is the explicit `n`-step prefix state. -/
theorem fl_kahanState_eq_prefixState (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) :
    fl_kahanState fp n v = kahanPrefixState fp v n (Nat.le_refl n) := by
  rfl

/-- The returned sum is the `s` field of the final state. -/
theorem fl_kahanSum_eq_state_s (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) :
    fl_kahanSum fp n v = (fl_kahanState fp n v).s := by
  rfl

/-- The retained correction is the `e` field of the final state. -/
theorem fl_kahanCorrection_eq_state_e (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) :
    fl_kahanCorrection fp n v = (fl_kahanState fp n v).e := by
  rfl

end NumStability
