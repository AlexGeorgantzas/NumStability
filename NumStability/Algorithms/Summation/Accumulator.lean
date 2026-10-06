-- Algorithms/Summation/Accumulator.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Error
import NumStability.Algorithms.Summation.Recursive.Core

namespace NumStability

open scoped BigOperators

/-!
# Accumulator and Distillation Summation

Reusable APIs for overflow-driven accumulator cascades and sum-preserving
distillation traces. The principal surfaces are `AccumulatorState`,
`accumulatorCascadeFrom`, `fl_accumulatorSum`, `DistillationState`, and
`DistillationTrace`; overflow detection and final accumulator order remain
explicit parameters so the API is independent of a particular machine.

The design follows the Wolfe--Malcolm--Ross accumulator methods and the
distillation discussion in Higham, Chapter 4, §4.4. Their machine-specific
overflow rules, and Malcolm's relative-error guarantee of order `u`, require a
separate concrete finite-machine model.
-/

/-- A finite bank of `levels + 1` accumulators. -/
abbrev AccumulatorState (levels : ℕ) := Fin (levels + 1) → ℝ

/-- A machine-dependent overflow test for a proposed value at an accumulator
level.  The source text does not specify this predicate portably. -/
abbrev AccumulatorOverflowTest (levels : ℕ) :=
  Fin (levels + 1) → ℝ → Bool

/-- Initial accumulator bank, all zero. -/
def accumulatorZero (levels : ℕ) : AccumulatorState levels :=
  fun _ => 0

/-- Update one accumulator level. -/
def accumulatorSet {levels : ℕ} (state : AccumulatorState levels)
    (level : Fin (levels + 1)) (value : ℝ) : AccumulatorState levels :=
  Function.update state level value

/-- Reading back the level just updated. -/
theorem accumulatorSet_self {levels : ℕ} (state : AccumulatorState levels)
    (level : Fin (levels + 1)) (value : ℝ) :
    accumulatorSet state level value level = value := by
  simp [accumulatorSet]

/-- Other accumulator levels are unchanged by a single-level update. -/
theorem accumulatorSet_of_ne {levels : ℕ} (state : AccumulatorState levels)
    {level other : Fin (levels + 1)} (value : ℝ) (hne : other ≠ level) :
    accumulatorSet state level value other = state other := by
  simp [accumulatorSet, Function.update_of_ne hne]

/-- Source-level cascade after adding a carry to a specific accumulator level.
If the proposed value overflows and a higher level exists, the current level is
reset to zero and the proposed value is carried upward.  Otherwise the proposed
value is stored at the current level and the cascade stops. -/
noncomputable def accumulatorCascadeFrom (fp : FPModel) {levels : ℕ}
    (overflow : AccumulatorOverflowTest levels) :
    ℕ → AccumulatorState levels → ℕ → ℝ → AccumulatorState levels
  | 0, state, _, _ => state
  | fuel + 1, state, level, carry =>
      if hlevel : level < levels + 1 then
        let i : Fin (levels + 1) := ⟨level, hlevel⟩
        let proposed := fp.fl_add (state i) carry
        if overflow i proposed && decide (level < levels) then
          accumulatorCascadeFrom fp overflow fuel
            (accumulatorSet state i 0) (level + 1) proposed
        else
          accumulatorSet state i proposed
      else
        state

/-- If the proposed value at a level does not overflow, the cascade stops by
storing that value. -/
theorem accumulatorCascadeFrom_no_overflow {levels fuel level : ℕ}
    (fp : FPModel) (overflow : AccumulatorOverflowTest levels)
    (state : AccumulatorState levels) (carry : ℝ)
    (hlevel : level < levels + 1)
    (hno : overflow ⟨level, hlevel⟩
      (fp.fl_add (state ⟨level, hlevel⟩) carry) = false) :
    accumulatorCascadeFrom fp overflow (fuel + 1) state level carry =
      accumulatorSet state ⟨level, hlevel⟩
        (fp.fl_add (state ⟨level, hlevel⟩) carry) := by
  simp [accumulatorCascadeFrom, hlevel, hno]

/-- If the proposed value overflows and a higher level exists, the current
level is reset to zero and the proposed value is carried upward. -/
theorem accumulatorCascadeFrom_overflow_to_next {levels fuel level : ℕ}
    (fp : FPModel) (overflow : AccumulatorOverflowTest levels)
    (state : AccumulatorState levels) (carry : ℝ)
    (hlevel : level < levels + 1) (hnext : level < levels)
    (hover : overflow ⟨level, hlevel⟩
      (fp.fl_add (state ⟨level, hlevel⟩) carry) = true) :
    accumulatorCascadeFrom fp overflow (fuel + 1) state level carry =
      accumulatorCascadeFrom fp overflow fuel
        (accumulatorSet state ⟨level, hlevel⟩ 0) (level + 1)
        (fp.fl_add (state ⟨level, hlevel⟩) carry) := by
  simp [accumulatorCascadeFrom, hlevel, hnext, hover]

/-- At the highest available level there is no next accumulator, so even a
machine overflow signal stores the proposed value and stops the finite cascade.
Concrete machine models can choose enough levels so this branch is unreachable. -/
theorem accumulatorCascadeFrom_no_next_level {levels fuel level : ℕ}
    (fp : FPModel) (overflow : AccumulatorOverflowTest levels)
    (state : AccumulatorState levels) (carry : ℝ)
    (hlevel : level < levels + 1) (hnoNext : ¬ level < levels) :
    accumulatorCascadeFrom fp overflow (fuel + 1) state level carry =
      accumulatorSet state ⟨level, hlevel⟩
        (fp.fl_add (state ⟨level, hlevel⟩) carry) := by
  cases hover : overflow ⟨level, hlevel⟩
      (fp.fl_add (state ⟨level, hlevel⟩) carry)
  · simp [accumulatorCascadeFrom, hlevel, hnoNext, hover]
  · simp [accumulatorCascadeFrom, hlevel, hnoNext, hover]

/-- Add a source term to the lowest-level accumulator and cascade as needed. -/
noncomputable def accumulatorAddTerm (fp : FPModel) {levels : ℕ}
    (overflow : AccumulatorOverflowTest levels)
    (state : AccumulatorState levels) (x : ℝ) : AccumulatorState levels :=
  accumulatorCascadeFrom fp overflow (levels + 1) state 0 x

/-- If adding a term to the lowest accumulator does not overflow, only that
lowest accumulator is updated. -/
theorem accumulatorAddTerm_no_lowest_overflow (fp : FPModel) {levels : ℕ}
    (overflow : AccumulatorOverflowTest levels)
    (state : AccumulatorState levels) (x : ℝ)
    (hno : overflow ⟨0, Nat.succ_pos levels⟩
      (fp.fl_add (state ⟨0, Nat.succ_pos levels⟩) x) = false) :
    accumulatorAddTerm fp overflow state x =
      accumulatorSet state ⟨0, Nat.succ_pos levels⟩
        (fp.fl_add (state ⟨0, Nat.succ_pos levels⟩) x) := by
  simpa [accumulatorAddTerm] using
    accumulatorCascadeFrom_no_overflow (fuel := levels) (level := 0)
      fp overflow state x (Nat.succ_pos levels) hno

/-- State after processing the first `k` source terms through the accumulator
cascade. -/
noncomputable def accumulatorPrefixState (fp : FPModel) {levels n : ℕ}
    (overflow : AccumulatorOverflowTest levels)
    (x : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : AccumulatorState levels :=
  Fin.foldl k
    (fun state i =>
      accumulatorAddTerm fp overflow state
        (x ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩))
    (accumulatorZero levels)

/-- Final accumulator bank after all source terms have been processed. -/
noncomputable def fl_accumulatorState (fp : FPModel) {levels : ℕ}
    (overflow : AccumulatorOverflowTest levels)
    (n : ℕ) (x : Fin n → ℝ) : AccumulatorState levels :=
  accumulatorPrefixState fp overflow x n (Nat.le_refl n)

/-- Predicate saying that `order` lists the accumulator bank in decreasing
absolute value, the final order specified for Malcolm's method. -/
def DecreasingAbsAccumulatorOrder {levels : ℕ}
    (state : AccumulatorState levels)
    (order : Fin (levels + 1) → Fin (levels + 1)) : Prop :=
  ∀ i j : Fin (levels + 1), i.val < j.val →
    |state (order j)| ≤ |state (order i)|

/-- Recursive summation of the final accumulators in a supplied order. -/
noncomputable def fl_accumulatorFinalSum (fp : FPModel) {levels : ℕ}
    (state : AccumulatorState levels)
    (order : Fin (levels + 1) → Fin (levels + 1)) : ℝ :=
  fl_recursiveSum fp (levels + 1) (fun i => state (order i))

/-- Full accumulator method: process the inputs by cascading accumulators, then
recursively sum the final accumulator bank in the supplied order. -/
noncomputable def fl_accumulatorSum (fp : FPModel) {levels : ℕ}
    (overflow : AccumulatorOverflowTest levels)
    (n : ℕ) (x : Fin n → ℝ)
    (order : Fin (levels + 1) → Fin (levels + 1)) : ℝ :=
  fl_accumulatorFinalSum fp (fl_accumulatorState fp overflow n x) order

/-- The final state is the explicit `n`-step prefix state. -/
theorem fl_accumulatorState_eq_prefixState (fp : FPModel) {levels : ℕ}
    (overflow : AccumulatorOverflowTest levels)
    (n : ℕ) (x : Fin n → ℝ) :
    fl_accumulatorState fp overflow n x =
      accumulatorPrefixState fp overflow x n (Nat.le_refl n) := by
  rfl

/-- The accumulator method's final phase is recursive summation of the final
accumulator bank in the supplied order. -/
theorem fl_accumulatorSum_eq_recursive_final_state (fp : FPModel)
    {levels : ℕ} (overflow : AccumulatorOverflowTest levels)
    (n : ℕ) (x : Fin n → ℝ)
    (order : Fin (levels + 1) → Fin (levels + 1)) :
    fl_accumulatorSum fp overflow n x order =
      fl_recursiveSum fp (levels + 1)
        (fun i => fl_accumulatorState fp overflow n x (order i)) := by
  rfl

/-- When the supplied final order is decreasing in absolute value, the full
method records Malcolm's source-side final-order condition. -/
theorem fl_accumulatorSum_uses_decreasing_abs_order (fp : FPModel)
    {levels : ℕ} (overflow : AccumulatorOverflowTest levels)
    (n : ℕ) (x : Fin n → ℝ)
    (order : Fin (levels + 1) → Fin (levels + 1))
    (horder :
      DecreasingAbsAccumulatorOrder
        (fl_accumulatorState fp overflow n x) order) :
    DecreasingAbsAccumulatorOrder
      (fl_accumulatorState fp overflow n x) order :=
  horder

/-- A concrete overflow predicate for the sanity path where no accumulator level
signals overflow. -/
def accumulatorNeverOverflow {levels : ℕ} : AccumulatorOverflowTest levels :=
  fun _ _ => false

/-- The identity final accumulator order. -/
def accumulatorIdentityOrder {levels : ℕ} :
    Fin (levels + 1) → Fin (levels + 1) :=
  id

/-- Under exact arithmetic and a never-overflowing accumulator, the lowest
accumulator contains the exact source sum. -/
theorem fl_accumulatorState_neverOverflow_zero_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) {levels : ℕ} :
    ∀ (n : ℕ) (x : Fin n → ℝ),
      fl_accumulatorState (FPModel.exactWithUnitRoundoff u0 hu0)
          (accumulatorNeverOverflow (levels := levels)) n x
          ⟨0, Nat.succ_pos levels⟩ =
        ∑ i : Fin n, x i
  | 0, _x => by
      simp [fl_accumulatorState, accumulatorPrefixState, accumulatorZero]
  | n + 1, x => by
      let fp := FPModel.exactWithUnitRoundoff u0 hu0
      have hfold :
          fl_accumulatorState (levels := levels) fp
              (accumulatorNeverOverflow (levels := levels)) (n + 1) x =
            accumulatorAddTerm (levels := levels) fp
              (accumulatorNeverOverflow (levels := levels))
              (fl_accumulatorState (levels := levels) fp
                (accumulatorNeverOverflow (levels := levels)) n
                (fun i : Fin n => x i.castSucc))
              (x (Fin.last n)) := by
        unfold fl_accumulatorState accumulatorPrefixState
        rw [Fin.foldl_succ_last]
      rw [hfold]
      let prev :=
        fl_accumulatorState (levels := levels) fp
          (accumulatorNeverOverflow (levels := levels)) n
          (fun i : Fin n => x i.castSucc)
      have hadd :
          accumulatorAddTerm (levels := levels) fp
              (accumulatorNeverOverflow (levels := levels)) prev
              (x (Fin.last n)) =
            accumulatorSet prev ⟨0, Nat.succ_pos levels⟩
              (fp.fl_add (prev ⟨0, Nat.succ_pos levels⟩)
                (x (Fin.last n))) := by
        exact accumulatorAddTerm_no_lowest_overflow (levels := levels) fp
          (accumulatorNeverOverflow (levels := levels)) prev
          (x (Fin.last n)) rfl
      rw [hadd, accumulatorSet_self]
      dsimp [prev]
      have hprev0 :
          fl_accumulatorState (levels := levels) fp
              (accumulatorNeverOverflow (levels := levels)) n
              (fun i : Fin n => x i.castSucc) 0 =
            ∑ i : Fin n, x i.castSucc := by
        simpa [fp] using
          fl_accumulatorState_neverOverflow_zero_exactWithUnitRoundoff
            (levels := levels) u0 hu0 n (fun i : Fin n => x i.castSucc)
      rw [hprev0]
      simp [fp, FPModel.exactWithUnitRoundoff, Fin.sum_univ_castSucc,
        add_comm]

/-- Under exact arithmetic and a never-overflowing accumulator, every higher
accumulator remains zero. -/
theorem fl_accumulatorState_neverOverflow_of_ne_zero_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) {levels : ℕ} :
    ∀ (n : ℕ) (x : Fin n → ℝ) (level : Fin (levels + 1)),
      level ≠ ⟨0, Nat.succ_pos levels⟩ →
        fl_accumulatorState (FPModel.exactWithUnitRoundoff u0 hu0)
          (accumulatorNeverOverflow (levels := levels)) n x level = 0
  | 0, _x, level, _hne => by
      simp [fl_accumulatorState, accumulatorPrefixState, accumulatorZero]
  | n + 1, x, level, hne => by
      let fp := FPModel.exactWithUnitRoundoff u0 hu0
      have hfold :
          fl_accumulatorState (levels := levels) fp
              (accumulatorNeverOverflow (levels := levels)) (n + 1) x =
            accumulatorAddTerm (levels := levels) fp
              (accumulatorNeverOverflow (levels := levels))
              (fl_accumulatorState (levels := levels) fp
                (accumulatorNeverOverflow (levels := levels)) n
                (fun i : Fin n => x i.castSucc))
              (x (Fin.last n)) := by
        unfold fl_accumulatorState accumulatorPrefixState
        rw [Fin.foldl_succ_last]
      rw [hfold]
      let prev :=
        fl_accumulatorState (levels := levels) fp
          (accumulatorNeverOverflow (levels := levels)) n
          (fun i : Fin n => x i.castSucc)
      have hadd :
          accumulatorAddTerm (levels := levels) fp
              (accumulatorNeverOverflow (levels := levels)) prev
              (x (Fin.last n)) =
            accumulatorSet prev ⟨0, Nat.succ_pos levels⟩
              (fp.fl_add (prev ⟨0, Nat.succ_pos levels⟩)
                (x (Fin.last n))) := by
        exact accumulatorAddTerm_no_lowest_overflow (levels := levels) fp
          (accumulatorNeverOverflow (levels := levels)) prev
          (x (Fin.last n)) rfl
      rw [hadd]
      rw [accumulatorSet_of_ne prev
        (fp.fl_add (prev ⟨0, Nat.succ_pos levels⟩) (x (Fin.last n)))
        hne]
      exact
        fl_accumulatorState_neverOverflow_of_ne_zero_exactWithUnitRoundoff
          (levels := levels) u0 hu0 n (fun i : Fin n => x i.castSucc)
          level hne

/-- The never-overflow accumulator method returns the exact source sum under
exact arithmetic for any finite accumulator bank when the final accumulator
order is the identity.  This is a sanity theorem for the source-level
accumulator pipeline, not Malcolm's machine-dependent order-`u` guarantee. -/
theorem fl_accumulatorSum_neverOverflow_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) {levels : ℕ}
    (n : ℕ) (x : Fin n → ℝ) :
    fl_accumulatorSum (FPModel.exactWithUnitRoundoff u0 hu0)
        (accumulatorNeverOverflow (levels := levels)) n x
        (accumulatorIdentityOrder (levels := levels)) =
      ∑ i : Fin n, x i := by
  rw [fl_accumulatorSum_eq_recursive_final_state,
    fl_recursiveSum_exactWithUnitRoundoff]
  rw [Fin.sum_univ_succ]
  simp [accumulatorIdentityOrder]
  have hlowest :
      fl_accumulatorState (FPModel.exactWithUnitRoundoff u0 hu0)
          (accumulatorNeverOverflow (levels := levels)) n x
          ⟨0, Nat.succ_pos levels⟩ =
        ∑ i : Fin n, x i :=
    fl_accumulatorState_neverOverflow_zero_exactWithUnitRoundoff
      (levels := levels) u0 hu0 n x
  have hlowest0 :
      fl_accumulatorState (FPModel.exactWithUnitRoundoff u0 hu0)
          (accumulatorNeverOverflow (levels := levels)) n x 0 =
        ∑ i : Fin n, x i := by
    simpa using hlowest
  rw [hlowest0]
  have htail :
      (∑ i : Fin levels,
        fl_accumulatorState (FPModel.exactWithUnitRoundoff u0 hu0)
          (accumulatorNeverOverflow (levels := levels)) n x
          (Fin.succ i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    exact
      fl_accumulatorState_neverOverflow_of_ne_zero_exactWithUnitRoundoff
        (levels := levels) u0 hu0 n x (Fin.succ i) (by simp)
  rw [htail]
  ring

/-- The one-level never-overflow accumulator method returns the exact source sum
under exact arithmetic.  This is retained as the scalar-bank specialization of
`fl_accumulatorSum_neverOverflow_exactWithUnitRoundoff`. -/
theorem fl_accumulatorSum_singleLevel_neverOverflow_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) (n : ℕ) (x : Fin n → ℝ) :
    fl_accumulatorSum (FPModel.exactWithUnitRoundoff u0 hu0)
        (accumulatorNeverOverflow (levels := 0)) n x
        (accumulatorIdentityOrder (levels := 0)) =
      ∑ i : Fin n, x i := by
  exact fl_accumulatorSum_neverOverflow_exactWithUnitRoundoff
    (levels := 0) u0 hu0 n x

/-! ## Distillation algorithm traces -/

/-- State of a distillation algorithm on a nonempty family of floating-point
numbers.  The source paragraph indexes the distinguished final component as
`x_n^(k)`, so the Lean state uses `Fin (n + 1)`. -/
structure DistillationState (n : ℕ) where
  values : Fin (n + 1) → ℝ

/-- Initial distillation state for already-rounded floating-point inputs
`x_i = fl(\bar x_i)`. -/
def distillationInitialState {n : ℕ}
    (x : Fin (n + 1) → ℝ) : DistillationState n :=
  { values := x }

/-- Exact sum represented by a distillation state. -/
noncomputable def distillationStateSum {n : ℕ}
    (state : DistillationState n) : ℝ :=
  ∑ i : Fin (n + 1), state.values i

/-- The initial distillation state represents exactly the supplied input sum. -/
theorem distillationInitialState_sum_eq {n : ℕ}
    (x : Fin (n + 1) → ℝ) :
    distillationStateSum (distillationInitialState x) =
      ∑ i : Fin (n + 1), x i := by
  rfl

/-- Abstract source-level trace for Kahan-style distillation algorithms:
starting from the supplied floating-point inputs, each constructed state
preserves the exact sum of the inputs.  The chapter excerpt does not specify
the concrete transformation, so the transformation itself is intentionally a
trace field rather than a claimed implementation. -/
structure DistillationTrace (n steps : ℕ) (x : Fin (n + 1) → ℝ) where
  state : Fin (steps + 1) → DistillationState n
  initial :
    state ⟨0, Nat.succ_pos steps⟩ = distillationInitialState x
  sum_preserved :
    ∀ k : Fin (steps + 1),
      distillationStateSum (state k) = ∑ i : Fin (n + 1), x i

/-- The final state of a finite distillation trace. -/
def DistillationTrace.finalState {n steps : ℕ}
    {x : Fin (n + 1) → ℝ}
    (trace : DistillationTrace n steps x) : DistillationState n :=
  trace.state (Fin.last steps)

/-- The distinguished final component `x_n^(k)` of a distillation trace. -/
def DistillationTrace.finalComponent {n steps : ℕ}
    {x : Fin (n + 1) → ℝ}
    (trace : DistillationTrace n steps x) : ℝ :=
  (trace.finalState).values (Fin.last n)

/-- Termination predicate from the source paragraph: the distinguished final
component approximates the original sum with relative error at most `u`. -/
noncomputable def DistillationTrace.terminatesWithinUnitRoundoff {n steps : ℕ}
    {x : Fin (n + 1) → ℝ}
    (trace : DistillationTrace n steps x) (u : ℝ) : Prop :=
  relError trace.finalComponent (∑ i : Fin (n + 1), x i) ≤ u

/-- Every state in a distillation trace preserves the exact source sum. -/
theorem distillationTrace_sum_preserved {n steps : ℕ}
    {x : Fin (n + 1) → ℝ}
    (trace : DistillationTrace n steps x) (k : Fin (steps + 1)) :
    distillationStateSum (trace.state k) = ∑ i : Fin (n + 1), x i :=
  trace.sum_preserved k

/-- The final distillation state preserves the exact input sum. -/
theorem distillationTrace_finalState_sum_eq {n steps : ℕ}
    {x : Fin (n + 1) → ℝ}
    (trace : DistillationTrace n steps x) :
    distillationStateSum trace.finalState = ∑ i : Fin (n + 1), x i :=
  trace.sum_preserved (Fin.last steps)

/-- The final distillation state has the same represented sum as the initial
distillation state. -/
theorem distillationTrace_finalState_sum_eq_initial {n steps : ℕ}
    {x : Fin (n + 1) → ℝ}
    (trace : DistillationTrace n steps x) :
    distillationStateSum trace.finalState =
      distillationStateSum (distillationInitialState x) := by
  rw [distillationTrace_finalState_sum_eq trace,
    distillationInitialState_sum_eq x]

/-- The source termination condition unfolded at the final trace state. -/
theorem distillationTrace_terminatesWithinUnitRoundoff_iff {n steps : ℕ}
    {x : Fin (n + 1) → ℝ}
    (trace : DistillationTrace n steps x) (u : ℝ) :
    trace.terminatesWithinUnitRoundoff u ↔
      relError ((trace.finalState).values (Fin.last n))
        (∑ i : Fin (n + 1), x i) ≤ u := by
  rfl

/-- Source-facing relative-error guarantee at distillation termination. -/
theorem distillationTrace_finalComponent_relError_le {n steps : ℕ}
    {x : Fin (n + 1) → ℝ}
    (trace : DistillationTrace n steps x) {u : ℝ}
    (hterm : trace.terminatesWithinUnitRoundoff u) :
    relError trace.finalComponent (∑ i : Fin (n + 1), x i) ≤ u :=
  hterm

/-- Absolute-error consequence of the distillation termination predicate. -/
theorem distillationTrace_finalComponent_abs_error_le {n steps : ℕ}
    {x : Fin (n + 1) → ℝ}
    (trace : DistillationTrace n steps x) {u : ℝ}
    (hterm : trace.terminatesWithinUnitRoundoff u)
    (hsum : (∑ i : Fin (n + 1), x i) ≠ 0) :
    |trace.finalComponent - ∑ i : Fin (n + 1), x i| ≤
      u * |∑ i : Fin (n + 1), x i| := by
  have hden : 0 < |∑ i : Fin (n + 1), x i| := abs_pos.mpr hsum
  unfold DistillationTrace.terminatesWithinUnitRoundoff
    DistillationTrace.finalComponent relError at hterm
  rw [div_le_iff₀ hden] at hterm
  exact hterm

end NumStability
