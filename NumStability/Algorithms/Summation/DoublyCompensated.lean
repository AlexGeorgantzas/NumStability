-- Algorithms/Summation/DoublyCompensated.lean

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import NumStability.FloatingPoint.Model

namespace NumStability

open scoped BigOperators

/-!
# Doubly Compensated Summation

Reusable state, ordering, and rounded-trace APIs for Priest-style doubly
compensated summation. `PriestState`, `PriestStepTrace`, `priestStepTrace`,
`priestTrace`, and `fl_priestSum` expose every nested floating-point operation
and keep the decreasing-magnitude input condition explicit.

The trace follows Priest's method as presented by Higham in Algorithm 4.3
(§4.3). The attributed `2u` accuracy result for `n < β^(t-3)` depends on a
concrete finite-arithmetic model and additional assumptions, so it is not part
of this source-independent trace API.
-/

/-- Source-side weak ordering predicate for Algorithm 4.3: the supplied input
is in nonincreasing absolute value. -/
def priestSortedByDecreasingAbs {n : ℕ} (x : Fin (n + 1) → ℝ) : Prop :=
  ∀ i j : Fin (n + 1), i.val < j.val → |x j| ≤ |x i|

/-- Source-shaped strict ordering predicate for Algorithm 4.3: the supplied
input is in strictly decreasing absolute value, matching the displayed
inequalities before the loop. -/
def priestStrictlySortedByDecreasingAbs {n : ℕ}
    (x : Fin (n + 1) → ℝ) : Prop :=
  ∀ i j : Fin (n + 1), i.val < j.val → |x j| < |x i|

/-- The source-shaped strict order entails the weak order consumed by the
Algorithm 4.3 trace surface. -/
theorem priestSortedByDecreasingAbs_of_strict {n : ℕ}
    {x : Fin (n + 1) → ℝ}
    (h : priestStrictlySortedByDecreasingAbs x) :
    priestSortedByDecreasingAbs x := by
  intro i j hij
  exact le_of_lt (h i j hij)

/-- Persistent state of Priest doubly compensated summation: the running sum
`s` and correction `c`. -/
structure PriestState where
  s : ℝ
  c : ℝ

/-- Initial Priest state `s₁ = x₁; c₁ = 0` for a nonempty input. -/
noncomputable def priestInitialState {n : ℕ}
    (x : Fin (n + 1) → ℝ) : PriestState :=
  { s := x ⟨0, Nat.succ_pos n⟩, c := 0 }

/-- One source-level Priest loop trace, including every displayed intermediate
quantity. -/
structure PriestStepTrace where
  y : ℝ
  u : ℝ
  t : ℝ
  upsilon : ℝ
  z : ℝ
  s : ℝ
  c : ℝ

namespace PriestStepTrace

/-- The persistent state after a Priest step trace. -/
def nextState (t : PriestStepTrace) : PriestState :=
  { s := t.s, c := t.c }

end PriestStepTrace

/-- One rounded Priest doubly compensated summation step for input `x`. -/
noncomputable def priestStepTrace (fp : FPModel) (x : ℝ)
    (state : PriestState) : PriestStepTrace :=
  let y := fp.fl_add state.c x
  let u := fp.fl_sub x (fp.fl_sub y state.c)
  let t := fp.fl_add y state.s
  let upsilon := fp.fl_sub y (fp.fl_sub t state.s)
  let z := fp.fl_add u upsilon
  let s := fp.fl_add t z
  let c := fp.fl_sub z (fp.fl_sub s t)
  { y := y, u := u, t := t, upsilon := upsilon, z := z, s := s, c := c }

/-- Persistent-state update induced by one Priest step. -/
noncomputable def priestStep (fp : FPModel) (x : ℝ)
    (state : PriestState) : PriestState :=
  (priestStepTrace fp x state).nextState

/-- The `y_k = c_{k-1} + x_k` assignment in Algorithm 4.3. -/
theorem priestStepTrace_y (fp : FPModel) (x : ℝ) (state : PriestState) :
    (priestStepTrace fp x state).y = fp.fl_add state.c x := by
  rfl

/-- The `u_k = x_k - (y_k - c_{k-1})` assignment in Algorithm 4.3. -/
theorem priestStepTrace_u (fp : FPModel) (x : ℝ) (state : PriestState) :
    (priestStepTrace fp x state).u =
      fp.fl_sub x (fp.fl_sub (priestStepTrace fp x state).y state.c) := by
  rfl

/-- The `t_k = y_k + s_{k-1}` assignment in Algorithm 4.3. -/
theorem priestStepTrace_t (fp : FPModel) (x : ℝ) (state : PriestState) :
    (priestStepTrace fp x state).t =
      fp.fl_add (priestStepTrace fp x state).y state.s := by
  rfl

/-- The `υ_k = y_k - (t_k - s_{k-1})` assignment in Algorithm 4.3. -/
theorem priestStepTrace_upsilon (fp : FPModel) (x : ℝ)
    (state : PriestState) :
    (priestStepTrace fp x state).upsilon =
      fp.fl_sub (priestStepTrace fp x state).y
        (fp.fl_sub (priestStepTrace fp x state).t state.s) := by
  rfl

/-- The `z_k = u_k + υ_k` assignment in Algorithm 4.3. -/
theorem priestStepTrace_z (fp : FPModel) (x : ℝ) (state : PriestState) :
    (priestStepTrace fp x state).z =
      fp.fl_add (priestStepTrace fp x state).u
        (priestStepTrace fp x state).upsilon := by
  rfl

/-- The `s_k = t_k + z_k` assignment in Algorithm 4.3. -/
theorem priestStepTrace_s (fp : FPModel) (x : ℝ) (state : PriestState) :
    (priestStepTrace fp x state).s =
      fp.fl_add (priestStepTrace fp x state).t
        (priestStepTrace fp x state).z := by
  rfl

/-- The `c_k = z_k - (s_k - t_k)` assignment in Algorithm 4.3. -/
theorem priestStepTrace_c (fp : FPModel) (x : ℝ) (state : PriestState) :
    (priestStepTrace fp x state).c =
      fp.fl_sub (priestStepTrace fp x state).z
        (fp.fl_sub (priestStepTrace fp x state).s
          (priestStepTrace fp x state).t) := by
  rfl

/-- State after the first `k` Priest loop iterations beyond the initial
`s₁ = x₁` state. -/
noncomputable def priestPrefixState (fp : FPModel) {n : ℕ}
    (x : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n) : PriestState :=
  Fin.foldl k
    (fun state i =>
      priestStep fp
        (x ⟨i.val + 1,
          Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt hk)⟩)
        state)
    (priestInitialState x)

/-- The per-tail-index Priest step trace, with the input state obtained by
running all earlier loop iterations.  The index `i` addresses the source
indices `2:n` through `x (i+1)`. -/
noncomputable def priestTrace (fp : FPModel) {n : ℕ}
    (x : Fin (n + 1) → ℝ) (i : Fin n) : PriestStepTrace :=
  priestStepTrace fp
    (x ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    (priestPrefixState fp x i.val (Nat.le_of_lt i.isLt))

/-- Final Priest state after processing a nonempty input. -/
noncomputable def fl_priestState (fp : FPModel) {n : ℕ}
    (x : Fin (n + 1) → ℝ) : PriestState :=
  priestPrefixState fp x n (Nat.le_refl n)

/-- Final doubly compensated summation value returned by Algorithm 4.3. -/
noncomputable def fl_priestSum (fp : FPModel) {n : ℕ}
    (x : Fin (n + 1) → ℝ) : ℝ :=
  (fl_priestState fp x).s

/-- Final correction retained by Algorithm 4.3. -/
noncomputable def fl_priestCorrection (fp : FPModel) {n : ℕ}
    (x : Fin (n + 1) → ℝ) : ℝ :=
  (fl_priestState fp x).c

/-- The final Priest state is the explicit final prefix state. -/
theorem fl_priestState_eq_prefixState (fp : FPModel) {n : ℕ}
    (x : Fin (n + 1) → ℝ) :
    fl_priestState fp x = priestPrefixState fp x n (Nat.le_refl n) := by
  rfl

/-- The returned sum is the `s` field of the final Priest state. -/
theorem fl_priestSum_eq_state_s (fp : FPModel) {n : ℕ}
    (x : Fin (n + 1) → ℝ) :
    fl_priestSum fp x = (fl_priestState fp x).s := by
  rfl

/-- The retained correction is the `c` field of the final Priest state. -/
theorem fl_priestCorrection_eq_state_c (fp : FPModel) {n : ℕ}
    (x : Fin (n + 1) → ℝ) :
    fl_priestCorrection fp x = (fl_priestState fp x).c := by
  rfl

/-- Under exact arithmetic, Priest's doubly compensated state is the exact
source sum with zero retained correction. -/
theorem fl_priestState_exactWithUnitRoundoff (u0 : ℝ) (hu0 : 0 ≤ u0) :
    ∀ {n : ℕ} (x : Fin (n + 1) → ℝ),
      fl_priestState (FPModel.exactWithUnitRoundoff u0 hu0) x =
        { s := ∑ i : Fin (n + 1), x i, c := 0 }
  | 0, x => by
      simp [fl_priestState, priestPrefixState, priestInitialState]
  | n + 1, x => by
      let fp := FPModel.exactWithUnitRoundoff u0 hu0
      have hfold :
          fl_priestState fp x =
            priestStep fp (x (Fin.last (n + 1)))
              (fl_priestState fp
                (fun i : Fin (n + 1) => x i.castSucc)) := by
        unfold fl_priestState priestPrefixState
        rw [Fin.foldl_succ_last]
        congr 1
      rw [hfold, fl_priestState_exactWithUnitRoundoff u0 hu0
        (fun i : Fin (n + 1) => x i.castSucc)]
      simp [fp, priestStep, priestStepTrace, PriestStepTrace.nextState,
        FPModel.exactWithUnitRoundoff, Fin.sum_univ_castSucc, add_comm]

/-- Under exact arithmetic, Priest's returned sum is the exact source sum. -/
theorem fl_priestSum_exactWithUnitRoundoff (u0 : ℝ) (hu0 : 0 ≤ u0)
    {n : ℕ} (x : Fin (n + 1) → ℝ) :
    fl_priestSum (FPModel.exactWithUnitRoundoff u0 hu0) x =
      ∑ i : Fin (n + 1), x i := by
  have hstate := fl_priestState_exactWithUnitRoundoff u0 hu0 x
  simpa [fl_priestSum] using congrArg PriestState.s hstate

/-- Under exact arithmetic, Priest's retained correction is zero. -/
theorem fl_priestCorrection_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) {n : ℕ}
    (x : Fin (n + 1) → ℝ) :
    fl_priestCorrection (FPModel.exactWithUnitRoundoff u0 hu0) x = 0 := by
  have hstate := fl_priestState_exactWithUnitRoundoff u0 hu0 x
  simpa [fl_priestCorrection] using congrArg PriestState.c hstate

end NumStability
