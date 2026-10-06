-- Algorithms/Ch14GaussJordanSourceClosure.lean
--
-- Source-strength closure for Higham, Chapter 14, Algorithm 14.4 and
-- equations (14.25b)-(14.28).

import NumStability.Algorithms.GaussJordanPivoting
import NumStability.Algorithms.Ch14GaussJordanQConstruction

namespace NumStability.Ch14Ext

open Finset BigOperators
open NumStability

/-! ## Exact correctness of Algorithm 14.4 -/

/-- A vector satisfies every equation represented by a mutable GJE state. -/
def ch14ext_StateSatisfies {n : Nat} (s : Ch14GJEState n) (x : Fin n -> Real) : Prop :=
  forall i : Fin n, matMulVec n s.matrix x i = s.rhs i

/-- Two GJE states have exactly the same solution set. -/
def ch14ext_SameSolutions {n : Nat} (s t : Ch14GJEState n) : Prop :=
  forall x : Fin n -> Real, ch14ext_StateSatisfies s x <-> ch14ext_StateSatisfies t x

/-- The intermediate state after Algorithm 14.4's tail-row and RHS swaps. -/
noncomputable def ch14ext_tailPivotState {n : Nat} (s : Ch14GJEState n) (k : Fin n) :
    Ch14GJEState n where
  matrix := ch14ext_tailPivotMatrix s k
  rhs := ch14ext_tailPivotRhs s k

/-- On a state reduced through the columns before `k`, the source's tail-only
    row swap has the same matrix rows as the corresponding full row swap. -/
theorem ch14ext_tailPivotMatrix_eq_permuted_of_reduced {n : Nat}
    (s : Ch14GJEState n) (k i j : Fin n)
    (hred : ch14ext_FullReducedUpTo k.val s) :
    ch14ext_tailPivotMatrix s k i j =
      s.matrix (Equiv.swap k (ch14ext_pivotRow s.matrix k) i) j := by
  let r := ch14ext_pivotRow s.matrix k
  have hkr : k <= r := ch14ext_pivotRow_ge s.matrix k
  by_cases hkj : k <= j
  · simp [ch14ext_tailPivotMatrix, ch14ext_tailSwapRows, hkj]
  · have hjk : j.val < k.val := by
      simpa [Fin.not_le] using hkj
    rw [ch14ext_tailPivotMatrix_before s k i j (by exact hjk)]
    by_cases hik : k <= i
    · have hswap : k <= Equiv.swap k r i := ch14ext_swap_ge hkr hik
      have hij : i ≠ j := by
        intro h
        subst i
        omega
      have hsj : Equiv.swap k r i ≠ j := by
        intro h
        have hv := congrArg Fin.val h
        omega
      rw [hred j hjk i hij, hred j hjk (Equiv.swap k r i) hsj]
    · have hiklt : i < k := lt_of_not_ge hik
      have hikne : i ≠ k := ne_of_lt hiklt
      have hirne : i ≠ r := by
        intro h
        subst i
        exact (not_le_of_gt hiklt) hkr
      rw [Equiv.swap_apply_of_ne_of_ne hikne hirne]

/-- The simultaneous source swaps preserve the represented system exactly. -/
theorem ch14ext_tailPivotState_sameSolutions {n : Nat}
    (s : Ch14GJEState n) (k : Fin n)
    (hred : ch14ext_FullReducedUpTo k.val s) :
    ch14ext_SameSolutions s (ch14ext_tailPivotState s k) := by
  intro x
  let sigma := Equiv.swap k (ch14ext_pivotRow s.matrix k)
  have hrow : forall i j : Fin n,
      (ch14ext_tailPivotState s k).matrix i j = s.matrix (sigma i) j := by
    intro i j
    exact ch14ext_tailPivotMatrix_eq_permuted_of_reduced s k i j hred
  have hrhs : forall i : Fin n,
      (ch14ext_tailPivotState s k).rhs i = s.rhs (sigma i) := by
    intro i
    rfl
  constructor
  · intro hs i
    change (forall a : Fin n, matMulVec n s.matrix x a = s.rhs a) at hs
    unfold matMulVec
    simp_rw [hrow i]
    rw [hrhs i]
    simpa [matMulVec] using hs (sigma i)
  · intro ht i
    change (forall a : Fin n,
      matMulVec n (ch14ext_tailPivotState s k).matrix x a =
        (ch14ext_tailPivotState s k).rhs a) at ht
    have h := ht (sigma.symm i)
    change matMulVec n (ch14ext_tailPivotState s k).matrix x (sigma.symm i) =
      (ch14ext_tailPivotState s k).rhs (sigma.symm i) at h
    unfold matMulVec at h
    simp_rw [hrow (sigma.symm i)] at h
    rw [hrhs (sigma.symm i)] at h
    simpa [matMulVec, sigma] using h

/-- The elimination part of a successful Algorithm 14.4 step is reversible,
    hence preserves the complete solution set of the pivoted state. -/
theorem ch14ext_fullStep_sameSolutions_tailPivot {n : Nat}
    (s : Ch14GJEState n) (k : Fin n)
    (hred : ch14ext_FullReducedUpTo k.val s) :
    ch14ext_SameSolutions (ch14ext_tailPivotState s k) (ch14ext_fullStep s k) := by
  intro x
  let p := ch14ext_tailPivotState s k
  let m : Fin n -> Real := ch14ext_fullMultiplier s k
  have hmatPivot : forall j : Fin n,
      (ch14ext_fullStep s k).matrix k j = p.matrix k j := by
    intro j
    simp [ch14ext_fullStep, p, ch14ext_tailPivotState]
  have hrhsPivot : (ch14ext_fullStep s k).rhs k = p.rhs k := by
    simp [ch14ext_fullStep, p, ch14ext_tailPivotState]
  have hmatOff : forall i : Fin n, i ≠ k -> forall j : Fin n,
      (ch14ext_fullStep s k).matrix i j = p.matrix i j - m i * p.matrix k j := by
    intro i hik j
    by_cases hkj : k <= j
    · simp [ch14ext_fullStep, hik, hkj, p, m, ch14ext_tailPivotState]
    · have hjk : j < k := lt_of_not_ge hkj
      have hpkj : ch14ext_tailPivotMatrix s k k j = 0 := by
        rw [ch14ext_tailPivotMatrix_before s k k j hjk]
        exact hred j hjk k (ne_of_gt hjk)
      simp [ch14ext_fullStep, hik, hkj, p, m, ch14ext_tailPivotState, hpkj]
  have hrhsOff : forall i : Fin n, i ≠ k ->
      (ch14ext_fullStep s k).rhs i = p.rhs i - m i * p.rhs k := by
    intro i hik
    simp [ch14ext_fullStep, hik, p, m, ch14ext_tailPivotState]
  constructor
  · intro hp
    change (forall a : Fin n, matMulVec n p.matrix x a = p.rhs a) at hp
    change forall a : Fin n,
      matMulVec n (ch14ext_fullStep s k).matrix x a = (ch14ext_fullStep s k).rhs a
    intro i
    by_cases hik : i = k
    · subst i
      unfold matMulVec
      simp_rw [hmatPivot]
      rw [hrhsPivot]
      simpa [matMulVec] using hp k
    · unfold matMulVec
      simp_rw [hmatOff i hik]
      rw [hrhsOff i hik]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      simpa [matMulVec] using
        congrArg₂ (fun a b : Real => a - m i * b) (hp i) (hp k)
  · intro hstep
    change (forall a : Fin n,
      matMulVec n (ch14ext_fullStep s k).matrix x a =
        (ch14ext_fullStep s k).rhs a) at hstep
    change forall a : Fin n, matMulVec n p.matrix x a = p.rhs a
    intro i
    by_cases hik : i = k
    · subst i
      have h := hstep k
      unfold matMulVec at h
      simp_rw [hmatPivot] at h
      rw [hrhsPivot] at h
      simpa [matMulVec] using h
    · have hi := hstep i
      have hk := hstep k
      unfold matMulVec at hi hk
      simp_rw [hmatOff i hik] at hi
      rw [hrhsOff i hik] at hi
      simp_rw [hmatPivot] at hk
      rw [hrhsPivot] at hk
      unfold matMulVec
      simp_rw [sub_mul] at hi
      rw [Finset.sum_sub_distrib] at hi
      simp_rw [mul_assoc] at hi
      rw [← Finset.mul_sum] at hi
      rw [hk] at hi
      linarith

/-- One complete successful loop body preserves the original linear system. -/
theorem ch14ext_fullStep_sameSolutions {n : Nat}
    (s : Ch14GJEState n) (k : Fin n)
    (hred : ch14ext_FullReducedUpTo k.val s) :
    ch14ext_SameSolutions s (ch14ext_fullStep s k) := by
  intro x
  exact (ch14ext_tailPivotState_sameSolutions s k hred x).trans
    (ch14ext_fullStep_sameSolutions_tailPivot s k hred x)

/-- Every successful prefix of the literal loop represents the original
    system, in both directions. -/
theorem ch14ext_fullReduce_sameSolutions {n : Nat} (s : Ch14GJEState n)
    (hpiv : forall t : Nat, forall ht : t < n,
      ch14ext_tailPivotMatrix (ch14ext_fullReduce s t) ⟨t, ht⟩ ⟨t, ht⟩ ⟨t, ht⟩ ≠ 0) :
    forall t : Nat, ch14ext_SameSolutions s (ch14ext_fullReduce s t) := by
  intro t
  induction t with
  | zero =>
      intro x
      simp [ch14ext_fullReduce]
  | succ t ih =>
      by_cases ht : t < n
      · have hstep : ch14ext_fullReduce s (t + 1) =
            ch14ext_fullStep (ch14ext_fullReduce s t) ⟨t, ht⟩ := by
          simp [ch14ext_fullReduce, ht]
        rw [hstep]
        intro x
        exact (ih x).trans
          (ch14ext_fullStep_sameSolutions (ch14ext_fullReduce s t) ⟨t, ht⟩
            (ch14ext_fullReduce_ReducedUpTo s hpiv t) x)
      · have hstep : ch14ext_fullReduce s (t + 1) = ch14ext_fullReduce s t := by
          simp [ch14ext_fullReduce, ht]
        rw [hstep]
        exact ih

/-- Once a column has been processed, later literal loop steps leave it
    exactly unchanged. -/
theorem ch14ext_fullReduce_processed_column_stable {n : Nat}
    (s : Ch14GJEState n) (start steps : Nat) (i j : Fin n)
    (hj : j.val < start) :
    (ch14ext_fullReduce s (start + steps)).matrix i j =
      (ch14ext_fullReduce s start).matrix i j := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      have hsum : start + (steps + 1) = (start + steps) + 1 := by omega
      rw [hsum]
      by_cases ht : start + steps < n
      · have hjk : j < (⟨start + steps, ht⟩ : Fin n) := by
          change j.val < start + steps
          omega
        calc
          (ch14ext_fullReduce s ((start + steps) + 1)).matrix i j =
              (ch14ext_fullStep (ch14ext_fullReduce s (start + steps))
                ⟨start + steps, ht⟩).matrix i j := by
                  simp [ch14ext_fullReduce, ht]
          _ = (ch14ext_fullReduce s (start + steps)).matrix i j :=
                ch14ext_fullStep_matrix_before
                  (ch14ext_fullReduce s (start + steps)) ⟨start + steps, ht⟩ i j hjk
          _ = (ch14ext_fullReduce s start).matrix i j := ih
      · calc
          (ch14ext_fullReduce s ((start + steps) + 1)).matrix i j =
              (ch14ext_fullReduce s (start + steps)).matrix i j := by
                simp [ch14ext_fullReduce, ht]
          _ = (ch14ext_fullReduce s start).matrix i j := ih

/-- At its own iteration, the diagonal entry is the selected nonzero pivot. -/
theorem ch14ext_fullReduce_diag_after_step_eq_pivot {n : Nat}
    (s : Ch14GJEState n) (i : Fin n) :
    (ch14ext_fullReduce s (i.val + 1)).matrix i i =
      ch14ext_tailPivotMatrix (ch14ext_fullReduce s i.val) i i i := by
  have hi : i.val < n := i.isLt
  have hk : (⟨i.val, hi⟩ : Fin n) = i := Fin.ext rfl
  rw [show i.val + 1 = Nat.succ i.val by omega]
  simp only [ch14ext_fullReduce]
  rw [dif_pos hi, hk]
  simp [ch14ext_fullStep]

/-- The operational nonzero-pivot success condition implies every final
    diagonal entry is nonzero; no extra final-state premise is required. -/
theorem ch14ext_fullReduce_final_diag_ne_zero {n : Nat}
    (s : Ch14GJEState n)
    (hpiv : forall t : Nat, forall ht : t < n,
      ch14ext_tailPivotMatrix (ch14ext_fullReduce s t) ⟨t, ht⟩ ⟨t, ht⟩ ⟨t, ht⟩ ≠ 0)
    (i : Fin n) :
    (ch14ext_fullReduce s n).matrix i i ≠ 0 := by
  have hle : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
  have hstable := ch14ext_fullReduce_processed_column_stable s (i.val + 1)
    (n - (i.val + 1)) i i (Nat.lt_succ_self i.val)
  have hsum : i.val + 1 + (n - (i.val + 1)) = n := Nat.add_sub_of_le hle
  rw [hsum, ch14ext_fullReduce_diag_after_step_eq_pivot s i] at hstable
  rw [hstable]
  have hp := hpiv i.val i.isLt
  simpa using hp

/-- The vector produced by the final source scaling satisfies the final
    diagonal system. -/
theorem ch14ext_fullSolution_satisfies_final {n : Nat}
    (s : Ch14GJEState n)
    (hpiv : forall t : Nat, forall ht : t < n,
      ch14ext_tailPivotMatrix (ch14ext_fullReduce s t) ⟨t, ht⟩ ⟨t, ht⟩ ⟨t, ht⟩ ≠ 0) :
    ch14ext_StateSatisfies (ch14ext_fullReduce s n) (ch14ext_fullSolution s) := by
  classical
  intro i
  unfold matMulVec
  rw [Finset.sum_eq_single i]
  · rw [mul_comm]
    exact ch14ext_fullSolution_diag_equation s i
      (ch14ext_fullReduce_final_diag_ne_zero s hpiv i)
  · intro j _ hji
    rw [ch14ext_fullReduce_diagonal s hpiv i j (Ne.symm hji), zero_mul]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ i))

/-- **Algorithm 14.4, end-to-end exact correctness.**  If every selected
    pivot is nonzero, the literal pivot/swap/eliminate/scale program returns a
    solution of the original system represented by `s`. -/
theorem ch14ext_algorithm14_4_correct {n : Nat}
    (s : Ch14GJEState n)
    (hpiv : forall t : Nat, forall ht : t < n,
      ch14ext_tailPivotMatrix (ch14ext_fullReduce s t) ⟨t, ht⟩ ⟨t, ht⟩ ⟨t, ht⟩ ≠ 0) :
    ch14ext_StateSatisfies s (ch14ext_fullSolution s) := by
  exact (ch14ext_fullReduce_sameSolutions s hpiv n (ch14ext_fullSolution s)).mpr
    (ch14ext_fullSolution_satisfies_final s hpiv)

/-- Matrix/RHS presentation of the end-to-end Algorithm 14.4 theorem. -/
theorem ch14ext_algorithm14_4_solves_original {n : Nat}
    (A : Fin n -> Fin n -> Real) (b : Fin n -> Real)
    (hpiv : forall t : Nat, forall ht : t < n,
      ch14ext_tailPivotMatrix
          (ch14ext_fullReduce ({ matrix := A, rhs := b } : Ch14GJEState n) t)
          ⟨t, ht⟩ ⟨t, ht⟩ ⟨t, ht⟩ ≠ 0) :
    forall i : Fin n,
      matMulVec n A (ch14ext_fullSolution ({ matrix := A, rhs := b } : Ch14GJEState n)) i =
        b i := by
  exact ch14ext_algorithm14_4_correct ({ matrix := A, rhs := b } : Ch14GJEState n) hpiv

/-! ## Literal local errors in (14.25b) and (14.26) -/

/-- The active matrix block in the source's second GJE stage: only rows above
    the current pivot and columns at or to its right are updated. -/
abbrev ch14ext_gjeSourceActive {n : Nat} (k i j : Fin n) : Prop :=
  i.val < k.val ∧ k.val ≤ j.val

/-- Source-faithful rounded matrix step. Entries outside the active upper-right
    block are retained, as encoded by Higham's displayed block `Delta_k`. -/
noncomputable def ch14ext_gjeSourceStepMatrix (fp : FPModel) (n : Nat)
    (U : Fin n -> Fin n -> Real) (k : Fin n) : Fin n -> Fin n -> Real :=
  fun i j => if ch14ext_gjeSourceActive k i j
    then ch14ext_gjeStepMatrix fp n U k i j
    else U i j

/-- Source-faithful rounded RHS step: only rows above the current pivot are
    updated in the second stage. -/
noncomputable def ch14ext_gjeSourceStepVec (fp : FPModel) (n : Nat)
    (U : Fin n -> Fin n -> Real) (k : Fin n) (x : Fin n -> Real) : Fin n -> Real :=
  fun i => if i.val < k.val then ch14ext_gjeStepVec fp n U k x i else x i

/-- The concrete local matrix error in (14.25a). -/
noncomputable def ch14ext_gjeSourceDelta (fp : FPModel) (n : Nat)
    (U : Fin n -> Fin n -> Real) (k : Fin n) : Fin n -> Fin n -> Real :=
  fun i j => ch14ext_gjeSourceStepMatrix fp n U k i j -
    matMul n (ch14ext_gjeStageMatrix n U k) U i j

/-- The concrete local RHS error in (14.26). -/
noncomputable def ch14ext_gjeSourceF (fp : FPModel) (n : Nat)
    (U : Fin n -> Fin n -> Real) (k : Fin n) (x : Fin n -> Real) : Fin n -> Real :=
  fun i => ch14ext_gjeSourceStepVec fp n U k x i -
    matMulVec n (ch14ext_gjeStageMatrix n U k) x i

/-- An elementary GJE stage acts as the identity on entry `(i,j)` whenever
    either row `i` is not above the pivot or column `j` is left of it. -/
theorem ch14ext_gjeStageMatrix_mul_eq_self_of_inactive {n : Nat}
    (U : Fin n -> Fin n -> Real) (k i j : Fin n)
    (hUpper : forall a b : Fin n, b.val < a.val -> U a b = 0)
    (hinactive : k.val ≤ i.val ∨ j.val < k.val) :
    matMul n (ch14ext_gjeStageMatrix n U k) U i j = U i j := by
  rw [show matMul n (ch14ext_gjeStageMatrix n U k) U i j =
      U i j - ch14ext_gjeMultVec n U k i * U k j by
    exact ch14ext_gjeStageMatrix_mulVec_row n U k i j]
  rcases hinactive with hki | hjk
  · rw [ch14ext_gjeMultVec_zero_of_upper n U k i hUpper hki, zero_mul, sub_zero]
  · rw [hUpper k j hjk, mul_zero, sub_zero]

/-- The concrete matrix error is identically zero outside Higham's displayed
    upper-right error block. -/
theorem ch14ext_gjeSourceDelta_zero_of_inactive {n : Nat}
    (fp : FPModel) (U : Fin n -> Fin n -> Real) (k i j : Fin n)
    (hUpper : forall a b : Fin n, b.val < a.val -> U a b = 0)
    (hinactive : k.val ≤ i.val ∨ j.val < k.val) :
    ch14ext_gjeSourceDelta fp n U k i j = 0 := by
  have hnot : ¬ ch14ext_gjeSourceActive k i j := by
    intro h
    rcases h with ⟨hik, hkj⟩
    rcases hinactive with hki | hjk <;> omega
  unfold ch14ext_gjeSourceDelta ch14ext_gjeSourceStepMatrix
  rw [if_neg hnot, ch14ext_gjeStageMatrix_mul_eq_self_of_inactive U k i j hUpper hinactive]
  ring

/-- One source-faithful rounded matrix step preserves upper triangularity. -/
theorem ch14ext_gjeSourceStepMatrix_upper {n : Nat}
    (fp : FPModel) (U : Fin n -> Fin n -> Real) (k : Fin n)
    (hUpper : forall a b : Fin n, b.val < a.val -> U a b = 0) :
    forall i j : Fin n, j.val < i.val ->
      ch14ext_gjeSourceStepMatrix fp n U k i j = 0 := by
  intro i j hji
  have hnot : ¬ ch14ext_gjeSourceActive k i j := by
    intro h
    rcases h with ⟨hik, hkj⟩
    omega
  simp [ch14ext_gjeSourceStepMatrix, hnot, hUpper i j hji]

/-- **Higham (14.25a-b), literal local matrix equation and support.** -/
theorem ch14ext_gjeSource_local_matrix_14_25 {n : Nat}
    (fp : FPModel) (U : Fin n -> Fin n -> Real) (k : Fin n)
    (hUpper : forall a b : Fin n, b.val < a.val -> U a b = 0)
    (hpiv : U k k ≠ 0) (h3 : gammaValid fp 3) :
    (forall i j : Fin n,
      ch14ext_gjeSourceStepMatrix fp n U k i j =
        matMul n (ch14ext_gjeStageMatrix n U k) U i j +
          ch14ext_gjeSourceDelta fp n U k i j) ∧
    (forall i j : Fin n,
      |ch14ext_gjeSourceDelta fp n U k i j| ≤
        gamma fp 3 * matMul n (absMatrix n (ch14ext_gjeStageMatrix n U k))
          (absMatrix n U) i j) ∧
    (forall i j : Fin n, k.val ≤ i.val ->
      ch14ext_gjeSourceDelta fp n U k i j = 0) ∧
    (forall i j : Fin n, j.val < k.val ->
      ch14ext_gjeSourceDelta fp n U k i j = 0) := by
  constructor
  · intro i j
    unfold ch14ext_gjeSourceDelta
    ring
  constructor
  · intro i j
    by_cases hactive : ch14ext_gjeSourceActive k i j
    · have h := ch14ext_gjeStepMatrix_hComp fp n U k hpiv h3 i j
      unfold ch14ext_gjeSourceDelta matMul absMatrix
      rw [ch14ext_gjeSourceStepMatrix, if_pos hactive]
      exact h
    · have hinactive : k.val ≤ i.val ∨ j.val < k.val := by
        unfold ch14ext_gjeSourceActive at hactive
        omega
      rw [ch14ext_gjeSourceDelta_zero_of_inactive fp U k i j hUpper hinactive,
        abs_zero]
      exact mul_nonneg (gamma_nonneg fp h3)
        (Finset.sum_nonneg (fun l _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  constructor
  · intro i j hki
    exact ch14ext_gjeSourceDelta_zero_of_inactive fp U k i j hUpper (Or.inl hki)
  · intro i j hjk
    exact ch14ext_gjeSourceDelta_zero_of_inactive fp U k i j hUpper (Or.inr hjk)

/-- An elementary stage acts as the identity on vector row `i` at or below
    the current pivot. -/
theorem ch14ext_gjeStageMatrix_vec_eq_self_of_inactive {n : Nat}
    (U : Fin n -> Fin n -> Real) (k i : Fin n) (x : Fin n -> Real)
    (hUpper : forall a b : Fin n, b.val < a.val -> U a b = 0)
    (hki : k.val ≤ i.val) :
    matMulVec n (ch14ext_gjeStageMatrix n U k) x i = x i := by
  unfold matMulVec
  rw [ch14ext_gjeStageMatrix_apply,
    ch14ext_gjeMultVec_zero_of_upper n U k i hUpper hki, zero_mul, sub_zero]

/-- The concrete RHS error has exactly the row support printed in (14.26). -/
theorem ch14ext_gjeSourceF_zero_of_inactive {n : Nat}
    (fp : FPModel) (U : Fin n -> Fin n -> Real) (k i : Fin n) (x : Fin n -> Real)
    (hUpper : forall a b : Fin n, b.val < a.val -> U a b = 0)
    (hki : k.val ≤ i.val) :
    ch14ext_gjeSourceF fp n U k x i = 0 := by
  have hnot : ¬ i.val < k.val := by omega
  unfold ch14ext_gjeSourceF ch14ext_gjeSourceStepVec
  rw [if_neg hnot, ch14ext_gjeStageMatrix_vec_eq_self_of_inactive U k i x hUpper hki]
  ring

/-- **Higham (14.26), literal local RHS equation and support.** -/
theorem ch14ext_gjeSource_local_rhs_14_26 {n : Nat}
    (fp : FPModel) (U : Fin n -> Fin n -> Real) (k : Fin n) (x : Fin n -> Real)
    (hUpper : forall a b : Fin n, b.val < a.val -> U a b = 0)
    (hpiv : U k k ≠ 0) (h3 : gammaValid fp 3) :
    (forall i : Fin n,
      ch14ext_gjeSourceStepVec fp n U k x i =
        matMulVec n (ch14ext_gjeStageMatrix n U k) x i +
          ch14ext_gjeSourceF fp n U k x i) ∧
    (forall i : Fin n,
      |ch14ext_gjeSourceF fp n U k x i| ≤
        gamma fp 3 * matMulVec n (absMatrix n (ch14ext_gjeStageMatrix n U k))
          (absVec n x) i) ∧
    (forall i : Fin n, k.val ≤ i.val ->
      ch14ext_gjeSourceF fp n U k x i = 0) := by
  constructor
  · intro i
    unfold ch14ext_gjeSourceF
    ring
  constructor
  · intro i
    by_cases hactive : i.val < k.val
    · have h := ch14ext_gjeStepVec_hComp fp n U k x hpiv h3 i
      unfold ch14ext_gjeSourceF matMulVec absMatrix absVec
      rw [ch14ext_gjeSourceStepVec, if_pos hactive]
      exact h
    · have hki : k.val ≤ i.val := by omega
      rw [ch14ext_gjeSourceF_zero_of_inactive fp U k i x hUpper hki, abs_zero]
      exact mul_nonneg (gamma_nonneg fp h3)
        (Finset.sum_nonneg (fun l _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  · intro i hki
    exact ch14ext_gjeSourceF_zero_of_inactive fp U k i x hUpper hki

/-- A later GJE stage leaves an earlier supported local matrix error unchanged,
    which is the structural identity used between (14.26) and (14.27). -/
theorem ch14ext_gjeStageMatrix_mul_sourceDelta_of_ge {n : Nat}
    (fp : FPModel) (Ufuture U : Fin n -> Fin n -> Real)
    (kfuture k : Fin n)
    (hUpper : forall a b : Fin n, b.val < a.val -> U a b = 0)
    (hkk : k.val ≤ kfuture.val) :
    matMul n (ch14ext_gjeStageMatrix n Ufuture kfuture)
        (ch14ext_gjeSourceDelta fp n U k) =
      ch14ext_gjeSourceDelta fp n U k := by
  funext i j
  change (∑ l : Fin n,
    ch14ext_gjeStageMatrix n Ufuture kfuture i l *
      ch14ext_gjeSourceDelta fp n U k l j) = _
  rw [ch14ext_gjeStageMatrix_apply]
  rw [ch14ext_gjeSourceDelta_zero_of_inactive fp U k kfuture j hUpper (Or.inl hkk)]
  ring

/-- A later GJE stage likewise leaves an earlier supported RHS error unchanged. -/
theorem ch14ext_gjeStageMatrix_mul_sourceF_of_ge {n : Nat}
    (fp : FPModel) (Ufuture U : Fin n -> Fin n -> Real)
    (kfuture k : Fin n) (x : Fin n -> Real)
    (hUpper : forall a b : Fin n, b.val < a.val -> U a b = 0)
    (hkk : k.val ≤ kfuture.val) :
    matMulVec n (ch14ext_gjeStageMatrix n Ufuture kfuture)
        (ch14ext_gjeSourceF fp n U k x) =
      ch14ext_gjeSourceF fp n U k x := by
  funext i
  unfold matMulVec
  rw [ch14ext_gjeStageMatrix_apply]
  rw [ch14ext_gjeSourceF_zero_of_inactive fp U k kfuture x hUpper hkk]
  ring

/-! ## Support-driven, unpropagated error sums -/

/-- Pointwise sum of the first `steps` local matrix errors. -/
noncomputable def ch14ext_matrixErrorSum {n : Nat}
    (E : Nat -> Fin n -> Fin n -> Real) (steps : Nat) : Fin n -> Fin n -> Real :=
  fun i j => ∑ t ∈ Finset.range steps, E t i j

/-- Pointwise sum of the first `steps` local RHS errors. -/
noncomputable def ch14ext_vecErrorSum {n : Nat}
    (f : Nat -> Fin n -> Real) (steps : Nat) : Fin n -> Real :=
  fun i => ∑ t ∈ Finset.range steps, f t i

@[simp] theorem ch14ext_matrixErrorSum_zero {n : Nat}
    (E : Nat -> Fin n -> Fin n -> Real) :
    ch14ext_matrixErrorSum E 0 = fun _ _ => 0 := by
  funext i j
  simp [ch14ext_matrixErrorSum]

theorem ch14ext_matrixErrorSum_succ {n : Nat}
    (E : Nat -> Fin n -> Fin n -> Real) (steps : Nat) :
    ch14ext_matrixErrorSum E (steps + 1) =
      fun i j => ch14ext_matrixErrorSum E steps i j + E steps i j := by
  funext i j
  simp [ch14ext_matrixErrorSum, Finset.sum_range_succ]

@[simp] theorem ch14ext_vecErrorSum_zero {n : Nat}
    (f : Nat -> Fin n -> Real) :
    ch14ext_vecErrorSum f 0 = fun _ => 0 := by
  funext i
  simp [ch14ext_vecErrorSum]

theorem ch14ext_vecErrorSum_succ {n : Nat}
    (f : Nat -> Fin n -> Real) (steps : Nat) :
    ch14ext_vecErrorSum f (steps + 1) =
      fun i => ch14ext_vecErrorSum f steps i + f steps i := by
  funext i
  simp [ch14ext_vecErrorSum, Finset.sum_range_succ]

/-- If a stage fixes every earlier local matrix error, it fixes their sum. -/
theorem ch14ext_matMul_matrixErrorSum_of_fixed {n : Nat}
    (A : Fin n -> Fin n -> Real) (E : Nat -> Fin n -> Fin n -> Real) :
    forall steps : Nat,
      (forall t : Nat, t < steps -> matMul n A (E t) = E t) ->
      matMul n A (ch14ext_matrixErrorSum E steps) =
        ch14ext_matrixErrorSum E steps := by
  intro steps
  induction steps with
  | zero =>
      intro _
      ext i j
      simp [ch14ext_matrixErrorSum, matMul]
  | succ steps ih =>
      intro hfix
      have hprev : forall t : Nat, t < steps -> matMul n A (E t) = E t :=
        fun t ht => hfix t (Nat.lt_trans ht (Nat.lt_succ_self steps))
      rw [show steps + 1 = Nat.succ steps by omega,
        ch14ext_matrixErrorSum_succ, matMul_add_right, ih hprev,
        hfix steps (Nat.lt_succ_self steps)]

/-- If a stage fixes every earlier local RHS error, it fixes their sum. -/
theorem ch14ext_matMulVec_vecErrorSum_of_fixed {n : Nat}
    (A : Fin n -> Fin n -> Real) (f : Nat -> Fin n -> Real) :
    forall steps : Nat,
      (forall t : Nat, t < steps -> matMulVec n A (f t) = f t) ->
      matMulVec n A (ch14ext_vecErrorSum f steps) =
        ch14ext_vecErrorSum f steps := by
  intro steps
  induction steps with
  | zero =>
      intro _
      ext i
      simp [ch14ext_vecErrorSum, matMulVec]
  | succ steps ih =>
      intro hfix
      have hprev : forall t : Nat, t < steps -> matMulVec n A (f t) = f t :=
        fun t ht => hfix t (Nat.lt_trans ht (Nat.lt_succ_self steps))
      rw [show steps + 1 = Nat.succ steps by omega,
        ch14ext_vecErrorSum_succ, matMulVec_add_right, ih hprev,
        hfix steps (Nat.lt_succ_self steps)]

/-- Exact telescoping with unpropagated matrix errors. The absence of stage
    products in front of the error sum is a conclusion of `hfuture`. -/
theorem ch14ext_gje_unpropagated_matrix_recurrence {n : Nat}
    (Nhat : Fin n -> Fin n -> Fin n -> Real)
    (V E : Nat -> Fin n -> Fin n -> Real) (start steps : Nat)
    (hidx : forall t : Nat, t < steps -> start + t < n)
    (hrec : forall t : Nat, (ht : t < steps) ->
      V (start + (t + 1)) =
        fun i j => matMul n (Nhat ⟨start + t, hidx t ht⟩) (V (start + t)) i j +
          E t i j)
    (hfuture : forall r q : Nat, r < q -> (hq : q < steps) ->
      matMul n (Nhat ⟨start + q, hidx q hq⟩) (E r) = E r) :
    V (start + steps) =
      fun i j =>
        matMul n (gje_cumulative_product n Nhat start (start + steps)) (V start) i j +
          ch14ext_matrixErrorSum E steps i j := by
  induction steps with
  | zero =>
      rw [Nat.add_zero,
        gje_cumulative_product_base n Nhat (le_refl start), matMul_id_left]
      funext i j
      simp [ch14ext_matrixErrorSum]
  | succ steps ih =>
      have hlt : steps < steps + 1 := Nat.lt_succ_self steps
      have htop : start + steps < n := hidx steps hlt
      have hidxPrev : forall t : Nat, t < steps -> start + t < n :=
        fun t ht => hidx t (Nat.lt_trans ht hlt)
      have hrecPrev : forall t : Nat, (ht : t < steps) ->
          V (start + (t + 1)) =
            fun i j => matMul n (Nhat ⟨start + t, hidxPrev t ht⟩) (V (start + t)) i j +
              E t i j := by
        intro t ht
        simpa using hrec t (Nat.lt_trans ht hlt)
      have hfuturePrev : forall r q : Nat, r < q -> (hq : q < steps) ->
          matMul n (Nhat ⟨start + q, hidxPrev q hq⟩) (E r) = E r := by
        intro r q hrq hq
        simpa using hfuture r q hrq (Nat.lt_trans hq hlt)
      have ih' := ih hidxPrev hrecPrev hfuturePrev
      let k : Fin n := ⟨start + steps, htop⟩
      let P := gje_cumulative_product n Nhat start (start + steps)
      have hstepIndex : start + (steps + 1) - 1 = start + steps := by omega
      have hprod : gje_cumulative_product n Nhat start (start + (steps + 1)) =
          matMul n (Nhat k) P := by
        have hstart : start < start + (steps + 1) := by omega
        have hfin : start + (steps + 1) - 1 < n := by
          rw [hstepIndex]
          exact htop
        rw [gje_cumulative_product_step n Nhat hstart hfin]
        simp [hstepIndex, k, P]
      have hfix : matMul n (Nhat k) (ch14ext_matrixErrorSum E steps) =
          ch14ext_matrixErrorSum E steps := by
        apply ch14ext_matMul_matrixErrorSum_of_fixed (A := Nhat k) (E := E) steps
        intro r hr
        simpa [k] using hfuture r steps hr hlt
      have hlast := hrec steps hlt
      have hlast' : V (start + (steps + 1)) =
          fun i j => matMul n (Nhat k) (V (start + steps)) i j + E steps i j := by
        simpa [k] using hlast
      rw [hlast', ih']
      rw [show matMul n (Nhat k)
          (fun a b => matMul n P (V start) a b +
            ch14ext_matrixErrorSum E steps a b) =
          (fun i j => matMul n (Nhat k) (matMul n P (V start)) i j +
            matMul n (Nhat k) (ch14ext_matrixErrorSum E steps) i j) by
        exact matMul_add_right n (Nhat k) (matMul n P (V start))
          (ch14ext_matrixErrorSum E steps)]
      rw [hfix, hprod, matMul_assoc, ch14ext_matrixErrorSum_succ]
      funext i j
      ring

/-- Vector counterpart of the support-driven unpropagated recurrence. -/
theorem ch14ext_gje_unpropagated_rhs_recurrence {n : Nat}
    (Nhat : Fin n -> Fin n -> Fin n -> Real)
    (xseq f : Nat -> Fin n -> Real) (start steps : Nat)
    (hidx : forall t : Nat, t < steps -> start + t < n)
    (hrec : forall t : Nat, (ht : t < steps) ->
      xseq (start + (t + 1)) =
        fun i => matMulVec n (Nhat ⟨start + t, hidx t ht⟩) (xseq (start + t)) i +
          f t i)
    (hfuture : forall r q : Nat, r < q -> (hq : q < steps) ->
      matMulVec n (Nhat ⟨start + q, hidx q hq⟩) (f r) = f r) :
    xseq (start + steps) =
      fun i =>
        matMulVec n (gje_cumulative_product n Nhat start (start + steps)) (xseq start) i +
          ch14ext_vecErrorSum f steps i := by
  induction steps with
  | zero =>
      rw [Nat.add_zero,
        gje_cumulative_product_base n Nhat (le_refl start), matMulVec_id]
      funext i
      simp [ch14ext_vecErrorSum]
  | succ steps ih =>
      have hlt : steps < steps + 1 := Nat.lt_succ_self steps
      have htop : start + steps < n := hidx steps hlt
      have hidxPrev : forall t : Nat, t < steps -> start + t < n :=
        fun t ht => hidx t (Nat.lt_trans ht hlt)
      have hrecPrev : forall t : Nat, (ht : t < steps) ->
          xseq (start + (t + 1)) =
            fun i => matMulVec n (Nhat ⟨start + t, hidxPrev t ht⟩)
              (xseq (start + t)) i + f t i := by
        intro t ht
        simpa using hrec t (Nat.lt_trans ht hlt)
      have hfuturePrev : forall r q : Nat, r < q -> (hq : q < steps) ->
          matMulVec n (Nhat ⟨start + q, hidxPrev q hq⟩) (f r) = f r := by
        intro r q hrq hq
        simpa using hfuture r q hrq (Nat.lt_trans hq hlt)
      have ih' := ih hidxPrev hrecPrev hfuturePrev
      let k : Fin n := ⟨start + steps, htop⟩
      let P := gje_cumulative_product n Nhat start (start + steps)
      have hstepIndex : start + (steps + 1) - 1 = start + steps := by omega
      have hprod : gje_cumulative_product n Nhat start (start + (steps + 1)) =
          matMul n (Nhat k) P := by
        have hstart : start < start + (steps + 1) := by omega
        have hfin : start + (steps + 1) - 1 < n := by
          rw [hstepIndex]
          exact htop
        rw [gje_cumulative_product_step n Nhat hstart hfin]
        simp [hstepIndex, k, P]
      have hfix : matMulVec n (Nhat k) (ch14ext_vecErrorSum f steps) =
          ch14ext_vecErrorSum f steps := by
        apply ch14ext_matMulVec_vecErrorSum_of_fixed (A := Nhat k) (f := f) steps
        intro r hr
        simpa [k] using hfuture r steps hr hlt
      have hlast := hrec steps hlt
      have hlast' : xseq (start + (steps + 1)) =
          fun i => matMulVec n (Nhat k) (xseq (start + steps)) i + f steps i := by
        simpa [k] using hlast
      rw [hlast', ih']
      rw [show matMulVec n (Nhat k)
          (fun a => matMulVec n P (xseq start) a + ch14ext_vecErrorSum f steps a) =
          (fun i => matMulVec n (Nhat k) (matMulVec n P (xseq start)) i +
            matMulVec n (Nhat k) (ch14ext_vecErrorSum f steps) i) by
        exact matMulVec_add_right n (Nhat k) (matMulVec n P (xseq start))
          (ch14ext_vecErrorSum f steps)]
      rw [hfix, hprod, ch14ext_vecErrorSum_succ]
      funext i
      rw [matMulVec_matMul]
      ring

/-! ## Concrete source loop specialization -/

/-- Guarded sequence of the concrete local matrix errors. In the source range
    the guard is discharged by the stage-index hypothesis. -/
noncomputable def ch14ext_gjeSourceDeltaSeq (fp : FPModel) (n : Nat)
    (V : Nat -> Fin n -> Fin n -> Real) (start : Nat) :
    Nat -> Fin n -> Fin n -> Real :=
  fun t => if h : start + t < n then
    ch14ext_gjeSourceDelta fp n (V (start + t)) ⟨start + t, h⟩
  else fun _ _ => 0

/-- Guarded sequence of the concrete local RHS errors. -/
noncomputable def ch14ext_gjeSourceFSeq (fp : FPModel) (n : Nat)
    (V : Nat -> Fin n -> Fin n -> Real) (xseq : Nat -> Fin n -> Real)
    (start : Nat) : Nat -> Fin n -> Real :=
  fun t => if h : start + t < n then
    ch14ext_gjeSourceF fp n (V (start + t)) ⟨start + t, h⟩ (xseq (start + t))
  else fun _ => 0

theorem ch14ext_gjeSourceDeltaSeq_of_lt (fp : FPModel) (n : Nat)
    (V : Nat -> Fin n -> Fin n -> Real) (start t : Nat) (ht : start + t < n) :
    ch14ext_gjeSourceDeltaSeq fp n V start t =
      ch14ext_gjeSourceDelta fp n (V (start + t)) ⟨start + t, ht⟩ := by
  unfold ch14ext_gjeSourceDeltaSeq
  rw [dif_pos ht]

theorem ch14ext_gjeSourceFSeq_of_lt (fp : FPModel) (n : Nat)
    (V : Nat -> Fin n -> Fin n -> Real) (xseq : Nat -> Fin n -> Real)
    (start t : Nat) (ht : start + t < n) :
    ch14ext_gjeSourceFSeq fp n V xseq start t =
      ch14ext_gjeSourceF fp n (V (start + t)) ⟨start + t, ht⟩ (xseq (start + t)) := by
  unfold ch14ext_gjeSourceFSeq
  rw [dif_pos ht]

/-- All iterates of the source-faithful second stage remain upper triangular. -/
theorem ch14ext_gjeSourceSeq_upper {n : Nat} (fp : FPModel)
    (V : Nat -> Fin n -> Fin n -> Real) (start steps : Nat)
    (hidx : forall t : Nat, t < steps -> start + t < n)
    (hV0 : forall i j : Fin n, j.val < i.val -> V start i j = 0)
    (hVrec : forall t : Nat, (ht : t < steps) ->
      V (start + (t + 1)) =
        ch14ext_gjeSourceStepMatrix fp n (V (start + t)) ⟨start + t, hidx t ht⟩) :
    forall t : Nat, t ≤ steps ->
      forall i j : Fin n, j.val < i.val -> V (start + t) i j = 0 := by
  intro t
  induction t with
  | zero =>
      intro _ i j hji
      simpa using hV0 i j hji
  | succ t ih =>
      intro ht i j hji
      have htstep : t < steps := by omega
      rw [hVrec t htstep]
      exact ch14ext_gjeSourceStepMatrix_upper fp (V (start + t))
        ⟨start + t, hidx t htstep⟩ (ih (by omega)) i j hji

/-- **Higham (14.27), concrete source loop before setting the final diagonal
    to the identity.** The plain sum of local errors is derived from their
    proved support; no unpropagated-sum premise is accepted. -/
theorem ch14ext_gjeSource_matrix_unpropagated_14_27 {n : Nat}
    (fp : FPModel) (V : Nat -> Fin n -> Fin n -> Real) (start steps : Nat)
    (hidx : forall t : Nat, t < steps -> start + t < n)
    (hV0 : forall i j : Fin n, j.val < i.val -> V start i j = 0)
    (hVrec : forall t : Nat, (ht : t < steps) ->
      V (start + (t + 1)) =
        ch14ext_gjeSourceStepMatrix fp n (V (start + t)) ⟨start + t, hidx t ht⟩) :
    V (start + steps) =
      fun i j =>
        matMul n (gje_cumulative_product n (ch14ext_gjeSeqStages n V)
          start (start + steps)) (V start) i j +
        ch14ext_matrixErrorSum (ch14ext_gjeSourceDeltaSeq fp n V start) steps i j := by
  have hUpper := ch14ext_gjeSourceSeq_upper fp V start steps hidx hV0 hVrec
  have hrec : forall t : Nat, (ht : t < steps) ->
      V (start + (t + 1)) =
        fun i j => matMul n
            (ch14ext_gjeSeqStages n V ⟨start + t, hidx t ht⟩)
            (V (start + t)) i j +
          ch14ext_gjeSourceDeltaSeq fp n V start t i j := by
    intro t ht
    rw [hVrec t ht]
    funext i j
    rw [ch14ext_gjeSourceDeltaSeq_of_lt fp n V start t (hidx t ht)]
    unfold ch14ext_gjeSourceDelta
    simp [ch14ext_gjeSeqStages]
  have hfuture : forall r q : Nat, r < q -> (hq : q < steps) ->
      matMul n
          (ch14ext_gjeSeqStages n V ⟨start + q, hidx q hq⟩)
          (ch14ext_gjeSourceDeltaSeq fp n V start r) =
        ch14ext_gjeSourceDeltaSeq fp n V start r := by
    intro r q hrq hq
    have hr : r < steps := Nat.lt_trans hrq hq
    rw [ch14ext_gjeSourceDeltaSeq_of_lt fp n V start r (hidx r hr)]
    simpa [ch14ext_gjeSeqStages] using
      ch14ext_gjeStageMatrix_mul_sourceDelta_of_ge fp (V (start + q))
        (V (start + r)) ⟨start + q, hidx q hq⟩ ⟨start + r, hidx r hr⟩
        (hUpper r (Nat.le_of_lt hr)) (by
          change start + r ≤ start + q
          exact Nat.add_le_add_left (Nat.le_of_lt hrq) start)
  exact ch14ext_gje_unpropagated_matrix_recurrence
    (ch14ext_gjeSeqStages n V) V (ch14ext_gjeSourceDeltaSeq fp n V start)
    start steps hidx hrec hfuture

/-- **Higham (14.28), concrete source RHS loop.** As in (14.27), every
    future-stage action on an earlier `f_k` is discharged from proved support. -/
theorem ch14ext_gjeSource_rhs_unpropagated_14_28 {n : Nat}
    (fp : FPModel) (V : Nat -> Fin n -> Fin n -> Real)
    (xseq : Nat -> Fin n -> Real) (start steps : Nat)
    (hidx : forall t : Nat, t < steps -> start + t < n)
    (hV0 : forall i j : Fin n, j.val < i.val -> V start i j = 0)
    (hVrec : forall t : Nat, (ht : t < steps) ->
      V (start + (t + 1)) =
        ch14ext_gjeSourceStepMatrix fp n (V (start + t)) ⟨start + t, hidx t ht⟩)
    (hxrec : forall t : Nat, (ht : t < steps) ->
      xseq (start + (t + 1)) =
        ch14ext_gjeSourceStepVec fp n (V (start + t)) ⟨start + t, hidx t ht⟩
          (xseq (start + t))) :
    xseq (start + steps) =
      fun i => matMulVec n
          (gje_cumulative_product n (ch14ext_gjeSeqStages n V) start (start + steps))
          (xseq start) i +
        ch14ext_vecErrorSum (ch14ext_gjeSourceFSeq fp n V xseq start) steps i := by
  have hUpper := ch14ext_gjeSourceSeq_upper fp V start steps hidx hV0 hVrec
  have hrec : forall t : Nat, (ht : t < steps) ->
      xseq (start + (t + 1)) =
        fun i => matMulVec n
            (ch14ext_gjeSeqStages n V ⟨start + t, hidx t ht⟩)
            (xseq (start + t)) i +
          ch14ext_gjeSourceFSeq fp n V xseq start t i := by
    intro t ht
    rw [hxrec t ht]
    funext i
    rw [ch14ext_gjeSourceFSeq_of_lt fp n V xseq start t (hidx t ht)]
    unfold ch14ext_gjeSourceF
    simp [ch14ext_gjeSeqStages]
  have hfuture : forall r q : Nat, r < q -> (hq : q < steps) ->
      matMulVec n
          (ch14ext_gjeSeqStages n V ⟨start + q, hidx q hq⟩)
          (ch14ext_gjeSourceFSeq fp n V xseq start r) =
        ch14ext_gjeSourceFSeq fp n V xseq start r := by
    intro r q hrq hq
    have hr : r < steps := Nat.lt_trans hrq hq
    rw [ch14ext_gjeSourceFSeq_of_lt fp n V xseq start r (hidx r hr)]
    simpa [ch14ext_gjeSeqStages] using
      ch14ext_gjeStageMatrix_mul_sourceF_of_ge fp (V (start + q))
        (V (start + r)) ⟨start + q, hidx q hq⟩ ⟨start + r, hidx r hr⟩
        (xseq (start + r)) (hUpper r (Nat.le_of_lt hr)) (by
          change start + r ≤ start + q
          exact Nat.add_le_add_left (Nat.le_of_lt hrq) start)
  exact ch14ext_gje_unpropagated_rhs_recurrence
    (ch14ext_gjeSeqStages n V) xseq (ch14ext_gjeSourceFSeq fp n V xseq start)
    start steps hidx hrec hfuture

/-- The sequence-level forms of (14.25a-b) and (14.26). Every equation,
    bound, and support clause is obtained from the concrete rounded source
    step; none appears among the hypotheses. -/
theorem ch14ext_gjeSource_sequence_local_14_25b_14_26 {n : Nat}
    (fp : FPModel) (V : Nat -> Fin n -> Fin n -> Real)
    (xseq : Nat -> Fin n -> Real) (start steps : Nat)
    (hidx : forall t : Nat, t < steps -> start + t < n)
    (hV0 : forall i j : Fin n, j.val < i.val -> V start i j = 0)
    (hVrec : forall t : Nat, (ht : t < steps) ->
      V (start + (t + 1)) =
        ch14ext_gjeSourceStepMatrix fp n (V (start + t)) ⟨start + t, hidx t ht⟩)
    (hxrec : forall t : Nat, (ht : t < steps) ->
      xseq (start + (t + 1)) =
        ch14ext_gjeSourceStepVec fp n (V (start + t)) ⟨start + t, hidx t ht⟩
          (xseq (start + t)))
    (hpiv : forall t : Nat, (ht : t < steps) ->
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0)
    (h3 : gammaValid fp 3) :
    forall t : Nat, (ht : t < steps) ->
      (forall i j : Fin n,
        V (start + (t + 1)) i j =
          matMul n (ch14ext_gjeSeqStages n V ⟨start + t, hidx t ht⟩)
            (V (start + t)) i j +
          ch14ext_gjeSourceDeltaSeq fp n V start t i j) ∧
      (forall i j : Fin n,
        |ch14ext_gjeSourceDeltaSeq fp n V start t i j| ≤
          gamma fp 3 * matMul n
            (absMatrix n (ch14ext_gjeSeqStages n V ⟨start + t, hidx t ht⟩))
            (absMatrix n (V (start + t))) i j) ∧
      (forall i j : Fin n, start + t ≤ i.val ->
        ch14ext_gjeSourceDeltaSeq fp n V start t i j = 0) ∧
      (forall i j : Fin n, j.val < start + t ->
        ch14ext_gjeSourceDeltaSeq fp n V start t i j = 0) ∧
      (forall i : Fin n,
        xseq (start + (t + 1)) i =
          matMulVec n (ch14ext_gjeSeqStages n V ⟨start + t, hidx t ht⟩)
            (xseq (start + t)) i +
          ch14ext_gjeSourceFSeq fp n V xseq start t i) ∧
      (forall i : Fin n,
        |ch14ext_gjeSourceFSeq fp n V xseq start t i| ≤
          gamma fp 3 * matMulVec n
            (absMatrix n (ch14ext_gjeSeqStages n V ⟨start + t, hidx t ht⟩))
            (absVec n (xseq (start + t))) i) ∧
      (forall i : Fin n, start + t ≤ i.val ->
        ch14ext_gjeSourceFSeq fp n V xseq start t i = 0) := by
  have hUpper := ch14ext_gjeSourceSeq_upper fp V start steps hidx hV0 hVrec
  intro t ht
  have hU := hUpper t (Nat.le_of_lt ht)
  have hM := ch14ext_gjeSource_local_matrix_14_25 fp (V (start + t))
    ⟨start + t, hidx t ht⟩ hU (hpiv t ht) h3
  have hF := ch14ext_gjeSource_local_rhs_14_26 fp (V (start + t))
    ⟨start + t, hidx t ht⟩ (xseq (start + t)) hU (hpiv t ht) h3
  have hDelta := ch14ext_gjeSourceDeltaSeq_of_lt fp n V start t (hidx t ht)
  have hLocalF := ch14ext_gjeSourceFSeq_of_lt fp n V xseq start t (hidx t ht)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [hVrec t ht, hDelta]
    simpa [ch14ext_gjeSeqStages] using hM.1 i j
  · intro i j
    rw [hDelta]
    simpa [ch14ext_gjeSeqStages] using hM.2.1 i j
  · intro i j hki
    rw [hDelta]
    exact hM.2.2.1 i j hki
  · intro i j hjk
    rw [hDelta]
    exact hM.2.2.2 i j hjk
  · intro i
    rw [hxrec t ht, hLocalF]
    simpa [ch14ext_gjeSeqStages] using hF.1 i
  · intro i
    rw [hLocalF]
    simpa [ch14ext_gjeSeqStages] using hF.2.1 i
  · intro i hki
    rw [hLocalF]
    exact hF.2.2 i hki

/-- **Higham (14.27)-(14.28), literal source indices `k = 2,...,n`.**

    With `V 1 = U_2 = U`, `V n = I`, and zero-based `Fin` index `1+t`
    representing Higham's stage `k = 2+t`, the two displayed equations have
    the exact unpropagated sums printed in the book. -/
theorem ch14ext_gjeSource_literal_14_27_14_28 {n : Nat}
    (fp : FPModel) (V : Nat -> Fin n -> Fin n -> Real)
    (xseq : Nat -> Fin n -> Real) (hnpos : 1 ≤ n)
    (hV0 : forall i j : Fin n, j.val < i.val -> V 1 i j = 0)
    (hVrec : forall t : Nat, (ht : t < n - 1) ->
      V (1 + (t + 1)) =
        ch14ext_gjeSourceStepMatrix fp n (V (1 + t))
          ⟨1 + t, by omega⟩)
    (hxrec : forall t : Nat, (ht : t < n - 1) ->
      xseq (1 + (t + 1)) =
        ch14ext_gjeSourceStepVec fp n (V (1 + t))
          ⟨1 + t, by omega⟩ (xseq (1 + t)))
    (hVfinal : V n = idMatrix n) :
    idMatrix n =
        (fun i j =>
          matMul n (gje_cumulative_product n (ch14ext_gjeSeqStages n V) 1 n)
            (V 1) i j +
          ch14ext_matrixErrorSum (ch14ext_gjeSourceDeltaSeq fp n V 1) (n - 1) i j) ∧
      xseq n =
        (fun i =>
          matMulVec n (gje_cumulative_product n (ch14ext_gjeSeqStages n V) 1 n)
            (xseq 1) i +
          ch14ext_vecErrorSum (ch14ext_gjeSourceFSeq fp n V xseq 1) (n - 1) i) := by
  have hidx : forall t : Nat, t < n - 1 -> 1 + t < n := by omega
  have hVrec' : forall t : Nat, (ht : t < n - 1) ->
      V (1 + (t + 1)) =
        ch14ext_gjeSourceStepMatrix fp n (V (1 + t)) ⟨1 + t, hidx t ht⟩ := by
    intro t ht
    simpa using hVrec t ht
  have hxrec' : forall t : Nat, (ht : t < n - 1) ->
      xseq (1 + (t + 1)) =
        ch14ext_gjeSourceStepVec fp n (V (1 + t)) ⟨1 + t, hidx t ht⟩
          (xseq (1 + t)) := by
    intro t ht
    simpa using hxrec t ht
  have hM := ch14ext_gjeSource_matrix_unpropagated_14_27 fp V 1 (n - 1)
    hidx hV0 hVrec'
  have hX := ch14ext_gjeSource_rhs_unpropagated_14_28 fp V xseq 1 (n - 1)
    hidx hV0 hVrec' hxrec'
  have hsum : 1 + (n - 1) = n := by omega
  constructor
  · rw [hsum, hVfinal] at hM
    simpa [hsum] using hM
  · rw [hsum] at hX
    simpa [hsum] using hX

/-! ## Recursively executed source trace -/

/-- One coupled matrix/RHS step of the source-faithful second stage. -/
noncomputable def ch14ext_gjeSourceStepState {n : Nat} (fp : FPModel)
    (s : Ch14GJEState n) (k : Fin n) : Ch14GJEState n where
  matrix := ch14ext_gjeSourceStepMatrix fp n s.matrix k
  rhs := ch14ext_gjeSourceStepVec fp n s.matrix k s.rhs

/-- The actual recursively executed second-stage trace. The natural argument
    is the number of completed stages; `start+t` is the matrix stage index. -/
noncomputable def ch14ext_gjeSourceTrace {n : Nat} (fp : FPModel) (start : Nat)
    (s : Ch14GJEState n) : Nat -> Ch14GJEState n
  | 0 => s
  | t + 1 => if h : start + t < n then
      ch14ext_gjeSourceStepState fp (ch14ext_gjeSourceTrace fp start s t)
        ⟨start + t, h⟩
    else ch14ext_gjeSourceTrace fp start s t

/-- Absolute-indexed matrix view of the recursively executed trace. -/
noncomputable def ch14ext_gjeSourceTraceMatrix {n : Nat} (fp : FPModel)
    (start : Nat) (s : Ch14GJEState n) (q : Nat) : Fin n -> Fin n -> Real :=
  (ch14ext_gjeSourceTrace fp start s (q - start)).matrix

/-- Absolute-indexed RHS view of the recursively executed trace. -/
noncomputable def ch14ext_gjeSourceTraceRhs {n : Nat} (fp : FPModel)
    (start : Nat) (s : Ch14GJEState n) (q : Nat) : Fin n -> Real :=
  (ch14ext_gjeSourceTrace fp start s (q - start)).rhs

theorem ch14ext_gjeSourceTraceMatrix_rec {n : Nat} (fp : FPModel)
    (start : Nat) (s : Ch14GJEState n) (t : Nat) (ht : start + t < n) :
    ch14ext_gjeSourceTraceMatrix fp start s (start + (t + 1)) =
      ch14ext_gjeSourceStepMatrix fp n
        (ch14ext_gjeSourceTraceMatrix fp start s (start + t)) ⟨start + t, ht⟩ := by
  simp [ch14ext_gjeSourceTraceMatrix, ch14ext_gjeSourceTrace,
    ch14ext_gjeSourceStepState, ht]

theorem ch14ext_gjeSourceTraceRhs_rec {n : Nat} (fp : FPModel)
    (start : Nat) (s : Ch14GJEState n) (t : Nat) (ht : start + t < n) :
    ch14ext_gjeSourceTraceRhs fp start s (start + (t + 1)) =
      ch14ext_gjeSourceStepVec fp n
        (ch14ext_gjeSourceTraceMatrix fp start s (start + t)) ⟨start + t, ht⟩
        (ch14ext_gjeSourceTraceRhs fp start s (start + t)) := by
  simp [ch14ext_gjeSourceTraceRhs, ch14ext_gjeSourceTraceMatrix,
    ch14ext_gjeSourceTrace, ch14ext_gjeSourceStepState, ht]

/-- Fully executed form of (14.27)-(14.28). Unlike the sequence adapter above,
    this theorem has no matrix or RHS recurrence hypothesis: both traces are
    projections of `ch14ext_gjeSourceTrace`, and their recurrences are reduced
    by definition before applying the support-driven sum theorem. -/
theorem ch14ext_gjeSourceTrace_literal_14_27_14_28 {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) (hnpos : 1 ≤ n)
    (hUpper : forall i j : Fin n, j.val < i.val -> s.matrix i j = 0)
    (hfinal : (ch14ext_gjeSourceTrace fp 1 s (n - 1)).matrix = idMatrix n) :
    let V := ch14ext_gjeSourceTraceMatrix fp 1 s
    let xseq := ch14ext_gjeSourceTraceRhs fp 1 s
    idMatrix n =
        (fun i j =>
          matMul n (gje_cumulative_product n (ch14ext_gjeSeqStages n V) 1 n)
            (V 1) i j +
          ch14ext_matrixErrorSum (ch14ext_gjeSourceDeltaSeq fp n V 1) (n - 1) i j) ∧
      xseq n =
        (fun i =>
          matMulVec n (gje_cumulative_product n (ch14ext_gjeSeqStages n V) 1 n)
            (xseq 1) i +
          ch14ext_vecErrorSum (ch14ext_gjeSourceFSeq fp n V xseq 1) (n - 1) i) := by
  let V := ch14ext_gjeSourceTraceMatrix fp 1 s
  let xseq := ch14ext_gjeSourceTraceRhs fp 1 s
  have hidx : forall t : Nat, t < n - 1 -> 1 + t < n := by omega
  have hV0 : forall i j : Fin n, j.val < i.val -> V 1 i j = 0 := by
    intro i j hji
    simpa [V, ch14ext_gjeSourceTraceMatrix] using hUpper i j hji
  have hVrec : forall t : Nat, (ht : t < n - 1) ->
      V (1 + (t + 1)) =
        ch14ext_gjeSourceStepMatrix fp n (V (1 + t)) ⟨1 + t, hidx t ht⟩ := by
    intro t ht
    exact ch14ext_gjeSourceTraceMatrix_rec fp 1 s t (hidx t ht)
  have hxrec : forall t : Nat, (ht : t < n - 1) ->
      xseq (1 + (t + 1)) =
        ch14ext_gjeSourceStepVec fp n (V (1 + t)) ⟨1 + t, hidx t ht⟩
          (xseq (1 + t)) := by
    intro t ht
    exact ch14ext_gjeSourceTraceRhs_rec fp 1 s t (hidx t ht)
  have hVfinal : V n = idMatrix n := by
    have hsum : n - 1 = n - 1 := rfl
    simpa [V, ch14ext_gjeSourceTraceMatrix, hsum] using hfinal
  exact ch14ext_gjeSource_literal_14_27_14_28 fp V xseq hnpos hV0 hVrec hxrec hVfinal

end NumStability.Ch14Ext
