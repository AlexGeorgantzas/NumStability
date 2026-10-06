-- Algorithms/QR/GivensQR.lean
--
-- Backward error analysis for Givens QR factorization (Higham §18.5).
--
-- Lemma 18.8: A sequence of r Givens rotations with per-step error ≤ c
--   yields Â_{r+1} = Qᵀ(A + ΔA) with ‖ΔA‖_F ≤ r·c·‖A‖_F.
--
-- Theorem 18.9: Givens QR gives A + ΔA = Q·R̂ with ‖ΔA‖_F bounded.
--   For an n×n matrix, r = n(n-1)/2 Givens rotations are used.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.QR.GivensSpec
import NumStability.Algorithms.QR.GivensMatrixStep
import NumStability.Algorithms.QR.HouseholderQR

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-- A below-diagonal Givens QR annihilation task.  The pivot row is the task
    column, embedded into the row index using `below`. -/
structure GivensQRTask (m cols : Nat) where
  row : Fin m
  col : Fin cols
  below : col.val < row.val

/-- Pivot row for a below-diagonal Givens QR task. -/
def GivensQRTask.pivot {m cols : Nat} (t : GivensQRTask m cols) : Fin m :=
  ⟨t.col.val, lt_trans t.below t.row.isLt⟩

@[simp] theorem GivensQRTask.pivot_val {m cols : Nat}
    (t : GivensQRTask m cols) :
    t.pivot.val = t.col.val :=
  rfl

theorem GivensQRTask.pivot_ne_row {m cols : Nat}
    (t : GivensQRTask m cols) :
    Not (t.pivot = t.row) := by
  intro h
  exact Nat.ne_of_lt t.below (congrArg Fin.val h)

/-- Anti-diagonal stage index for a Givens QR task. -/
def GivensQRTask.stage {m cols : Nat} (t : GivensQRTask m cols) : Nat :=
  t.row.val + t.col.val - 1

/-- The stage index is one less than the row-plus-column anti-diagonal. -/
theorem GivensQRTask.stage_succ_eq {m cols : Nat}
    (t : GivensQRTask m cols) :
    t.stage + 1 = t.row.val + t.col.val := by
  dsimp [GivensQRTask.stage]
  have hpos : 0 < t.row.val + t.col.val := by
    have hbelow : t.col.val < t.row.val := t.below
    omega
  omega

/-- Two task records are equal when their row and column fields agree. -/
theorem GivensQRTask.ext_row_col {m cols : Nat} {t u : GivensQRTask m cols}
    (hrow : t.row = u.row) (hcol : t.col = u.col) :
    t = u := by
  cases t with
  | mk row col below =>
    cases u with
    | mk row' col' below' =>
      cases hrow
      cases hcol
      simp

/-- There are finitely many QR annihilation tasks, since a task is determined by
    its target row and column. -/
instance GivensQRTask.instFinite (m cols : Nat) :
    Finite (GivensQRTask m cols) := by
  exact Finite.of_injective
    (fun t : GivensQRTask m cols => (t.row, t.col))
    (by
      intro t u h
      exact GivensQRTask.ext_row_col
        (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- Noncomputable finite-type instance used only to enumerate concrete stage
    task lists. -/
noncomputable instance GivensQRTask.instFintype (m cols : Nat) :
    Fintype (GivensQRTask m cols) :=
  Fintype.ofFinite (GivensQRTask m cols)

/-- Same-stage QR tasks with the same pivot row are the same task. -/
theorem GivensQRTask.same_stage_eq_of_pivot_eq {m cols : Nat}
    {t u : GivensQRTask m cols}
    (hstage : t.stage = u.stage) (hpivot : t.pivot = u.pivot) :
    t = u := by
  have hcol_val : t.col.val = u.col.val := by
    simpa [GivensQRTask.pivot] using congrArg Fin.val hpivot
  have hcol : t.col = u.col := Fin.ext hcol_val
  have hrow_val : t.row.val = u.row.val := by
    have ht := GivensQRTask.stage_succ_eq t
    have hu := GivensQRTask.stage_succ_eq u
    omega
  exact GivensQRTask.ext_row_col (Fin.ext hrow_val) hcol

/-- Same-stage QR tasks with the same target row are the same task. -/
theorem GivensQRTask.same_stage_eq_of_row_eq {m cols : Nat}
    {t u : GivensQRTask m cols}
    (hstage : t.stage = u.stage) (hrow : t.row = u.row) :
    t = u := by
  have hrow_val : t.row.val = u.row.val := congrArg Fin.val hrow
  have hcol_val : t.col.val = u.col.val := by
    have ht := GivensQRTask.stage_succ_eq t
    have hu := GivensQRTask.stage_succ_eq u
    omega
  exact GivensQRTask.ext_row_col hrow (Fin.ext hcol_val)

/-- In one anti-diagonal stage, one task's pivot row cannot be another task's
    target row. -/
theorem GivensQRTask.same_stage_pivot_ne_row {m cols : Nat}
    {t u : GivensQRTask m cols}
    (hstage : t.stage = u.stage) :
    t.pivot ≠ u.row := by
  intro hrow
  have hpivot_row_val : t.col.val = u.row.val := by
    simpa [GivensQRTask.pivot] using congrArg Fin.val hrow
  have ht := GivensQRTask.stage_succ_eq t
  have hu := GivensQRTask.stage_succ_eq u
  have htbelow : t.col.val < t.row.val := t.below
  have hubelow : u.col.val < u.row.val := u.below
  omega

/-- Distinct tasks in the same anti-diagonal stage touch disjoint row pairs. -/
theorem GivensQRTask.same_stage_rowPair_disjoint {m cols : Nat}
    {t u : GivensQRTask m cols}
    (hstage : t.stage = u.stage) (hne : t ≠ u) :
    t.pivot ≠ u.pivot ∧ t.pivot ≠ u.row ∧
      t.row ≠ u.pivot ∧ t.row ≠ u.row := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hpivot
    exact hne (GivensQRTask.same_stage_eq_of_pivot_eq hstage hpivot)
  · exact GivensQRTask.same_stage_pivot_ne_row hstage
  · intro hrow
    exact (GivensQRTask.same_stage_pivot_ne_row
      (t := u) (u := t) hstage.symm) hrow.symm
  · intro hrow
    exact hne (GivensQRTask.same_stage_eq_of_row_eq hstage hrow)

/-- Number of anti-diagonal stages in the standard tall rectangular Givens QR
    schedule.  This is the source-stage count behind the `m+n-2` coefficient in
    Higham Theorem 19.10. -/
def givensQRStageCount (m cols : Nat) : Nat :=
  m + cols - 2

/-- Every below-diagonal QR task lies in the anti-diagonal stage range. -/
theorem GivensQRTask.stage_lt_stageCount {m cols : Nat}
    (t : GivensQRTask m cols) :
    t.stage < givensQRStageCount m cols := by
  have hstage := GivensQRTask.stage_succ_eq t
  have hrow : t.row.val < m := t.row.isLt
  have hcol : t.col.val < cols := t.col.isLt
  have hbelow : t.col.val < t.row.val := t.below
  dsimp [givensQRStageCount]
  omega

/-- Concrete finite list of all tasks in one anti-diagonal stage. -/
noncomputable def givensQRStageTasks (m cols s : Nat) :
    List (GivensQRTask m cols) := by
  classical
  exact ((Finset.univ : Finset (GivensQRTask m cols)).filter
    (fun t => t.stage = s)).toList

theorem mem_givensQRStageTasks_iff {m cols s : Nat}
    (t : GivensQRTask m cols) :
    t ∈ givensQRStageTasks m cols s ↔ t.stage = s := by
  classical
  simp [givensQRStageTasks]

theorem givensQRStageTasks_stage {m cols s : Nat} :
    forall t : GivensQRTask m cols,
      t ∈ givensQRStageTasks m cols s -> t.stage = s := by
  intro t ht
  exact (mem_givensQRStageTasks_iff t).mp ht

theorem givensQRStageTasks_complete {m cols s : Nat} :
    forall t : GivensQRTask m cols,
      t.stage = s -> t ∈ givensQRStageTasks m cols s := by
  intro t ht
  exact (mem_givensQRStageTasks_iff t).mpr ht

theorem givensQRStageTasks_nodup (m cols s : Nat) :
    (givensQRStageTasks m cols s).Nodup := by
  classical
  exact Finset.nodup_toList _

/-- A matrix has all below-diagonal entries whose anti-diagonal index is at most
    `s` already zeroed. -/
def ZeroedThrough {m cols : Nat} (s : Nat)
    (B : Fin m -> Fin cols -> Real) : Prop :=
  forall i j, j.val < i.val -> i.val + j.val <= s -> B i j = 0

/-- All below-diagonal targets in a given anti-diagonal stage are zero. -/
def StageTargetsZero {m cols : Nat} (s : Nat)
    (B : Fin m -> Fin cols -> Real) : Prop :=
  forall t : GivensQRTask m cols, t.stage = s -> B t.row t.col = 0

/-- If the previous frontier holds and all targets in the next anti-diagonal
    are zero, the `ZeroedThrough` frontier advances by one stage. -/
theorem ZeroedThrough.succ_of_stageTargetsZero {m cols : Nat}
    {s : Nat} {B : Fin m -> Fin cols -> Real}
    (hzero : ZeroedThrough s B) (htargets : StageTargetsZero s B) :
    ZeroedThrough (s + 1) B := by
  intro i j hbelow hsum
  by_cases hold : i.val + j.val <= s
  · exact hzero i j hbelow hold
  · let t : GivensQRTask m cols := ⟨i, j, hbelow⟩
    have hsum_eq : i.val + j.val = s + 1 := by omega
    have hstage_succ : t.stage + 1 = s + 1 := by
      rw [GivensQRTask.stage_succ_eq t]
      exact hsum_eq
    have hstage : t.stage = s := by
      omega
    exact htargets t hstage

/-- A `ZeroedThrough` invariant at a task's stage gives the previous-column
    zero hypothesis required by one QR task step.  The task itself targets the
    next anti-diagonal. -/
theorem ZeroedThrough.prev_pair_zero_of_task {m cols : Nat}
    {B : Fin m -> Fin cols -> Real} (t : GivensQRTask m cols)
    (hzero : ZeroedThrough t.stage B) :
    forall j : Fin cols, j.val < t.col.val ->
      B t.pivot j = 0 /\ B t.row j = 0 := by
  intro j hj
  have hstage := GivensQRTask.stage_succ_eq t
  have hbelow : t.col.val < t.row.val := t.below
  constructor
  · exact hzero t.pivot j (by
      simpa [GivensQRTask.pivot] using hj) (by
      dsimp [GivensQRTask.pivot]
      omega)
  · exact hzero t.row j (by omega) (by omega)

/-- Zero-aware QR task step for one Givens annihilation.

If the target entry is already zero, the step is the identity.  Otherwise it
uses the existing rounded Givens matrix application, preserves earlier columns,
and stores the target entry as exactly zero. -/
noncomputable def fl_givensQRTaskStep (fp : FPModel) (m cols : Nat)
    (p q : Fin m) (col : Fin cols)
    (B : Fin m -> Fin cols -> Real) : Fin m -> Fin cols -> Real :=
  if B q col = 0 then
    B
  else
    let C := fl_givensApplyMatrixRect fp m cols p q (B p col) (B q col) B
    fun i j =>
      if j.val < col.val then
        B i j
      else if i = q then
        if j = col then 0 else C i j
      else
        C i j

/-- Task-indexed version of `fl_givensQRTaskStep`. -/
noncomputable def fl_givensQRTaskStepOfTask (fp : FPModel) (m cols : Nat)
    (t : GivensQRTask m cols)
    (B : Fin m -> Fin cols -> Real) : Fin m -> Fin cols -> Real :=
  fl_givensQRTaskStep fp m cols t.pivot t.row t.col B

@[simp] theorem fl_givensQRTaskStep_zero (fp : FPModel) (m cols : Nat)
    (p q : Fin m) (col : Fin cols) (B : Fin m -> Fin cols -> Real)
    (hzero : B q col = 0) :
    fl_givensQRTaskStep fp m cols p q col B = B := by
  simp [fl_givensQRTaskStep, hzero]

theorem fl_givensQRTaskStep_prev_col (fp : FPModel) (m cols : Nat)
    (p q : Fin m) (col j : Fin cols) (B : Fin m -> Fin cols -> Real)
    (i : Fin m) (hj : j.val < col.val) :
    fl_givensQRTaskStep fp m cols p q col B i j = B i j := by
  by_cases hzero : B q col = 0
  · simp [fl_givensQRTaskStep, hzero]
  · unfold fl_givensQRTaskStep
    rw [if_neg hzero]
    rw [if_pos hj]

@[simp] theorem fl_givensQRTaskStep_target (fp : FPModel) (m cols : Nat)
    (p q : Fin m) (col : Fin cols) (B : Fin m -> Fin cols -> Real) :
    fl_givensQRTaskStep fp m cols p q col B q col = 0 := by
  by_cases hzero : B q col = 0
  · simp [fl_givensQRTaskStep, hzero]
  · simp [fl_givensQRTaskStep, hzero]

theorem fl_givensQRTaskStep_active_ne_target (fp : FPModel) (m cols : Nat)
    (p q : Fin m) (col j : Fin cols) (B : Fin m -> Fin cols -> Real)
    (i : Fin m) (hactive : Not (B q col = 0))
    (hj : Not (j.val < col.val))
    (hnot : Not (i = q) \/ Not (j = col)) :
    fl_givensQRTaskStep fp m cols p q col B i j =
      fl_givensApplyMatrixRect fp m cols p q (B p col) (B q col) B i j := by
  unfold fl_givensQRTaskStep
  rw [if_neg hactive]
  rw [if_neg hj]
  by_cases hi : i = q
  · rw [if_pos hi]
    have hjne : Not (j = col) := by
      cases hnot with
      | inl hine =>
          exact False.elim (hine hi)
      | inr hjne =>
          exact hjne
    rw [if_neg hjne]
  · rw [if_neg hi]

/-- On a previous column whose touched entries are already zero, the
    zero-aware QR task step agrees with the exact Givens rotation. -/
theorem fl_givensQRTaskStep_prev_col_exact_rotation (fp : FPModel)
    (m cols : Nat) (p q : Fin m) (col j : Fin cols)
    (B : Fin m -> Fin cols -> Real) (i : Fin m)
    (hpq : p ≠ q) (hj : j.val < col.val)
    (hbp : B p j = 0) (hbq : B q j = 0) :
    fl_givensQRTaskStep fp m cols p q col B i j =
      matMulRect m m cols
        (givensRotation m p q (givensC (B p col) (B q col))
          (givensS (B p col) (B q col))) B i j := by
  rw [fl_givensQRTaskStep_prev_col fp m cols p q col j B i hj]
  rw [givensRotation_matMulRect_pair_zero_col m cols p q
    (givensC (B p col) (B q col))
    (givensS (B p col) (B q col)) B j hpq hbp hbq i]

/-- The zero-aware QR task step's stored target zero agrees with the exact
    constructed Givens rotation for that target. -/
theorem fl_givensQRTaskStep_target_exact_rotation (fp : FPModel)
    (m cols : Nat) (p q : Fin m) (col : Fin cols)
    (B : Fin m -> Fin cols -> Real) (hpq : p ≠ q) :
    fl_givensQRTaskStep fp m cols p q col B q col =
      matMulRect m m cols
        (givensRotation m p q (givensC (B p col) (B q col))
          (givensS (B p col) (B q col))) B q col := by
  rw [fl_givensQRTaskStep_target]
  rw [givensRotation_constructed_matMulRect_target_zero m cols p q col B hpq]

/-- Nonzero branch residual for one zero-aware QR task step, assuming previous
    columns are already zero in the active row pair.

    This is the local sparse bridge needed before the anti-diagonal schedule:
    it combines the sparse panel residual with the exact facts that previous
    columns and the target entry are unchanged by the source exact rotation. -/
theorem fl_givensQRTaskStep_sparse_residual_of_prev_pair_zero
    (fp : FPModel) (m cols : Nat) (p q : Fin m) (col : Fin cols)
    (B : Fin m -> Fin cols -> Real)
    (hpq : p ≠ q) (hactive : Not (B q col = 0))
    (hprev : forall j : Fin cols, j.val < col.val ->
      B p j = 0 /\ B q j = 0)
    (hvalid : gammaValid fp 8) :
    exists E : Fin m -> Fin cols -> Real,
      (forall i j,
        fl_givensQRTaskStep fp m cols p q col B i j =
          matMulRect m m cols
            (givensRotation m p q (givensC (B p col) (B q col))
              (givensS (B p col) (B q col))) B i j + E i j) /\
      frobNorm E <=
        (gamma fp 8 *
          frobNorm (givensRotation m p q
            (givensC (B p col) (B q col))
            (givensS (B p col) (B q col)))) * frobNorm B /\
      forall i j, i ≠ p -> i ≠ q -> E i j = 0 := by
  have hnz : (B p col) ^ 2 + (B q col) ^ 2 ≠ 0 := by
    intro hsum
    have hq_sq_zero : (B q col) ^ 2 = 0 := by
      apply le_antisymm
      · calc
          (B q col) ^ 2 <= (B p col) ^ 2 + (B q col) ^ 2 := by
            exact le_add_of_nonneg_left (sq_nonneg (B p col))
          _ = 0 := hsum
      · exact sq_nonneg (B q col)
    exact hactive (sq_eq_zero_iff.mp hq_sq_zero)
  let G := givensRotation m p q (givensC (B p col) (B q col))
    (givensS (B p col) (B q col))
  let c :=
    gamma fp 8 * frobNorm G
  have hraw :
      SparseColumnwiseGivensStepErrorRect m cols p q G B
        (fl_givensApplyMatrixRect fp m cols p q (B p col) (B q col) B) c := by
    simpa [G, c] using
      fl_givensApply_computed_matrix_sparse_step_error_rect fp m cols
        p q (B p col) (B q col) B hpq hnz hvalid
  have hc : 0 <= c := by
    exact mul_nonneg (gamma_nonneg fp hvalid) (frobNorm_nonneg G)
  obtain ⟨Eraw, hEraw, hEraw_bound, hEraw_rows⟩ :=
    hraw.exists_residual_matrix_bound_row_support hc
  let E : Fin m -> Fin cols -> Real := fun i j =>
    if j.val < col.val then
      0
    else if i = q /\ j = col then
      0
    else
      Eraw i j
  refine ⟨E, ?_, ?_, ?_⟩
  · intro i j
    by_cases hjprev : j.val < col.val
    · have hpair := hprev j hjprev
      rw [fl_givensQRTaskStep_prev_col fp m cols p q col j B i hjprev]
      have hrot :=
        givensRotation_matMulRect_pair_zero_col m cols p q
          (givensC (B p col) (B q col))
          (givensS (B p col) (B q col)) B j hpq hpair.1 hpair.2 i
      rw [hrot]
      dsimp [E]
      rw [if_pos hjprev]
      ring
    · by_cases htarget : i = q /\ j = col
      · rcases htarget with ⟨hiq, hjcol⟩
        subst i
        subst j
        rw [fl_givensQRTaskStep_target]
        have hrot :=
          givensRotation_constructed_matMulRect_target_zero m cols p q col B hpq
        rw [hrot]
        dsimp [E]
        rw [if_neg (Nat.lt_irrefl col.val)]
        rw [if_pos ⟨rfl, rfl⟩]
        ring
      · have hnot : Not (i = q) \/ Not (j = col) := by
          by_cases hiq : i = q
          · right
            intro hjcol
            exact htarget ⟨hiq, hjcol⟩
          · left
            exact hiq
        rw [fl_givensQRTaskStep_active_ne_target fp m cols p q col j B
          i hactive hjprev hnot]
        have hraw_ij := hEraw i j
        rw [hraw_ij]
        dsimp [E]
        rw [if_neg hjprev]
        rw [if_neg htarget]
  · have hE_le_raw : frobNorm E <= (1 : Real) * frobNorm Eraw := by
      apply frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
      · norm_num
      · intro i j
        by_cases hjprev : j.val < col.val
        · dsimp [E]
          rw [if_pos hjprev]
          simp
        · by_cases htarget : i = q /\ j = col
          · dsimp [E]
            rw [if_neg hjprev]
            rw [if_pos htarget]
            simp
          · dsimp [E]
            rw [if_neg hjprev]
            rw [if_neg htarget]
            simp
    calc
      frobNorm E <= frobNorm Eraw := by simpa using hE_le_raw
      _ <= c * frobNorm B := hEraw_bound
      _ =
          (gamma fp 8 *
            frobNorm (givensRotation m p q
              (givensC (B p col) (B q col))
              (givensS (B p col) (B q col)))) * frobNorm B := by
            rfl
  · intro i j hip hiq
    by_cases hjprev : j.val < col.val
    · dsimp [E]
      rw [if_pos hjprev]
    · by_cases htarget : i = q /\ j = col
      · dsimp [E]
        rw [if_neg hjprev]
        rw [if_pos htarget]
      · dsimp [E]
        rw [if_neg hjprev]
        rw [if_neg htarget]
        exact hEraw_rows i j hip hiq

/-- Columnwise residual form of the nonzero branch for one zero-aware QR task
    step, assuming previous columns are already zero in the active row pair. -/
theorem fl_givensQRTaskStep_columnFrob_residual_of_prev_pair_zero
    (fp : FPModel) (m cols : Nat) (p q : Fin m) (col : Fin cols)
    (B : Fin m -> Fin cols -> Real)
    (hpq : p ≠ q) (hactive : Not (B q col = 0))
    (hprev : forall j : Fin cols, j.val < col.val ->
      B p j = 0 /\ B q j = 0)
    (hvalid : gammaValid fp 8) :
    exists E : Fin m -> Fin cols -> Real,
      (forall i j,
        fl_givensQRTaskStep fp m cols p q col B i j =
          matMulRect m m cols
            (givensRotation m p q (givensC (B p col) (B q col))
              (givensS (B p col) (B q col))) B i j + E i j) /\
      (forall j,
        columnFrob E j <=
          (gamma fp 8 *
            frobNorm (givensRotation m p q
              (givensC (B p col) (B q col))
              (givensS (B p col) (B q col)))) * columnFrob B j) /\
      forall i j, i ≠ p -> i ≠ q -> E i j = 0 := by
  have hnz : (B p col) ^ 2 + (B q col) ^ 2 ≠ 0 := by
    intro hsum
    have hq_sq_zero : (B q col) ^ 2 = 0 := by
      apply le_antisymm
      · calc
          (B q col) ^ 2 <= (B p col) ^ 2 + (B q col) ^ 2 := by
            exact le_add_of_nonneg_left (sq_nonneg (B p col))
          _ = 0 := hsum
      · exact sq_nonneg (B q col)
    exact hactive (sq_eq_zero_iff.mp hq_sq_zero)
  let G := givensRotation m p q (givensC (B p col) (B q col))
    (givensS (B p col) (B q col))
  let c := gamma fp 8 * frobNorm G
  have hraw :
      SparseColumnwiseGivensStepErrorRect m cols p q G B
        (fl_givensApplyMatrixRect fp m cols p q (B p col) (B q col) B) c := by
    simpa [G, c] using
      fl_givensApply_computed_matrix_sparse_step_error_rect fp m cols
        p q (B p col) (B q col) B hpq hnz hvalid
  have hc : 0 <= c := by
    exact mul_nonneg (gamma_nonneg fp hvalid) (frobNorm_nonneg G)
  obtain ⟨Eraw, hEraw, _hEraw_bound, hEraw_col⟩ :=
    hraw.exists_residual_matrix_bound hc
  let E : Fin m -> Fin cols -> Real := fun i j =>
    if j.val < col.val then
      0
    else if i = q /\ j = col then
      0
    else
      Eraw i j
  refine ⟨E, ?_, ?_, ?_⟩
  · intro i j
    by_cases hjprev : j.val < col.val
    · have hpair := hprev j hjprev
      rw [fl_givensQRTaskStep_prev_col fp m cols p q col j B i hjprev]
      have hrot :=
        givensRotation_matMulRect_pair_zero_col m cols p q
          (givensC (B p col) (B q col))
          (givensS (B p col) (B q col)) B j hpq hpair.1 hpair.2 i
      rw [hrot]
      dsimp [E]
      rw [if_pos hjprev]
      ring
    · by_cases htarget : i = q /\ j = col
      · rcases htarget with ⟨hiq, hjcol⟩
        subst i
        subst j
        rw [fl_givensQRTaskStep_target]
        have hrot :=
          givensRotation_constructed_matMulRect_target_zero m cols p q col B hpq
        rw [hrot]
        dsimp [E]
        rw [if_neg (Nat.lt_irrefl col.val)]
        rw [if_pos ⟨rfl, rfl⟩]
        ring
      · have hnot : Not (i = q) \/ Not (j = col) := by
          by_cases hiq : i = q
          · right
            intro hjcol
            exact htarget ⟨hiq, hjcol⟩
          · left
            exact hiq
        rw [fl_givensQRTaskStep_active_ne_target fp m cols p q col j B
          i hactive hjprev hnot]
        have hraw_ij := hEraw i j
        rw [hraw_ij]
        dsimp [E]
        rw [if_neg hjprev]
        rw [if_neg htarget]
  · intro j
    have hE_le_raw_col :
        columnFrob E j <= columnFrob Eraw j := by
      unfold columnFrob
      have hle :
          frobNorm (fun i (_ : Fin 1) => E i j) <=
            (1 : Real) * frobNorm (fun i (_ : Fin 1) => Eraw i j) := by
        apply frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
        · norm_num
        · intro i u
          cases u
          by_cases hjprev : j.val < col.val
          · dsimp [E]
            rw [if_pos hjprev]
            simp
          · by_cases htarget : i = q /\ j = col
            · dsimp [E]
              rw [if_neg hjprev]
              rw [if_pos htarget]
              simp
            · dsimp [E]
              rw [if_neg hjprev]
              rw [if_neg htarget]
              simp
      simpa using hle
    obtain ⟨ΔGj, hΔGj, _hsupp, hΔcol⟩ := hEraw_col j
    calc
      columnFrob E j <= columnFrob Eraw j := hE_le_raw_col
      _ <= frobNorm ΔGj * columnFrob B j :=
          columnFrob_matMulVec_le_frobNorm_mul_columnFrob Eraw B ΔGj j hΔcol
      _ <= c * columnFrob B j :=
          mul_le_mul_of_nonneg_right hΔGj (columnFrob_nonneg B j)
      _ =
          (gamma fp 8 *
            frobNorm (givensRotation m p q
              (givensC (B p col) (B q col))
              (givensS (B p col) (B q col)))) * columnFrob B j := by
            rfl
  · intro i j hip hiq
    by_cases hjprev : j.val < col.val
    · dsimp [E]
      rw [if_pos hjprev]
    · by_cases htarget : i = q /\ j = col
      · dsimp [E]
        rw [if_neg hjprev]
        rw [if_pos htarget]
      · dsimp [E]
        rw [if_neg hjprev]
        rw [if_neg htarget]
        obtain ⟨ΔGj, _hΔGj, hsupp, hΔcol⟩ := hEraw_col j
        rw [hΔcol i]
        have hrow : forall k : Fin m, ΔGj i k = 0 :=
          hsupp.row_zero hip hiq
        unfold matMulVec
        simp [hrow]

/-- Task-indexed sparse residual theorem using the `ZeroedThrough` invariant
    that holds at the task's anti-diagonal stage. -/
theorem fl_givensQRTaskStepOfTask_sparse_residual_of_zeroedThrough
    (fp : FPModel) (m cols : Nat) (t : GivensQRTask m cols)
    (B : Fin m -> Fin cols -> Real)
    (hzero : ZeroedThrough t.stage B)
    (hactive : Not (B t.row t.col = 0))
    (hvalid : gammaValid fp 8) :
    exists E : Fin m -> Fin cols -> Real,
      (forall i j,
        fl_givensQRTaskStepOfTask fp m cols t B i j =
          matMulRect m m cols
            (givensRotation m t.pivot t.row
              (givensC (B t.pivot t.col) (B t.row t.col))
              (givensS (B t.pivot t.col) (B t.row t.col))) B i j + E i j) /\
      frobNorm E <=
        (gamma fp 8 *
          frobNorm (givensRotation m t.pivot t.row
            (givensC (B t.pivot t.col) (B t.row t.col))
            (givensS (B t.pivot t.col) (B t.row t.col)))) * frobNorm B /\
      forall i j, i ≠ t.pivot -> i ≠ t.row -> E i j = 0 := by
  have hprev := ZeroedThrough.prev_pair_zero_of_task t hzero
  simpa [fl_givensQRTaskStepOfTask] using
    fl_givensQRTaskStep_sparse_residual_of_prev_pair_zero fp m cols
      t.pivot t.row t.col B t.pivot_ne_row hactive hprev hvalid

/-- Task-indexed columnwise residual theorem using the `ZeroedThrough`
    invariant at the task's anti-diagonal stage. -/
theorem fl_givensQRTaskStepOfTask_columnFrob_residual_of_zeroedThrough
    (fp : FPModel) (m cols : Nat) (t : GivensQRTask m cols)
    (B : Fin m -> Fin cols -> Real)
    (hzero : ZeroedThrough t.stage B)
    (hactive : Not (B t.row t.col = 0))
    (hvalid : gammaValid fp 8) :
    exists E : Fin m -> Fin cols -> Real,
      (forall i j,
        fl_givensQRTaskStepOfTask fp m cols t B i j =
          matMulRect m m cols
            (givensRotation m t.pivot t.row
              (givensC (B t.pivot t.col) (B t.row t.col))
              (givensS (B t.pivot t.col) (B t.row t.col))) B i j + E i j) /\
      (forall j,
        columnFrob E j <=
          (gamma fp 8 *
            frobNorm (givensRotation m t.pivot t.row
              (givensC (B t.pivot t.col) (B t.row t.col))
              (givensS (B t.pivot t.col) (B t.row t.col)))) *
            columnFrob B j) /\
      forall i j, i ≠ t.pivot -> i ≠ t.row -> E i j = 0 := by
  have hprev := ZeroedThrough.prev_pair_zero_of_task t hzero
  simpa [fl_givensQRTaskStepOfTask] using
    fl_givensQRTaskStep_columnFrob_residual_of_prev_pair_zero fp m cols
      t.pivot t.row t.col B t.pivot_ne_row hactive hprev hvalid

/-- Exact orthogonal factor associated with a zero-aware QR task step.

If the target entry is already zero, the computed task step is the identity and
the exact factor is `idMatrix`.  Otherwise the exact factor is the constructed
Givens rotation for the active pivot/target pair. -/
noncomputable def givensQRTaskRotation (m cols : Nat)
    (t : GivensQRTask m cols)
    (B : Fin m -> Fin cols -> Real) : Fin m -> Fin m -> Real :=
  if B t.row t.col = 0 then
    idMatrix m
  else
    givensRotation m t.pivot t.row
      (givensC (B t.pivot t.col) (B t.row t.col))
      (givensS (B t.pivot t.col) (B t.row t.col))

/-- The zero-aware exact factor for a QR task is orthogonal. -/
theorem givensQRTaskRotation_orthogonal (m cols : Nat)
    (t : GivensQRTask m cols)
    (B : Fin m -> Fin cols -> Real) :
    IsOrthogonal m (givensQRTaskRotation m cols t B) := by
  by_cases htarget : B t.row t.col = 0
  · simpa [givensQRTaskRotation, htarget] using idMatrix_orthogonal m
  · have hnz :
        (B t.pivot t.col) ^ 2 + (B t.row t.col) ^ 2 ≠ 0 := by
      intro hsum
      have hq_sq_zero : (B t.row t.col) ^ 2 = 0 := by
        apply le_antisymm
        · calc
            (B t.row t.col) ^ 2
                <= (B t.pivot t.col) ^ 2 + (B t.row t.col) ^ 2 := by
                  exact le_add_of_nonneg_left (sq_nonneg (B t.pivot t.col))
            _ = 0 := hsum
        · exact sq_nonneg (B t.row t.col)
      exact htarget (sq_eq_zero_iff.mp hq_sq_zero)
    exact by
      simpa [givensQRTaskRotation, htarget] using
        givensRotation_constructed_orthogonal m t.pivot t.row
          (B t.pivot t.col) (B t.row t.col) t.pivot_ne_row hnz

/-- The zero-aware exact factor has the Frobenius norm of an orthogonal matrix. -/
theorem givensQRTaskRotation_frobNorm (m cols : Nat)
    (t : GivensQRTask m cols)
    (B : Fin m -> Fin cols -> Real) :
    frobNorm (givensQRTaskRotation m cols t B) = Real.sqrt (m : Real) :=
  (givensQRTaskRotation_orthogonal m cols t B).frobNorm_eq_sqrt_card

/-- Zero-aware columnwise residual theorem for one QR task step.

Inactive tasks use the identity exact factor and zero residual; active tasks
reuse the sparse columnwise residual theorem and the orthogonal Frobenius norm
of the exact Givens factor. -/
theorem fl_givensQRTaskStepOfTask_columnFrob_uniform_of_zeroedThrough
    (fp : FPModel) (m cols : Nat) (t : GivensQRTask m cols)
    (B : Fin m -> Fin cols -> Real)
    (hzero : ZeroedThrough t.stage B)
    (hvalid : gammaValid fp 8) :
    exists E : Fin m -> Fin cols -> Real,
      (forall i j,
        fl_givensQRTaskStepOfTask fp m cols t B i j =
          matMulRect m m cols (givensQRTaskRotation m cols t B) B i j +
            E i j) /\
      (forall j,
        columnFrob E j <=
          (gamma fp 8 * Real.sqrt (m : Real)) * columnFrob B j) /\
      forall i j, i ≠ t.pivot -> i ≠ t.row -> E i j = 0 := by
  by_cases htarget : B t.row t.col = 0
  · let E : Fin m -> Fin cols -> Real := fun _ _ => 0
    refine ⟨E, ?_, ?_, ?_⟩
    · intro i j
      have hstep :
          fl_givensQRTaskStepOfTask fp m cols t B = B := by
        simp [fl_givensQRTaskStepOfTask, fl_givensQRTaskStep, htarget]
      rw [hstep]
      have hrot :
          givensQRTaskRotation m cols t B = idMatrix m := by
        simp [givensQRTaskRotation, htarget]
      rw [hrot, matMulRect_id_left]
      simp [E]
    · intro j
      have hE0 : columnFrob E j = 0 := by
        rw [columnFrob, frobNorm_eq_zero_iff]
        intro i u
        rfl
      rw [hE0]
      exact mul_nonneg
        (mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg _))
        (columnFrob_nonneg B j)
    · intro i j _hip _hiq
      rfl
  · obtain ⟨E, hrepr, hcol, hrows⟩ :=
      fl_givensQRTaskStepOfTask_columnFrob_residual_of_zeroedThrough
        fp m cols t B hzero htarget hvalid
    refine ⟨E, ?_, ?_, hrows⟩
    · intro i j
      simpa [givensQRTaskRotation, htarget] using hrepr i j
    · intro j
      have hrot_norm :
          frobNorm (givensRotation m t.pivot t.row
              (givensC (B t.pivot t.col) (B t.row t.col))
              (givensS (B t.pivot t.col) (B t.row t.col))) =
            Real.sqrt (m : Real) := by
        simpa [givensQRTaskRotation, htarget] using
          givensQRTaskRotation_frobNorm m cols t B
      calc
        columnFrob E j <=
            (gamma fp 8 *
              frobNorm (givensRotation m t.pivot t.row
                (givensC (B t.pivot t.col) (B t.row t.col))
                (givensS (B t.pivot t.col) (B t.row t.col)))) *
              columnFrob B j := hcol j
        _ = (gamma fp 8 * Real.sqrt (m : Real)) * columnFrob B j := by
            rw [hrot_norm]

/-- One residual-form orthogonal step for rectangular columnwise perturbation
    bounds.  This is the columnwise analogue of
    `orthogonal_sequence_one_step_of_residual_rect`. -/
theorem orthogonal_sequence_one_step_of_columnFrob_residual_rect (m p : Nat)
    (A A_hat : Fin m -> Fin p -> Real)
    (Q : Fin m -> Fin m -> Real) (dA : Fin m -> Fin p -> Real)
    (hQ : IsOrthogonal m Q)
    (hAhat : forall i j, A_hat i j =
      matMulRect m m p (matTranspose Q)
        (fun a b => A a b + dA a b) i j)
    (P : Fin m -> Fin m -> Real) (hP : IsOrthogonal m P)
    (A_next E : Fin m -> Fin p -> Real) (c_step : Real)
    (hNext : forall i j, A_next i j =
      matMulRect m m p P A_hat i j + E i j)
    (hE : forall j, columnFrob E j <= c_step * columnFrob A_hat j) :
    exists (Q' : Fin m -> Fin m -> Real) (dA' : Fin m -> Fin p -> Real),
      IsOrthogonal m Q' /\
      (forall i j, A_next i j =
        matMulRect m m p (matTranspose Q')
          (fun a b => A a b + dA' a b) i j) /\
      forall j, columnFrob dA' j <=
        columnFrob dA j +
          c_step * columnFrob (fun a b => A a b + dA a b) j := by
  let Q' := matMul m Q (matTranspose P)
  let B : Fin m -> Fin p -> Real := fun a b => A a b + dA a b
  let E' : Fin m -> Fin p -> Real := matMulRect m m p Q' E
  let dA' : Fin m -> Fin p -> Real := fun a b => dA a b + E' a b
  have hQ' : IsOrthogonal m Q' := hQ.mul hP.transpose
  have hAhat_mat : A_hat = matMulRect m m p (matTranspose Q) B :=
    funext fun k => funext fun l => hAhat k l
  have hQ'inv : matMul m (matTranspose Q') Q' = idMatrix m :=
    funext fun a => funext fun b => hQ'.left_inv a b
  have hQ'T : matTranspose Q' = matMul m P (matTranspose Q) := by
    show matTranspose (matMul m Q (matTranspose P)) = _
    rw [matTranspose_matMul, matTranspose_involutive]
  have eq1 :
      matMulRect m m p (matTranspose Q') B =
        matMulRect m m p P A_hat := by
    rw [hQ'T, matMulRect_assoc_square_left, <- hAhat_mat]
  have eq2 : matMulRect m m p (matTranspose Q') E' = E := by
    show matMulRect m m p (matTranspose Q') (matMulRect m m p Q' E) = _
    rw [<- matMulRect_assoc_square_left, hQ'inv, matMulRect_id_left]
  refine ⟨Q', dA', hQ', ?_, ?_⟩
  · have hBE : (fun a b => A a b + dA' a b) = fun a b => B a b + E' a b :=
      funext fun a => funext fun b =>
        show A a b + (dA a b + E' a b) =
          (A a b + dA a b) + E' a b from by ring
    intro i j
    rw [hNext i j, hBE]
    calc matMulRect m m p P A_hat i j + E i j
        = matMulRect m m p (matTranspose Q') B i j +
            matMulRect m m p (matTranspose Q') E' i j := by
          rw [<- congr_fun (congr_fun eq1 i) j,
            <- congr_fun (congr_fun eq2 i) j]
      _ = matMulRect m m p (matTranspose Q') (fun a b => B a b + E' a b) i j := by
          exact (congr_fun
            (congr_fun (matMulRect_add_right m m p (matTranspose Q') B E') i) j).symm
  · intro j
    have hE'col : columnFrob E' j = columnFrob E j := by
      show columnFrob (matMulRect m m p Q' E) j = columnFrob E j
      exact columnFrob_orthogonal_left Q' E hQ' j
    have hAhat_col :
        columnFrob A_hat j = columnFrob B j := by
      rw [hAhat_mat]
      exact columnFrob_orthogonal_left (matTranspose Q) B hQ.transpose j
    calc
      columnFrob dA' j
          = columnFrob (fun a b => dA a b + E' a b) j := rfl
      _ <= columnFrob dA j + columnFrob E' j :=
          columnFrob_add_le dA E' j
      _ = columnFrob dA j + columnFrob E j := by
          rw [hE'col]
      _ <= columnFrob dA j + c_step * columnFrob A_hat j := by
          linarith [hE j]
      _ = columnFrob dA j + c_step * columnFrob B j := by
          rw [hAhat_col]

/-- Repeated residual-form orthogonal sequence theorem for rectangular panels,
    preserving columnwise perturbation bounds. -/
theorem residual_orthogonal_sequence_columnFrob_backward_error_rect
    (m p r : Nat)
    (Aseq : Nat -> Fin m -> Fin p -> Real)
    (Pseq : Nat -> Fin m -> Fin m -> Real) (c : Real) (hc : 0 <= c)
    (hP : forall k : Nat, k < r -> IsOrthogonal m (Pseq k))
    (hStep : forall k : Nat, k < r ->
      exists E : Fin m -> Fin p -> Real,
        (forall (i : Fin m) (j : Fin p), Aseq (k + 1) i j =
          matMulRect m m p (Pseq k) (Aseq k) i j + E i j) /\
        (forall j, columnFrob E j <= c * columnFrob (Aseq k) j)) :
    exists (Q : Fin m -> Fin m -> Real) (dA : Fin m -> Fin p -> Real),
      IsOrthogonal m Q /\
      (forall (i : Fin m) (j : Fin p), Aseq r i j =
        matMulRect m m p (matTranspose Q)
          (fun a b => Aseq 0 a b + dA a b) i j) /\
      (forall j, columnFrob dA j <=
        residualAccumBound c r * columnFrob (Aseq 0) j) := by
  induction r with
  | zero =>
      let Z : Fin m -> Fin p -> Real := fun _ _ => 0
      refine ⟨idMatrix m, Z, idMatrix_orthogonal m, ?_, ?_⟩
      · intro i j
        simp [Z, matTranspose_id, matMulRect_id_left]
      · intro j
        have hZ : columnFrob Z j = 0 := by
          rw [columnFrob, frobNorm_eq_zero_iff]
          intro i u
          rfl
        simp [residualAccumBound, Z, hZ]
  | succ r ih =>
      have hP_prefix : forall k : Nat, k < r -> IsOrthogonal m (Pseq k) := by
        intro k hk
        exact hP k (Nat.lt_trans hk (Nat.lt_succ_self r))
      have hStep_prefix : forall k : Nat, k < r ->
          exists E : Fin m -> Fin p -> Real,
            (forall (i : Fin m) (j : Fin p), Aseq (k + 1) i j =
              matMulRect m m p (Pseq k) (Aseq k) i j + E i j) /\
            (forall j, columnFrob E j <= c * columnFrob (Aseq k) j) := by
        intro k hk
        exact hStep k (Nat.lt_trans hk (Nat.lt_succ_self r))
      obtain ⟨Q, dA, hQ, hAhat, hdA⟩ := ih hP_prefix hStep_prefix
      obtain ⟨E, hNext, hE⟩ := hStep r (Nat.lt_succ_self r)
      obtain ⟨Q', dA', hQ', hRep, hStepBound⟩ :=
        orthogonal_sequence_one_step_of_columnFrob_residual_rect m p
          (Aseq 0) (Aseq r) Q dA hQ hAhat
          (Pseq r) (hP r (Nat.lt_succ_self r))
          (Aseq (r + 1)) E c hNext hE
      refine ⟨Q', dA', hQ', ?_, ?_⟩
      · simpa using hRep
      · intro j
        let alpha : Real := residualAccumBound c r
        let N : Real := columnFrob (Aseq 0) j
        have hdA_j : columnFrob dA j <= alpha * N := by
          simpa [alpha, N] using hdA j
        have hB :
            columnFrob (fun a b => Aseq 0 a b + dA a b) j <=
              (1 + alpha) * N := by
          calc
            columnFrob (fun a b => Aseq 0 a b + dA a b) j
                <= columnFrob (Aseq 0) j + columnFrob dA j :=
                  columnFrob_add_le (Aseq 0) dA j
            _ <= N + alpha * N := by
                simpa [N] using
                  add_le_add_left hdA_j (columnFrob (Aseq 0) j)
            _ = (1 + alpha) * N := by ring
        have htotal :
            columnFrob dA' j <= alpha * N + c * ((1 + alpha) * N) := by
          calc
            columnFrob dA' j
                <= columnFrob dA j +
                    c * columnFrob (fun a b => Aseq 0 a b + dA a b) j :=
                  hStepBound j
            _ <= alpha * N + c * ((1 + alpha) * N) := by
                exact add_le_add hdA_j (mul_le_mul_of_nonneg_left hB hc)
        have hrec :
            residualAccumBound c (r + 1) * N =
              alpha * N + c * ((1 + alpha) * N) := by
          simp [residualAccumBound, alpha]
          ring
        rw [show residualAccumBound c (r + 1) * columnFrob (Aseq 0) j =
            alpha * N + c * ((1 + alpha) * N) from by
          rw [<- hrec]]
        exact htotal

/-- Zero-aware task residual theorem.

This removes the active-target side condition needed by
`fl_givensQRTaskStepOfTask_sparse_residual_of_zeroedThrough`: inactive tasks are
represented by the identity exact factor and a zero residual, while active tasks
reuse the sparse Givens residual. -/
theorem fl_givensQRTaskStepOfTask_residual_of_zeroedThrough
    (fp : FPModel) (m cols : Nat) (t : GivensQRTask m cols)
    (B : Fin m -> Fin cols -> Real)
    (hzero : ZeroedThrough t.stage B)
    (hvalid : gammaValid fp 8) :
    exists E : Fin m -> Fin cols -> Real,
      (forall i j,
        fl_givensQRTaskStepOfTask fp m cols t B i j =
          matMulRect m m cols (givensQRTaskRotation m cols t B) B i j +
            E i j) /\
      frobNorm E <=
        (gamma fp 8 * frobNorm (givensQRTaskRotation m cols t B)) *
          frobNorm B /\
      forall i j, i ≠ t.pivot -> i ≠ t.row -> E i j = 0 := by
  by_cases htarget : B t.row t.col = 0
  · let E : Fin m -> Fin cols -> Real := fun _ _ => 0
    refine ⟨E, ?_, ?_, ?_⟩
    · intro i j
      have hstep :
          fl_givensQRTaskStepOfTask fp m cols t B = B := by
        simp [fl_givensQRTaskStepOfTask, fl_givensQRTaskStep, htarget]
      rw [hstep]
      have hrot :
          givensQRTaskRotation m cols t B = idMatrix m := by
        simp [givensQRTaskRotation, htarget]
      rw [hrot, matMulRect_id_left]
      simp [E]
    · have hE0 : frobNorm E = 0 := by
        rw [frobNorm_eq_zero_iff]
        intro i j
        rfl
      rw [hE0]
      exact mul_nonneg
        (mul_nonneg (gamma_nonneg fp hvalid) (frobNorm_nonneg _))
        (frobNorm_nonneg B)
    · intro i j _hip _hiq
      rfl
  · obtain ⟨E, hrepr, hbound, hrows⟩ :=
      fl_givensQRTaskStepOfTask_sparse_residual_of_zeroedThrough
        fp m cols t B hzero htarget hvalid
    refine ⟨E, ?_, ?_, hrows⟩
    · intro i j
      simpa [givensQRTaskRotation, htarget] using hrepr i j
    · simpa [givensQRTaskRotation, htarget] using hbound

/-- Uniform Frobenius-norm bound for the zero-aware task residual. -/
theorem fl_givensQRTaskStepOfTask_residual_uniform_of_zeroedThrough
    (fp : FPModel) (m cols : Nat) (t : GivensQRTask m cols)
    (B : Fin m -> Fin cols -> Real)
    (hzero : ZeroedThrough t.stage B)
    (hvalid : gammaValid fp 8) :
    exists E : Fin m -> Fin cols -> Real,
      (forall i j,
        fl_givensQRTaskStepOfTask fp m cols t B i j =
          matMulRect m m cols (givensQRTaskRotation m cols t B) B i j +
            E i j) /\
      frobNorm E <=
        (gamma fp 8 * Real.sqrt (m : Real)) * frobNorm B /\
      forall i j, i ≠ t.pivot -> i ≠ t.row -> E i j = 0 := by
  obtain ⟨E, hrepr, hbound, hrows⟩ :=
    fl_givensQRTaskStepOfTask_residual_of_zeroedThrough
      fp m cols t B hzero hvalid
  refine ⟨E, hrepr, ?_, hrows⟩
  calc
    frobNorm E
        <= (gamma fp 8 * frobNorm (givensQRTaskRotation m cols t B)) *
          frobNorm B := hbound
    _ = (gamma fp 8 * Real.sqrt (m : Real)) * frobNorm B := by
      rw [givensQRTaskRotation_frobNorm]

/-- Sequence accumulation for zero-aware QR task steps.

This is the normwise residual bridge for the concrete Givens QR schedule: once
a matrix sequence is known to execute a task sequence and each step has the
`ZeroedThrough` invariant required by the local sparse residual theorem, the
whole sequence has a standard orthogonal backward-error representation. -/
theorem fl_givensQRTask_sequence_backward_error_uniform
    (fp : FPModel) {m cols r : Nat}
    (Aseq : Nat -> Fin m -> Fin cols -> Real)
    (taskseq : Nat -> GivensQRTask m cols)
    (hzero : forall k : Nat, k < r -> ZeroedThrough (taskseq k).stage (Aseq k))
    (hvalid : gammaValid fp 8)
    (hAstep : forall k : Nat, k < r ->
      Aseq (k + 1) =
        fl_givensQRTaskStepOfTask fp m cols (taskseq k) (Aseq k)) :
    exists (Q : Fin m -> Fin m -> Real) (dA : Fin m -> Fin cols -> Real),
      IsOrthogonal m Q /\
      (forall (i : Fin m) (j : Fin cols), Aseq r i j =
        matMulRect m m cols (matTranspose Q)
          (fun a b => Aseq 0 a b + dA a b) i j) /\
      frobNorm dA <=
        residualAccumBound (gamma fp 8 * Real.sqrt (m : Real)) r *
          frobNorm (Aseq 0) := by
  let Pseq : Nat -> Fin m -> Fin m -> Real := fun k =>
    givensQRTaskRotation m cols (taskseq k) (Aseq k)
  apply residual_orthogonal_sequence_backward_error_rect m cols r Aseq Pseq
    (gamma fp 8 * Real.sqrt (m : Real))
  · exact mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg _)
  · intro k _hk
    exact givensQRTaskRotation_orthogonal m cols (taskseq k) (Aseq k)
  · intro k hk
    obtain ⟨E, hrepr, hbound, _hrows⟩ :=
      fl_givensQRTaskStepOfTask_residual_uniform_of_zeroedThrough
        fp m cols (taskseq k) (Aseq k) (hzero k hk) hvalid
    refine ⟨E, ?_, hbound⟩
    intro i j
    rw [hAstep k hk]
    simpa [Pseq] using hrepr i j

/-- Columnwise sequence accumulation for zero-aware QR task steps.

This keeps the per-column residual information needed for Higham's Givens QR
backward-error theorem instead of immediately collapsing it to a Frobenius
bound. -/
theorem fl_givensQRTask_sequence_columnFrob_backward_error_uniform
    (fp : FPModel) {m cols r : Nat}
    (Aseq : Nat -> Fin m -> Fin cols -> Real)
    (taskseq : Nat -> GivensQRTask m cols)
    (hzero : forall k : Nat, k < r -> ZeroedThrough (taskseq k).stage (Aseq k))
    (hvalid : gammaValid fp 8)
    (hAstep : forall k : Nat, k < r ->
      Aseq (k + 1) =
        fl_givensQRTaskStepOfTask fp m cols (taskseq k) (Aseq k)) :
    exists (Q : Fin m -> Fin m -> Real) (dA : Fin m -> Fin cols -> Real),
      IsOrthogonal m Q /\
      (forall (i : Fin m) (j : Fin cols), Aseq r i j =
        matMulRect m m cols (matTranspose Q)
          (fun a b => Aseq 0 a b + dA a b) i j) /\
      (forall j, columnFrob dA j <=
        residualAccumBound (gamma fp 8 * Real.sqrt (m : Real)) r *
          columnFrob (Aseq 0) j) := by
  let Pseq : Nat -> Fin m -> Fin m -> Real := fun k =>
    givensQRTaskRotation m cols (taskseq k) (Aseq k)
  apply residual_orthogonal_sequence_columnFrob_backward_error_rect
    m cols r Aseq Pseq (gamma fp 8 * Real.sqrt (m : Real))
  · exact mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg _)
  · intro k _hk
    exact givensQRTaskRotation_orthogonal m cols (taskseq k) (Aseq k)
  · intro k hk
    obtain ⟨E, hrepr, hcol, _hrows⟩ :=
      fl_givensQRTaskStepOfTask_columnFrob_uniform_of_zeroedThrough
        fp m cols (taskseq k) (Aseq k) (hzero k hk) hvalid
    refine ⟨E, ?_, hcol⟩
    intro i j
    rw [hAstep k hk]
    simpa [Pseq] using hrepr i j

/-- A single task at stage `s` preserves all zeros already established through
    that stage.  This is the invariant needed to compose all tasks in the same
    anti-diagonal stage before advancing the frontier. -/
theorem fl_givensQRTaskStepOfTask_preserves_zeroedThrough_stage
    (fp : FPModel) (m cols : Nat) (t : GivensQRTask m cols)
    (B : Fin m -> Fin cols -> Real)
    (hzero : ZeroedThrough t.stage B) :
    ZeroedThrough t.stage (fl_givensQRTaskStepOfTask fp m cols t B) := by
  intro i j hbelow hsum
  by_cases hjprev : j.val < t.col.val
  · unfold fl_givensQRTaskStepOfTask
    rw [fl_givensQRTaskStep_prev_col fp m cols t.pivot t.row t.col j B i hjprev]
    exact hzero i j hbelow hsum
  · have hip : i ≠ t.pivot := by
      intro hi
      have hi_val : i.val = t.col.val := by
        rw [hi]
        simp [GivensQRTask.pivot]
      exact hjprev (by omega)
    have hiq : i ≠ t.row := by
      intro hi
      have hstage := GivensQRTask.stage_succ_eq t
      have hcol_le : t.col.val ≤ j.val := Nat.le_of_not_gt hjprev
      have hi_val : i.val = t.row.val := congrArg Fin.val hi
      omega
    unfold fl_givensQRTaskStepOfTask
    by_cases hactive : B t.row t.col = 0
    · simp [fl_givensQRTaskStep, hactive, hzero i j hbelow hsum]
    · rw [fl_givensQRTaskStep_active_ne_target fp m cols t.pivot t.row
        t.col j B i hactive hjprev (Or.inl hiq)]
      unfold fl_givensApplyMatrixRect
      rw [fl_givensApply_other fp m t.pivot t.row i
        (fl_givensC fp (B t.pivot t.col) (B t.row t.col))
        (fl_givensS fp (B t.pivot t.col) (B t.row t.col))
        (fun k => B k j) hip hiq]
      exact hzero i j hbelow hsum

/-- Applying one task in a stage preserves the already-zero target of any other
    task in the same stage. -/
theorem fl_givensQRTaskStepOfTask_preserves_same_stage_target
    (fp : FPModel) (m cols : Nat) (t u : GivensQRTask m cols)
    (B : Fin m -> Fin cols -> Real)
    (hstage : t.stage = u.stage) (hne : t ≠ u)
    (huzero : B u.row u.col = 0) :
    fl_givensQRTaskStepOfTask fp m cols t B u.row u.col = 0 := by
  have hdisj := GivensQRTask.same_stage_rowPair_disjoint hstage hne
  have hip : u.row ≠ t.pivot := hdisj.2.1.symm
  have hiq : u.row ≠ t.row := hdisj.2.2.2.symm
  unfold fl_givensQRTaskStepOfTask
  by_cases hjprev : u.col.val < t.col.val
  · rw [fl_givensQRTaskStep_prev_col fp m cols t.pivot t.row t.col
      u.col B u.row hjprev]
    exact huzero
  · by_cases hactive : B t.row t.col = 0
    · simp [fl_givensQRTaskStep, hactive, huzero]
    · rw [fl_givensQRTaskStep_active_ne_target fp m cols t.pivot t.row
        t.col u.col B u.row hactive hjprev (Or.inl hiq)]
      unfold fl_givensApplyMatrixRect
      rw [fl_givensApply_other fp m t.pivot t.row u.row
        (fl_givensC fp (B t.pivot t.col) (B t.row t.col))
        (fl_givensS fp (B t.pivot t.col) (B t.row t.col))
        (fun k => B k u.col) hip hiq]
      exact huzero

/-- Sequentially apply a finite list of zero-aware QR tasks.  This is a local
    schedule combinator used to assemble one anti-diagonal stage. -/
noncomputable def fl_givensQRTaskList (fp : FPModel) (m cols : Nat)
    (tasks : List (GivensQRTask m cols))
    (B : Fin m -> Fin cols -> Real) : Fin m -> Fin cols -> Real :=
  match tasks with
  | [] => B
  | t :: ts =>
      fl_givensQRTaskList fp m cols ts
        (fl_givensQRTaskStepOfTask fp m cols t B)

/-- A finite list of tasks all in stage `s` preserves zeros already established
    through that stage. -/
theorem fl_givensQRTaskList_preserves_zeroedThrough_stage
    (fp : FPModel) (m cols : Nat)
    (tasks : List (GivensQRTask m cols))
    (B : Fin m -> Fin cols -> Real) (s : Nat)
    (hstage : forall t, t ∈ tasks -> t.stage = s)
    (hzero : ZeroedThrough s B) :
    ZeroedThrough s (fl_givensQRTaskList fp m cols tasks B) := by
  induction tasks generalizing B with
  | nil =>
      simpa [fl_givensQRTaskList] using hzero
  | cons t ts ih =>
      have ht : t.stage = s := hstage t (by simp)
      have hts : forall u, u ∈ ts -> u.stage = s := by
        intro u hu
        exact hstage u (by simp [hu])
      have hzero_t : ZeroedThrough t.stage B := by
        simpa [ht] using hzero
      have hfirst_t :=
        fl_givensQRTaskStepOfTask_preserves_zeroedThrough_stage
          fp m cols t B hzero_t
      have hfirst : ZeroedThrough s
          (fl_givensQRTaskStepOfTask fp m cols t B) := by
        simpa [ht] using hfirst_t
      simpa [fl_givensQRTaskList] using ih
        (B := fl_givensQRTaskStepOfTask fp m cols t B) hts hfirst

/-- A finite list of tasks in one stage preserves a distinct same-stage target
    that is already zero. -/
theorem fl_givensQRTaskList_preserves_same_stage_target
    (fp : FPModel) (m cols : Nat)
    (tasks : List (GivensQRTask m cols))
    (B : Fin m -> Fin cols -> Real) (u : GivensQRTask m cols) (s : Nat)
    (hustage : u.stage = s)
    (hstage : forall t, t ∈ tasks -> t.stage = s)
    (hne : forall t, t ∈ tasks -> t ≠ u)
    (huzero : B u.row u.col = 0) :
    fl_givensQRTaskList fp m cols tasks B u.row u.col = 0 := by
  induction tasks generalizing B with
  | nil =>
      simpa [fl_givensQRTaskList] using huzero
  | cons t ts ih =>
      have ht : t.stage = s := hstage t (by simp)
      have hts : forall v, v ∈ ts -> v.stage = s := by
        intro v hv
        exact hstage v (by simp [hv])
      have hne_t : t ≠ u := hne t (by simp)
      have hne_ts : forall v, v ∈ ts -> v ≠ u := by
        intro v hv
        exact hne v (by simp [hv])
      have htu : t.stage = u.stage := by
        rw [ht, hustage]
      have hfirst :=
        fl_givensQRTaskStepOfTask_preserves_same_stage_target
          fp m cols t u B htu hne_t huzero
      simpa [fl_givensQRTaskList] using ih
        (B := fl_givensQRTaskStepOfTask fp m cols t B)
        hts hne_ts hfirst

/-- Every task target in a duplicate-free finite same-stage list is zero after
    executing the whole list. -/
theorem fl_givensQRTaskList_stage_target_zero_of_mem
    (fp : FPModel) (m cols : Nat)
    (tasks : List (GivensQRTask m cols))
    (B : Fin m -> Fin cols -> Real) (s : Nat)
    (hstage : forall t, t ∈ tasks -> t.stage = s)
    (hnodup : tasks.Nodup)
    (hzero : ZeroedThrough s B) :
    forall u, u ∈ tasks ->
      fl_givensQRTaskList fp m cols tasks B u.row u.col = 0 := by
  induction tasks generalizing B with
  | nil =>
      intro u hu
      cases hu
  | cons t ts ih =>
      intro u hu
      cases hnodup with
      | cons hnotin hnodup_ts =>
          have ht : t.stage = s := hstage t (by simp)
          have hts : forall v, v ∈ ts -> v.stage = s := by
            intro v hv
            exact hstage v (by simp [hv])
          have hzero_t : ZeroedThrough t.stage B := by
            simpa [ht] using hzero
          have hfirst_zeroed_t :=
            fl_givensQRTaskStepOfTask_preserves_zeroedThrough_stage
              fp m cols t B hzero_t
          have hfirst_zeroed : ZeroedThrough s
              (fl_givensQRTaskStepOfTask fp m cols t B) := by
            simpa [ht] using hfirst_zeroed_t
          have hu_cases : u = t \/ u ∈ ts := by
            simpa [List.mem_cons] using hu
          cases hu_cases with
          | inl hut =>
              subst u
              have htarget0 :
                  fl_givensQRTaskStepOfTask fp m cols t B t.row t.col = 0 := by
                simp [fl_givensQRTaskStepOfTask]
              have hrest_ne : forall v, v ∈ ts -> v ≠ t := by
                intro v hv hvt
                exact (hnotin v hv) hvt.symm
              have hrest_zero :=
                fl_givensQRTaskList_preserves_same_stage_target
                  fp m cols ts
                  (fl_givensQRTaskStepOfTask fp m cols t B) t s
                  ht hts hrest_ne htarget0
              simpa [fl_givensQRTaskList] using hrest_zero
          | inr huts =>
              have htail :=
                ih (B := fl_givensQRTaskStepOfTask fp m cols t B)
                  hts hnodup_ts hfirst_zeroed u huts
              simpa [fl_givensQRTaskList] using htail

/-- If a duplicate-free finite task list covers one stage, executing it advances
    the `ZeroedThrough` frontier by one. -/
theorem fl_givensQRTaskList_zeroedThrough_succ_of_stage_complete
    (fp : FPModel) (m cols : Nat)
    (tasks : List (GivensQRTask m cols))
    (B : Fin m -> Fin cols -> Real) (s : Nat)
    (hstage : forall t, t ∈ tasks -> t.stage = s)
    (hnodup : tasks.Nodup)
    (hcomplete : forall t : GivensQRTask m cols, t.stage = s -> t ∈ tasks)
    (hzero : ZeroedThrough s B) :
    ZeroedThrough (s + 1) (fl_givensQRTaskList fp m cols tasks B) := by
  have hzero_s :=
    fl_givensQRTaskList_preserves_zeroedThrough_stage
      fp m cols tasks B s hstage hzero
  apply ZeroedThrough.succ_of_stageTargetsZero hzero_s
  intro t htstage
  exact fl_givensQRTaskList_stage_target_zero_of_mem
    fp m cols tasks B s hstage hnodup hzero t (hcomplete t htstage)

/-- Executing the concrete finite task list for stage `s` advances the
    `ZeroedThrough` frontier by one stage. -/
theorem fl_givensQRStageTasks_zeroedThrough_succ
    (fp : FPModel) (m cols : Nat)
    (B : Fin m -> Fin cols -> Real) (s : Nat)
    (hzero : ZeroedThrough s B) :
    ZeroedThrough (s + 1)
      (fl_givensQRTaskList fp m cols (givensQRStageTasks m cols s) B) := by
  exact fl_givensQRTaskList_zeroedThrough_succ_of_stage_complete
    fp m cols (givensQRStageTasks m cols s) B s
    givensQRStageTasks_stage
    (givensQRStageTasks_nodup m cols s)
    givensQRStageTasks_complete
    hzero

/-- Every prefix of a same-stage task list preserves the stage frontier. -/
theorem fl_givensQRTaskList_take_preserves_zeroedThrough_stage
    (fp : FPModel) (m cols : Nat)
    (tasks : List (GivensQRTask m cols))
    (B : Fin m -> Fin cols -> Real) (s n : Nat)
    (hstage : forall t, t ∈ tasks -> t.stage = s)
    (hzero : ZeroedThrough s B) :
    ZeroedThrough s
      (fl_givensQRTaskList fp m cols (tasks.take n) B) := by
  have htake_subset : forall t, t ∈ tasks.take n -> t ∈ tasks := by
    intro t ht
    exact (List.take_sublist n tasks).subset ht
  exact fl_givensQRTaskList_preserves_zeroedThrough_stage
    fp m cols (tasks.take n) B s
    (by
      intro t ht
      exact hstage t (htake_subset t ht))
    hzero

/-- Every prefix of the concrete filtered task list for stage `s` preserves the
    `ZeroedThrough s` frontier. -/
theorem fl_givensQRStageTasks_take_preserves_zeroedThrough
    (fp : FPModel) (m cols : Nat)
    (B : Fin m -> Fin cols -> Real) (s n : Nat)
    (hzero : ZeroedThrough s B) :
    ZeroedThrough s
      (fl_givensQRTaskList fp m cols
        ((givensQRStageTasks m cols s).take n) B) := by
  exact fl_givensQRTaskList_take_preserves_zeroedThrough_stage
    fp m cols (givensQRStageTasks m cols s) B s n
    givensQRStageTasks_stage hzero

/-- A concrete same-stage task has the zero-aware residual theorem available
    after any prefix of that same concrete stage list has executed. -/
theorem fl_givensQRStageTasks_prefix_task_residual_uniform
    (fp : FPModel) (m cols : Nat)
    (B : Fin m -> Fin cols -> Real) (s n : Nat)
    (t : GivensQRTask m cols)
    (ht : t ∈ givensQRStageTasks m cols s)
    (hzero : ZeroedThrough s B)
    (hvalid : gammaValid fp 8) :
    exists E : Fin m -> Fin cols -> Real,
      (forall i j,
        fl_givensQRTaskStepOfTask fp m cols t
            (fl_givensQRTaskList fp m cols
              ((givensQRStageTasks m cols s).take n) B) i j =
          matMulRect m m cols
            (givensQRTaskRotation m cols t
              (fl_givensQRTaskList fp m cols
                ((givensQRStageTasks m cols s).take n) B))
            (fl_givensQRTaskList fp m cols
              ((givensQRStageTasks m cols s).take n) B) i j +
            E i j) /\
      frobNorm E <=
        (gamma fp 8 * Real.sqrt (m : Real)) *
          frobNorm
            (fl_givensQRTaskList fp m cols
              ((givensQRStageTasks m cols s).take n) B) /\
      forall i j, i ≠ t.pivot -> i ≠ t.row -> E i j = 0 := by
  have htstage : t.stage = s := givensQRStageTasks_stage t ht
  have hprefix_s :
      ZeroedThrough s
        (fl_givensQRTaskList fp m cols
          ((givensQRStageTasks m cols s).take n) B) :=
    fl_givensQRStageTasks_take_preserves_zeroedThrough
      fp m cols B s n hzero
  have hprefix :
      ZeroedThrough t.stage
        (fl_givensQRTaskList fp m cols
          ((givensQRStageTasks m cols s).take n) B) := by
    simpa [htstage] using hprefix_s
  exact fl_givensQRTaskStepOfTask_residual_uniform_of_zeroedThrough
    fp m cols t
      (fl_givensQRTaskList fp m cols
        ((givensQRStageTasks m cols s).take n) B)
      hprefix hvalid

/-- A concrete same-stage task has the zero-aware columnwise residual theorem
    available after any prefix of that same concrete stage list has executed. -/
theorem fl_givensQRStageTasks_prefix_task_columnFrob_uniform
    (fp : FPModel) (m cols : Nat)
    (B : Fin m -> Fin cols -> Real) (s n : Nat)
    (t : GivensQRTask m cols)
    (ht : t ∈ givensQRStageTasks m cols s)
    (hzero : ZeroedThrough s B)
    (hvalid : gammaValid fp 8) :
    exists E : Fin m -> Fin cols -> Real,
      (forall i j,
        fl_givensQRTaskStepOfTask fp m cols t
            (fl_givensQRTaskList fp m cols
              ((givensQRStageTasks m cols s).take n) B) i j =
          matMulRect m m cols
            (givensQRTaskRotation m cols t
              (fl_givensQRTaskList fp m cols
                ((givensQRStageTasks m cols s).take n) B))
            (fl_givensQRTaskList fp m cols
              ((givensQRStageTasks m cols s).take n) B) i j +
            E i j) /\
      (forall j,
        columnFrob E j <=
          (gamma fp 8 * Real.sqrt (m : Real)) *
            columnFrob
              (fl_givensQRTaskList fp m cols
                ((givensQRStageTasks m cols s).take n) B) j) /\
      forall i j, i ≠ t.pivot -> i ≠ t.row -> E i j = 0 := by
  have htstage : t.stage = s := givensQRStageTasks_stage t ht
  have hprefix_s :
      ZeroedThrough s
        (fl_givensQRTaskList fp m cols
          ((givensQRStageTasks m cols s).take n) B) :=
    fl_givensQRStageTasks_take_preserves_zeroedThrough
      fp m cols B s n hzero
  have hprefix :
      ZeroedThrough t.stage
        (fl_givensQRTaskList fp m cols
          ((givensQRStageTasks m cols s).take n) B) := by
    simpa [htstage] using hprefix_s
  exact fl_givensQRTaskStepOfTask_columnFrob_uniform_of_zeroedThrough
    fp m cols t
      (fl_givensQRTaskList fp m cols
        ((givensQRStageTasks m cols s).take n) B)
      hprefix hvalid

/-- Before the first anti-diagonal stage there are no below-diagonal entries
    whose row-plus-column index is already in range. -/
theorem ZeroedThrough.zero {m cols : Nat}
    (B : Fin m -> Fin cols -> Real) :
    ZeroedThrough 0 B := by
  intro i j hbelow hsum
  omega

/-- Apply the concrete Givens QR stage lists for stages `0, ..., k - 1`. -/
noncomputable def fl_givensQRStageFold (fp : FPModel) (m cols : Nat) :
    Nat -> (Fin m -> Fin cols -> Real) -> Fin m -> Fin cols -> Real
  | 0, B => B
  | s + 1, B =>
      fl_givensQRTaskList fp m cols (givensQRStageTasks m cols s)
        (fl_givensQRStageFold fp m cols s B)

/-- The concrete stage fold establishes the `ZeroedThrough` frontier at the
    number of stages already executed. -/
theorem fl_givensQRStageFold_zeroedThrough
    (fp : FPModel) (m cols : Nat)
    (B : Fin m -> Fin cols -> Real) :
    forall k : Nat,
      ZeroedThrough k (fl_givensQRStageFold fp m cols k B) := by
  intro k
  induction k with
  | zero =>
      simpa [fl_givensQRStageFold] using
        (ZeroedThrough.zero (m := m) (cols := cols) B)
  | succ s ih =>
      simpa [fl_givensQRStageFold] using
        fl_givensQRStageTasks_zeroedThrough_succ fp m cols
          (fl_givensQRStageFold fp m cols s B) s ih

/-- After all previous stages and an arbitrary prefix of stage `s`, the
    `ZeroedThrough s` frontier is still available. -/
theorem fl_givensQRStagePrefix_zeroedThrough
    (fp : FPModel) (m cols : Nat)
    (B : Fin m -> Fin cols -> Real) (s n : Nat) :
    ZeroedThrough s
      (fl_givensQRTaskList fp m cols
        ((givensQRStageTasks m cols s).take n)
        (fl_givensQRStageFold fp m cols s B)) := by
  exact fl_givensQRStageTasks_take_preserves_zeroedThrough
    fp m cols (fl_givensQRStageFold fp m cols s B) s n
    (fl_givensQRStageFold_zeroedThrough fp m cols B s)

/-- A concrete task in stage `s` has the zero-aware residual theorem available
    after all previous stages and any prefix of its own stage have executed. -/
theorem fl_givensQRStagePrefix_task_residual_uniform
    (fp : FPModel) (m cols : Nat)
    (B : Fin m -> Fin cols -> Real) (s n : Nat)
    (t : GivensQRTask m cols)
    (ht : t ∈ givensQRStageTasks m cols s)
    (hvalid : gammaValid fp 8) :
    exists E : Fin m -> Fin cols -> Real,
      (forall i j,
        fl_givensQRTaskStepOfTask fp m cols t
            (fl_givensQRTaskList fp m cols
              ((givensQRStageTasks m cols s).take n)
              (fl_givensQRStageFold fp m cols s B)) i j =
          matMulRect m m cols
            (givensQRTaskRotation m cols t
              (fl_givensQRTaskList fp m cols
                ((givensQRStageTasks m cols s).take n)
                (fl_givensQRStageFold fp m cols s B)))
            (fl_givensQRTaskList fp m cols
              ((givensQRStageTasks m cols s).take n)
              (fl_givensQRStageFold fp m cols s B)) i j +
            E i j) /\
      frobNorm E <=
        (gamma fp 8 * Real.sqrt (m : Real)) *
          frobNorm
            (fl_givensQRTaskList fp m cols
              ((givensQRStageTasks m cols s).take n)
              (fl_givensQRStageFold fp m cols s B)) /\
      forall i j, i ≠ t.pivot -> i ≠ t.row -> E i j = 0 := by
  exact fl_givensQRStageTasks_prefix_task_residual_uniform
    fp m cols (fl_givensQRStageFold fp m cols s B) s n t ht
    (fl_givensQRStageFold_zeroedThrough fp m cols B s) hvalid

/-- After all anti-diagonal stages have executed, the stored Givens QR panel has
    the upper-trapezoidal zero pattern. -/
theorem fl_givensQRStageFold_upper_trapezoidal
    (fp : FPModel) (m cols : Nat)
    (B : Fin m -> Fin cols -> Real) :
    IsUpperTrapezoidal m cols
      (fl_givensQRStageFold fp m cols (givensQRStageCount m cols) B) := by
  intro i j hbelow
  have hzero :=
    fl_givensQRStageFold_zeroedThrough fp m cols B
      (givensQRStageCount m cols)
  exact hzero i j hbelow (by
    dsimp [givensQRStageCount]
    omega)

/-- Flatten the concrete stage lists for stages `0, ..., k - 1` into one
    execution schedule.  This is the list-level bridge needed by sequence
    accumulation theorems. -/
noncomputable def givensQRStageTaskList (m cols : Nat) :
    Nat -> List (GivensQRTask m cols)
  | 0 => []
  | s + 1 => givensQRStageTaskList m cols s ++ givensQRStageTasks m cols s

/-- Monotonicity of the residual accumulation bound in the sequence length. -/
lemma residualAccumBound_le_of_le_nat (c : Real) (hc : 0 <= c)
    {r s : Nat} (h : r <= s) :
    residualAccumBound c r <= residualAccumBound c s := by
  induction h with
  | refl =>
      rfl
  | step h ih =>
      exact le_trans ih (residualAccumBound_le_succ c hc _)

/-- Any individual stage contributes no more tasks than the flattened list of
    all stages up through a later bound. -/
theorem givensQRStageTasks_length_le_stageTaskList_length
    (m cols : Nat) {s k : Nat} (hs : s < k) :
    (givensQRStageTasks m cols s).length <=
      (givensQRStageTaskList m cols k).length := by
  induction k with
  | zero =>
      omega
  | succ k ih =>
      rw [givensQRStageTaskList]
      simp only [List.length_append]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hslt | hseq
      · have hprev := ih hslt
        omega
      · subst hseq
        omega

/-- Executing an appended task list is the same as executing the first list and
    then the second. -/
theorem fl_givensQRTaskList_append
    (fp : FPModel) (m cols : Nat)
    (xs ys : List (GivensQRTask m cols))
    (B : Fin m -> Fin cols -> Real) :
    fl_givensQRTaskList fp m cols (xs ++ ys) B =
      fl_givensQRTaskList fp m cols ys
        (fl_givensQRTaskList fp m cols xs B) := by
  induction xs generalizing B with
  | nil =>
      simp [fl_givensQRTaskList]
  | cons x xs ih =>
      simp [fl_givensQRTaskList, ih]

/-- The recursive stage fold is exactly the flat execution of the concatenated
    stage-task schedule. -/
theorem fl_givensQRStageFold_eq_taskList
    (fp : FPModel) (m cols : Nat)
    (B : Fin m -> Fin cols -> Real) :
    forall k : Nat,
      fl_givensQRStageFold fp m cols k B =
        fl_givensQRTaskList fp m cols (givensQRStageTaskList m cols k) B := by
  intro k
  induction k with
  | zero =>
      simp [fl_givensQRStageFold, givensQRStageTaskList, fl_givensQRTaskList]
  | succ s ih =>
      simp [fl_givensQRStageFold, givensQRStageTaskList,
        fl_givensQRTaskList_append, ih]

/-- A stage prefix can be viewed as a prefix of the flattened all-stage schedule:
    all stages before `s`, followed by the first `n` tasks of stage `s`. -/
theorem fl_givensQRStagePrefix_eq_taskList_append
    (fp : FPModel) (m cols : Nat)
    (B : Fin m -> Fin cols -> Real) (s n : Nat) :
    fl_givensQRTaskList fp m cols
        (givensQRStageTaskList m cols s ++ (givensQRStageTasks m cols s).take n)
        B =
      fl_givensQRTaskList fp m cols
        ((givensQRStageTasks m cols s).take n)
        (fl_givensQRStageFold fp m cols s B) := by
  rw [fl_givensQRTaskList_append]
  rw [← fl_givensQRStageFold_eq_taskList fp m cols B s]

/-- Flat-schedule form of the stage-prefix frontier invariant. -/
theorem fl_givensQRStageTaskList_prefix_zeroedThrough
    (fp : FPModel) (m cols : Nat)
    (B : Fin m -> Fin cols -> Real) (s n : Nat) :
    ZeroedThrough s
      (fl_givensQRTaskList fp m cols
        (givensQRStageTaskList m cols s ++
          (givensQRStageTasks m cols s).take n) B) := by
  simpa [fl_givensQRStagePrefix_eq_taskList_append fp m cols B s n] using
    fl_givensQRStagePrefix_zeroedThrough fp m cols B s n

/-- Executing one more task from a concrete stage prefix is exactly the computed
    step for the next task in that stage list. -/
theorem fl_givensQRStageTasks_take_succ_eq_step
    (fp : FPModel) (m cols : Nat)
    (B : Fin m -> Fin cols -> Real) (s n : Nat)
    (hn : n < (givensQRStageTasks m cols s).length) :
    fl_givensQRTaskList fp m cols
        ((givensQRStageTasks m cols s).take (n + 1)) B =
      fl_givensQRTaskStepOfTask fp m cols
        ((givensQRStageTasks m cols s)[n]'hn)
        (fl_givensQRTaskList fp m cols
          ((givensQRStageTasks m cols s).take n) B) := by
  rw [← List.take_concat_get' (givensQRStageTasks m cols s) n hn]
  rw [fl_givensQRTaskList_append]
  simp [fl_givensQRTaskList]

/-- Accumulated normwise backward-error representation for one concrete
    anti-diagonal Givens QR stage. -/
theorem fl_givensQRStageTasks_sequence_backward_error_uniform
    (fp : FPModel) (m cols : Nat)
    (B : Fin m -> Fin cols -> Real) (s : Nat)
    (hzero : ZeroedThrough s B)
    (hvalid : gammaValid fp 8) :
    exists (Q : Fin m -> Fin m -> Real) (dA : Fin m -> Fin cols -> Real),
      IsOrthogonal m Q /\
      (forall (i : Fin m) (j : Fin cols),
        fl_givensQRTaskList fp m cols (givensQRStageTasks m cols s) B i j =
          matMulRect m m cols (matTranspose Q)
            (fun a b => B a b + dA a b) i j) /\
      frobNorm dA <=
        residualAccumBound (gamma fp 8 * Real.sqrt (m : Real))
          (givensQRStageTasks m cols s).length *
            frobNorm B := by
  let tasks : List (GivensQRTask m cols) := givensQRStageTasks m cols s
  let Aseq : Nat -> Fin m -> Fin cols -> Real := fun k =>
    fl_givensQRTaskList fp m cols (tasks.take k) B
  let Pseq : Nat -> Fin m -> Fin m -> Real := fun k =>
    if h : k < tasks.length then
      givensQRTaskRotation m cols (tasks[k]'h) (Aseq k)
    else
      idMatrix m
  have hc :
      0 <= gamma fp 8 * Real.sqrt (m : Real) :=
    mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg _)
  have hP : forall k : Nat, k < tasks.length -> IsOrthogonal m (Pseq k) := by
    intro k hk
    simp [Pseq, hk, givensQRTaskRotation_orthogonal]
  have hStep :
      forall k : Nat, k < tasks.length ->
        exists E : Fin m -> Fin cols -> Real,
          (forall (i : Fin m) (j : Fin cols), Aseq (k + 1) i j =
            matMulRect m m cols (Pseq k) (Aseq k) i j + E i j) /\
          frobNorm E <=
            (gamma fp 8 * Real.sqrt (m : Real)) * frobNorm (Aseq k) := by
    intro k hk
    have ht : tasks[k]'hk ∈ givensQRStageTasks m cols s := by
      simp [tasks]
    obtain ⟨E, hrepr, hbound, _hrows⟩ :=
      fl_givensQRStageTasks_prefix_task_residual_uniform
        fp m cols B s k (tasks[k]'hk) ht hzero hvalid
    refine ⟨E, ?_, ?_⟩
    · intro i j
      have hsucc :=
        fl_givensQRStageTasks_take_succ_eq_step fp m cols B s k
          (by simpa [tasks] using hk)
      have hsucc_tasks :
          fl_givensQRTaskList fp m cols (tasks.take (k + 1)) B =
            fl_givensQRTaskStepOfTask fp m cols (tasks[k]'hk)
              (fl_givensQRTaskList fp m cols (tasks.take k) B) := by
        simpa [tasks] using hsucc
      change
        fl_givensQRTaskList fp m cols (tasks.take (k + 1)) B i j =
          matMulRect m m cols (Pseq k)
            (fl_givensQRTaskList fp m cols (tasks.take k) B) i j + E i j
      rw [hsucc_tasks]
      simpa [Pseq, Aseq, tasks, hk] using hrepr i j
    · simpa [Aseq, tasks] using hbound
  obtain ⟨Q, dA, hQ, hrepr, hbound⟩ :=
    residual_orthogonal_sequence_backward_error_rect m cols tasks.length
      Aseq Pseq (gamma fp 8 * Real.sqrt (m : Real)) hc hP hStep
  refine ⟨Q, dA, hQ, ?_, ?_⟩
  · intro i j
    simpa [Aseq, tasks, fl_givensQRTaskList] using hrepr i j
  · simpa [Aseq, tasks, fl_givensQRTaskList] using hbound

/-- Accumulated columnwise backward-error representation for one concrete
    anti-diagonal Givens QR stage. -/
theorem fl_givensQRStageTasks_sequence_columnFrob_backward_error_uniform
    (fp : FPModel) (m cols : Nat)
    (B : Fin m -> Fin cols -> Real) (s : Nat)
    (hzero : ZeroedThrough s B)
    (hvalid : gammaValid fp 8) :
    exists (Q : Fin m -> Fin m -> Real) (dA : Fin m -> Fin cols -> Real),
      IsOrthogonal m Q /\
      (forall (i : Fin m) (j : Fin cols),
        fl_givensQRTaskList fp m cols (givensQRStageTasks m cols s) B i j =
          matMulRect m m cols (matTranspose Q)
            (fun a b => B a b + dA a b) i j) /\
      (forall j,
        columnFrob dA j <=
          residualAccumBound (gamma fp 8 * Real.sqrt (m : Real))
            (givensQRStageTasks m cols s).length *
              columnFrob B j) := by
  let tasks : List (GivensQRTask m cols) := givensQRStageTasks m cols s
  let Aseq : Nat -> Fin m -> Fin cols -> Real := fun k =>
    fl_givensQRTaskList fp m cols (tasks.take k) B
  let Pseq : Nat -> Fin m -> Fin m -> Real := fun k =>
    if h : k < tasks.length then
      givensQRTaskRotation m cols (tasks[k]'h) (Aseq k)
    else
      idMatrix m
  have hc :
      0 <= gamma fp 8 * Real.sqrt (m : Real) :=
    mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg _)
  have hP : forall k : Nat, k < tasks.length -> IsOrthogonal m (Pseq k) := by
    intro k hk
    simp [Pseq, hk, givensQRTaskRotation_orthogonal]
  have hStep :
      forall k : Nat, k < tasks.length ->
        exists E : Fin m -> Fin cols -> Real,
          (forall (i : Fin m) (j : Fin cols), Aseq (k + 1) i j =
            matMulRect m m cols (Pseq k) (Aseq k) i j + E i j) /\
          (forall j,
            columnFrob E j <=
              (gamma fp 8 * Real.sqrt (m : Real)) * columnFrob (Aseq k) j) := by
    intro k hk
    have ht : tasks[k]'hk ∈ givensQRStageTasks m cols s := by
      simp [tasks]
    obtain ⟨E, hrepr, hbound, _hrows⟩ :=
      fl_givensQRStageTasks_prefix_task_columnFrob_uniform
        fp m cols B s k (tasks[k]'hk) ht hzero hvalid
    refine ⟨E, ?_, ?_⟩
    · intro i j
      have hsucc :=
        fl_givensQRStageTasks_take_succ_eq_step fp m cols B s k
          (by simpa [tasks] using hk)
      have hsucc_tasks :
          fl_givensQRTaskList fp m cols (tasks.take (k + 1)) B =
            fl_givensQRTaskStepOfTask fp m cols (tasks[k]'hk)
              (fl_givensQRTaskList fp m cols (tasks.take k) B) := by
        simpa [tasks] using hsucc
      change
        fl_givensQRTaskList fp m cols (tasks.take (k + 1)) B i j =
          matMulRect m m cols (Pseq k)
            (fl_givensQRTaskList fp m cols (tasks.take k) B) i j + E i j
      rw [hsucc_tasks]
      simpa [Pseq, Aseq, tasks, hk] using hrepr i j
    · simpa [Aseq, tasks] using hbound
  obtain ⟨Q, dA, hQ, hrepr, hbound⟩ :=
    residual_orthogonal_sequence_columnFrob_backward_error_rect m cols tasks.length
      Aseq Pseq (gamma fp 8 * Real.sqrt (m : Real)) hc hP hStep
  refine ⟨Q, dA, hQ, ?_, ?_⟩
  · intro i j
    simpa [Aseq, tasks, fl_givensQRTaskList] using hrepr i j
  · simpa [Aseq, tasks, fl_givensQRTaskList] using hbound

/-- Accumulated normwise backward-error representation for the concrete
    anti-diagonal stage fold.  This lifts the single-stage accumulation theorem
    through the full stage recursion with a conservative stage-level residual
    budget. -/
theorem fl_givensQRStageFold_sequence_backward_error_uniform
    (fp : FPModel) (m cols : Nat)
    (B : Fin m -> Fin cols -> Real) (k : Nat)
    (hvalid : gammaValid fp 8) :
    exists (Q : Fin m -> Fin m -> Real) (dA : Fin m -> Fin cols -> Real),
      IsOrthogonal m Q /\
      (forall (i : Fin m) (j : Fin cols),
        fl_givensQRStageFold fp m cols k B i j =
          matMulRect m m cols (matTranspose Q)
            (fun a b => B a b + dA a b) i j) /\
      frobNorm dA <=
        residualAccumBound
          (residualAccumBound (gamma fp 8 * Real.sqrt (m : Real))
            (givensQRStageTaskList m cols k).length) k *
            frobNorm B := by
  classical
  let base : Real := gamma fp 8 * Real.sqrt (m : Real)
  let stageBudget : Real :=
    residualAccumBound base (givensQRStageTaskList m cols k).length
  let Aseq : Nat -> Fin m -> Fin cols -> Real := fun s =>
    fl_givensQRStageFold fp m cols s B
  let stageExists (s : Nat) :
      exists qd : (Fin m -> Fin m -> Real) × (Fin m -> Fin cols -> Real),
        IsOrthogonal m qd.1 /\
        (forall (i : Fin m) (j : Fin cols),
          fl_givensQRTaskList fp m cols (givensQRStageTasks m cols s)
            (Aseq s) i j =
            matMulRect m m cols (matTranspose qd.1)
              (fun a b => Aseq s a b + qd.2 a b) i j) /\
        frobNorm qd.2 <=
          residualAccumBound base (givensQRStageTasks m cols s).length *
            frobNorm (Aseq s) := by
    obtain ⟨Q, dA, hQ, hrepr, hbound⟩ :=
      fl_givensQRStageTasks_sequence_backward_error_uniform
        fp m cols (Aseq s) s
        (by simpa [Aseq] using fl_givensQRStageFold_zeroedThrough fp m cols B s)
        hvalid
    exact ⟨(Q, dA), hQ, hrepr, by simpa [base] using hbound⟩
  let stageWitness :
      Nat -> (Fin m -> Fin m -> Real) × (Fin m -> Fin cols -> Real) :=
    fun s => Classical.choose (stageExists s)
  have stageWitness_spec :
      forall s : Nat,
        IsOrthogonal m (stageWitness s).1 /\
        (forall (i : Fin m) (j : Fin cols),
          fl_givensQRTaskList fp m cols (givensQRStageTasks m cols s)
            (Aseq s) i j =
            matMulRect m m cols (matTranspose (stageWitness s).1)
              (fun a b => Aseq s a b + (stageWitness s).2 a b) i j) /\
        frobNorm (stageWitness s).2 <=
          residualAccumBound base (givensQRStageTasks m cols s).length *
            frobNorm (Aseq s) := by
    intro s
    exact Classical.choose_spec (stageExists s)
  let Pseq : Nat -> Fin m -> Fin m -> Real := fun s =>
    matTranspose (stageWitness s).1
  have hbase : 0 <= base := by
    exact mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg _)
  have hstageBudget_nonneg : 0 <= stageBudget := by
    exact residualAccumBound_nonneg base hbase _
  have hP : forall s : Nat, s < k -> IsOrthogonal m (Pseq s) := by
    intro s _hs
    exact (stageWitness_spec s).1.transpose
  have hStep :
      forall s : Nat, s < k ->
        exists E : Fin m -> Fin cols -> Real,
          (forall (i : Fin m) (j : Fin cols), Aseq (s + 1) i j =
            matMulRect m m cols (Pseq s) (Aseq s) i j + E i j) /\
          frobNorm E <= stageBudget * frobNorm (Aseq s) := by
    intro s hs
    let Qs : Fin m -> Fin m -> Real := (stageWitness s).1
    let dAs : Fin m -> Fin cols -> Real := (stageWitness s).2
    let E : Fin m -> Fin cols -> Real := matMulRect m m cols (matTranspose Qs) dAs
    have hQ : IsOrthogonal m Qs := (stageWitness_spec s).1
    have hrepr := (stageWitness_spec s).2.1
    have hbound := (stageWitness_spec s).2.2
    refine ⟨E, ?_, ?_⟩
    · intro i j
      have hsplit :
          matMulRect m m cols (matTranspose Qs)
              (fun a b => Aseq s a b + dAs a b) i j =
            matMulRect m m cols (matTranspose Qs) (Aseq s) i j +
              matMulRect m m cols (matTranspose Qs) dAs i j := by
        exact congr_fun
          (congr_fun
            (matMulRect_add_right m m cols (matTranspose Qs) (Aseq s) dAs) i) j
      change
        fl_givensQRStageFold fp m cols (s + 1) B i j =
          matMulRect m m cols (matTranspose Qs) (Aseq s) i j + E i j
      rw [fl_givensQRStageFold]
      rw [hrepr i j, hsplit]
    · have hEeq : frobNorm E = frobNorm dAs := by
        show frobNorm (matMulRect m m cols (matTranspose Qs) dAs) = _
        exact frobNorm_orthogonal_left_rect (matTranspose Qs) dAs hQ.transpose
      have hlen :
          (givensQRStageTasks m cols s).length <=
            (givensQRStageTaskList m cols k).length :=
        givensQRStageTasks_length_le_stageTaskList_length m cols hs
      have hbudget :
          residualAccumBound base (givensQRStageTasks m cols s).length <=
            stageBudget := by
        exact residualAccumBound_le_of_le_nat base hbase hlen
      rw [hEeq]
      exact le_trans hbound
        (mul_le_mul_of_nonneg_right hbudget (frobNorm_nonneg (Aseq s)))
  obtain ⟨Q, dA, hQ, hrepr, hbound⟩ :=
    residual_orthogonal_sequence_backward_error_rect m cols k
      Aseq Pseq stageBudget hstageBudget_nonneg hP hStep
  refine ⟨Q, dA, hQ, ?_, ?_⟩
  · intro i j
    simpa [Aseq] using hrepr i j
  · simpa [Aseq, stageBudget, base] using hbound

/-- Accumulated columnwise backward-error representation for the concrete
    anti-diagonal stage fold.  This is the columnwise analogue of
    `fl_givensQRStageFold_sequence_backward_error_uniform`. -/
theorem fl_givensQRStageFold_sequence_columnFrob_backward_error_uniform
    (fp : FPModel) (m cols : Nat)
    (B : Fin m -> Fin cols -> Real) (k : Nat)
    (hvalid : gammaValid fp 8) :
    exists (Q : Fin m -> Fin m -> Real) (dA : Fin m -> Fin cols -> Real),
      IsOrthogonal m Q /\
      (forall (i : Fin m) (j : Fin cols),
        fl_givensQRStageFold fp m cols k B i j =
          matMulRect m m cols (matTranspose Q)
            (fun a b => B a b + dA a b) i j) /\
      (forall j,
        columnFrob dA j <=
          residualAccumBound
            (residualAccumBound (gamma fp 8 * Real.sqrt (m : Real))
              (givensQRStageTaskList m cols k).length) k *
              columnFrob B j) := by
  classical
  let base : Real := gamma fp 8 * Real.sqrt (m : Real)
  let stageBudget : Real :=
    residualAccumBound base (givensQRStageTaskList m cols k).length
  let Aseq : Nat -> Fin m -> Fin cols -> Real := fun s =>
    fl_givensQRStageFold fp m cols s B
  let stageExists (s : Nat) :
      exists qd : (Fin m -> Fin m -> Real) × (Fin m -> Fin cols -> Real),
        IsOrthogonal m qd.1 /\
        (forall (i : Fin m) (j : Fin cols),
          fl_givensQRTaskList fp m cols (givensQRStageTasks m cols s)
            (Aseq s) i j =
            matMulRect m m cols (matTranspose qd.1)
              (fun a b => Aseq s a b + qd.2 a b) i j) /\
        (forall j,
          columnFrob qd.2 j <=
            residualAccumBound base (givensQRStageTasks m cols s).length *
              columnFrob (Aseq s) j) := by
    obtain ⟨Q, dA, hQ, hrepr, hbound⟩ :=
      fl_givensQRStageTasks_sequence_columnFrob_backward_error_uniform
        fp m cols (Aseq s) s
        (by simpa [Aseq] using fl_givensQRStageFold_zeroedThrough fp m cols B s)
        hvalid
    exact ⟨(Q, dA), hQ, hrepr, by
      intro j
      simpa [base] using hbound j⟩
  let stageWitness :
      Nat -> (Fin m -> Fin m -> Real) × (Fin m -> Fin cols -> Real) :=
    fun s => Classical.choose (stageExists s)
  have stageWitness_spec :
      forall s : Nat,
        IsOrthogonal m (stageWitness s).1 /\
        (forall (i : Fin m) (j : Fin cols),
          fl_givensQRTaskList fp m cols (givensQRStageTasks m cols s)
            (Aseq s) i j =
            matMulRect m m cols (matTranspose (stageWitness s).1)
              (fun a b => Aseq s a b + (stageWitness s).2 a b) i j) /\
        (forall j,
          columnFrob (stageWitness s).2 j <=
            residualAccumBound base (givensQRStageTasks m cols s).length *
              columnFrob (Aseq s) j) := by
    intro s
    exact Classical.choose_spec (stageExists s)
  let Pseq : Nat -> Fin m -> Fin m -> Real := fun s =>
    matTranspose (stageWitness s).1
  have hbase : 0 <= base := by
    exact mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg _)
  have hstageBudget_nonneg : 0 <= stageBudget := by
    exact residualAccumBound_nonneg base hbase _
  have hP : forall s : Nat, s < k -> IsOrthogonal m (Pseq s) := by
    intro s _hs
    exact (stageWitness_spec s).1.transpose
  have hStep :
      forall s : Nat, s < k ->
        exists E : Fin m -> Fin cols -> Real,
          (forall (i : Fin m) (j : Fin cols), Aseq (s + 1) i j =
            matMulRect m m cols (Pseq s) (Aseq s) i j + E i j) /\
          (forall j, columnFrob E j <= stageBudget * columnFrob (Aseq s) j) := by
    intro s hs
    let Qs : Fin m -> Fin m -> Real := (stageWitness s).1
    let dAs : Fin m -> Fin cols -> Real := (stageWitness s).2
    let E : Fin m -> Fin cols -> Real := matMulRect m m cols (matTranspose Qs) dAs
    have hQ : IsOrthogonal m Qs := (stageWitness_spec s).1
    have hrepr := (stageWitness_spec s).2.1
    have hbound := (stageWitness_spec s).2.2
    refine ⟨E, ?_, ?_⟩
    · intro i j
      have hsplit :
          matMulRect m m cols (matTranspose Qs)
              (fun a b => Aseq s a b + dAs a b) i j =
            matMulRect m m cols (matTranspose Qs) (Aseq s) i j +
              matMulRect m m cols (matTranspose Qs) dAs i j := by
        exact congr_fun
          (congr_fun
            (matMulRect_add_right m m cols (matTranspose Qs) (Aseq s) dAs) i) j
      change
        fl_givensQRStageFold fp m cols (s + 1) B i j =
          matMulRect m m cols (matTranspose Qs) (Aseq s) i j + E i j
      rw [fl_givensQRStageFold]
      rw [hrepr i j, hsplit]
    · intro j
      have hEeq : columnFrob E j = columnFrob dAs j := by
        show columnFrob (matMulRect m m cols (matTranspose Qs) dAs) j = _
        exact columnFrob_orthogonal_left (matTranspose Qs) dAs hQ.transpose j
      have hlen :
          (givensQRStageTasks m cols s).length <=
            (givensQRStageTaskList m cols k).length :=
        givensQRStageTasks_length_le_stageTaskList_length m cols hs
      have hbudget :
          residualAccumBound base (givensQRStageTasks m cols s).length <=
            stageBudget := by
        exact residualAccumBound_le_of_le_nat base hbase hlen
      rw [hEeq]
      exact le_trans (hbound j)
        (mul_le_mul_of_nonneg_right hbudget (columnFrob_nonneg (Aseq s) j))
  obtain ⟨Q, dA, hQ, hrepr, hbound⟩ :=
    residual_orthogonal_sequence_columnFrob_backward_error_rect m cols k
      Aseq Pseq stageBudget hstageBudget_nonneg hP hStep
  refine ⟨Q, dA, hQ, ?_, ?_⟩
  · intro i j
    simpa [Aseq] using hrepr i j
  · intro j
    simpa [Aseq, stageBudget, base] using hbound j

/-- Flat-schedule form of the concrete prefix successor equation. -/
theorem fl_givensQRStageTaskList_prefix_succ_eq_step
    (fp : FPModel) (m cols : Nat)
    (B : Fin m -> Fin cols -> Real) (s n : Nat)
    (hn : n < (givensQRStageTasks m cols s).length) :
    fl_givensQRTaskList fp m cols
        (givensQRStageTaskList m cols s ++
          (givensQRStageTasks m cols s).take (n + 1)) B =
      fl_givensQRTaskStepOfTask fp m cols
        ((givensQRStageTasks m cols s)[n]'hn)
        (fl_givensQRTaskList fp m cols
          (givensQRStageTaskList m cols s ++
            (givensQRStageTasks m cols s).take n) B) := by
  rw [← List.take_concat_get' (givensQRStageTasks m cols s) n hn]
  rw [← List.append_assoc]
  rw [fl_givensQRTaskList_append]
  simp [fl_givensQRTaskList]

/-- Flat-schedule form of the stage-prefix residual hook.  This is the form
    needed to instantiate task-sequence accumulation over the concrete QR
    schedule. -/
theorem fl_givensQRStageTaskList_prefix_task_residual_uniform
    (fp : FPModel) (m cols : Nat)
    (B : Fin m -> Fin cols -> Real) (s n : Nat)
    (t : GivensQRTask m cols)
    (ht : t ∈ givensQRStageTasks m cols s)
    (hvalid : gammaValid fp 8) :
    exists E : Fin m -> Fin cols -> Real,
      (forall i j,
        fl_givensQRTaskStepOfTask fp m cols t
            (fl_givensQRTaskList fp m cols
              (givensQRStageTaskList m cols s ++
                (givensQRStageTasks m cols s).take n) B) i j =
          matMulRect m m cols
            (givensQRTaskRotation m cols t
              (fl_givensQRTaskList fp m cols
                (givensQRStageTaskList m cols s ++
                  (givensQRStageTasks m cols s).take n) B))
            (fl_givensQRTaskList fp m cols
              (givensQRStageTaskList m cols s ++
                (givensQRStageTasks m cols s).take n) B) i j +
            E i j) /\
      frobNorm E <=
        (gamma fp 8 * Real.sqrt (m : Real)) *
          frobNorm
            (fl_givensQRTaskList fp m cols
              (givensQRStageTaskList m cols s ++
                (givensQRStageTasks m cols s).take n) B) /\
      forall i j, i ≠ t.pivot -> i ≠ t.row -> E i j = 0 := by
  simpa [fl_givensQRStagePrefix_eq_taskList_append fp m cols B s n] using
    fl_givensQRStagePrefix_task_residual_uniform
      fp m cols B s n t ht hvalid

/-- A task occurs in the flattened first `k` stages exactly when its stage is
    below `k`. -/
theorem mem_givensQRStageTaskList_iff {m cols k : Nat}
    (t : GivensQRTask m cols) :
    t ∈ givensQRStageTaskList m cols k ↔ t.stage < k := by
  induction k with
  | zero =>
      simp [givensQRStageTaskList]
  | succ s ih =>
      constructor
      · intro ht
        have hmem :
            t ∈ givensQRStageTaskList m cols s ∨
              t ∈ givensQRStageTasks m cols s := by
          simpa [givensQRStageTaskList] using ht
        rcases hmem with hprev | hstage
        · exact Nat.lt_trans (ih.mp hprev) (Nat.lt_succ_self s)
        · have hstage_eq : t.stage = s :=
            (mem_givensQRStageTasks_iff t).mp hstage
          rw [hstage_eq]
          exact Nat.lt_succ_self s
      · intro hlt
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hprev | hstage
        · have hprev_mem : t ∈ givensQRStageTaskList m cols s :=
            ih.mpr hprev
          simp [givensQRStageTaskList, hprev_mem]
        · have hstage_mem : t ∈ givensQRStageTasks m cols s :=
            (mem_givensQRStageTasks_iff t).mpr hstage
          simp [givensQRStageTaskList, hstage_mem]

/-- The flattened complete QR schedule produces the same upper-trapezoidal
    output as the stage fold. -/
theorem fl_givensQRStageTaskList_upper_trapezoidal
    (fp : FPModel) (m cols : Nat)
    (B : Fin m -> Fin cols -> Real) :
    IsUpperTrapezoidal m cols
      (fl_givensQRTaskList fp m cols
        (givensQRStageTaskList m cols (givensQRStageCount m cols)) B) := by
  rw [← fl_givensQRStageFold_eq_taskList fp m cols B
    (givensQRStageCount m cols)]
  exact fl_givensQRStageFold_upper_trapezoidal fp m cols B

theorem fl_givensQRTaskStepOfTask_prev_col (fp : FPModel) (m cols : Nat)
    (t : GivensQRTask m cols) (B : Fin m -> Fin cols -> Real)
    (i : Fin m) (j : Fin cols) (hj : j.val < t.col.val) :
    fl_givensQRTaskStepOfTask fp m cols t B i j = B i j :=
  fl_givensQRTaskStep_prev_col fp m cols t.pivot t.row t.col j B i hj

@[simp] theorem fl_givensQRTaskStepOfTask_target (fp : FPModel)
    (m cols : Nat) (t : GivensQRTask m cols)
    (B : Fin m -> Fin cols -> Real) :
    fl_givensQRTaskStepOfTask fp m cols t B t.row t.col = 0 := by
  simp [fl_givensQRTaskStepOfTask]

-- ============================================================
-- §18.5  Lemma 18.8: Sequence of Givens rotations backward error
-- ============================================================

/-- **Backward error from a sequence of perturbed Givens rotations**
    (Lemma 18.8, normwise form).

    Given r Givens rotations G₁,...,Gᵣ, if each computed application
    satisfies ‖ΔGₖ‖_F ≤ c, then the product
    (Gᵣ + ΔGᵣ)···(G₁ + ΔG₁)A = Qᵀ(A + ΔA)
    where Q is orthogonal and ‖ΔA‖_F ≤ r·c·‖A‖_F.

    This is an instance of OrthogonalSequenceBackwardError since
    Givens rotations are orthogonal matrices and the accumulation
    mechanism is identical to Lemma 18.3 for Householder. -/
abbrev GivensSequenceBackwardError (n : ℕ) (A : Fin n → Fin n → ℝ)
    (A_hat : Fin n → Fin n → ℝ) (r : ℕ) (c : ℝ) :=
  OrthogonalSequenceBackwardError n A A_hat r c

-- ============================================================
-- §18.5  Theorem 18.9: Givens QR backward error
-- ============================================================

/-- **Theorem 18.9**: Givens QR factorization backward error (normwise).

    The computed R̂ from Givens QR satisfies A + ΔA = Q·R̂
    where Q is orthogonal and ‖ΔA‖_F ≤ c_bound.

    For an n×n matrix, r = n(n-1)/2 Givens rotations are used,
    each with per-step error ≤ √2·γ₆. The total bound is
    c_bound = r · √2·γ₆ · ‖A‖_F. -/
structure GivensQRBackwardError (n : ℕ) (A R_hat : Fin n → Fin n → ℝ)
    (c_bound : ℝ) : Prop where
  /-- There exists an orthogonal Q such that A + ΔA = Q·R̂ with bounded ΔA. -/
  result : ∃ (Q : Fin n → Fin n → ℝ) (ΔA : Fin n → Fin n → ℝ),
    IsOrthogonal n Q ∧
    (∀ i j, matMul n Q R_hat i j = A i j + ΔA i j) ∧
    frobNorm ΔA ≤ c_bound

/-- Theorem 18.9 instantiation: r Givens rotations with per-step error ≤ c
    yield total backward error ≤ r · c · ‖A‖_F.

    The proof is identical to Theorem 18.4 since both use the same
    orthogonal sequence backward error structure (Lemma 18.3/18.8). -/
theorem givens_qr_backward (n : ℕ) (r : ℕ) (_hr : 0 < r)
    (A R_hat : Fin n → Fin n → ℝ) (c : ℝ) (_hc : 0 ≤ c)
    (hSeq : GivensSequenceBackwardError n A R_hat r c) :
    GivensQRBackwardError n A R_hat
      (↑r * c * frobNorm A) := by
  obtain ⟨Q, ΔA, hQ, hAhat, hbound⟩ := hSeq.result
  exact ⟨⟨Q, ΔA, hQ, by
    intro i j
    have hR : R_hat = matMul n (matTranspose Q) (fun a b => A a b + ΔA a b) :=
      funext fun k => funext fun l => hAhat k l
    have hQQT : matMul n Q (matTranspose Q) = idMatrix n :=
      funext fun a => funext fun b => hQ.right_inv a b
    rw [hR, ← matMul_assoc, hQQT, matMul_id_left], hbound⟩⟩

/-- Repeated concrete computed-coefficient Givens matrix applications.

    This theorem is the implementation-backed sequence bridge below the full
    Givens QR loop.  It does not choose the QR annihilation schedule.  Instead,
    it assumes a concrete matrix sequence whose step `k` is exactly
    `fl_givensApplyMatrix` with the supplied row pair and two-vector used to
    construct the rotation coefficients.  Each step is proved from the concrete
    `fl_givensC`/`fl_givensS`/`fl_givensApply` kernels, then accumulated by the
    generic residual-form orthogonal sequence theorem. -/
theorem fl_givens_sequence_backward_error (fp : FPModel) {n r : ℕ}
    (Aseq : ℕ → Fin n → Fin n → ℝ)
    (pseq qseq : ℕ → Fin n)
    (xiseq xjseq : ℕ → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hpq : ∀ k : ℕ, k < r → pseq k ≠ qseq k)
    (hnz : ∀ k : ℕ, k < r → xiseq k ^ 2 + xjseq k ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8)
    (hstep_bound : ∀ k : ℕ, k < r →
      gamma fp 8 *
        frobNorm (givensRotation n (pseq k) (qseq k)
          (givensC (xiseq k) (xjseq k))
          (givensS (xiseq k) (xjseq k))) ≤ c)
    (hAstep : ∀ k : ℕ, k < r →
      Aseq (k + 1) =
        fl_givensApplyMatrix fp n (pseq k) (qseq k)
          (xiseq k) (xjseq k) (Aseq k)) :
    ∃ (Q : Fin n → Fin n → ℝ) (ΔA : Fin n → Fin n → ℝ),
      IsOrthogonal n Q ∧
      (∀ i j : Fin n, Aseq r i j =
        matMul n (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤ residualAccumBound c r * frobNorm (Aseq 0) := by
  let Pseq : ℕ → Fin n → Fin n → ℝ := fun k =>
    givensRotation n (pseq k) (qseq k)
      (givensC (xiseq k) (xjseq k))
      (givensS (xiseq k) (xjseq k))
  apply residual_orthogonal_sequence_backward_error n r Aseq Pseq c hc
  · intro k hk
    exact givensRotation_constructed_orthogonal n (pseq k) (qseq k)
      (xiseq k) (xjseq k) (hpq k hk) (hnz k hk)
  · intro k hk
    have hraw :=
      fl_givensApply_computed_matrix_step_error fp n (pseq k) (qseq k)
        (xiseq k) (xjseq k) (Aseq k) (hpq k hk) (hnz k hk) hvalid
    have hcstep : 0 ≤
        gamma fp 8 *
          frobNorm (givensRotation n (pseq k) (qseq k)
            (givensC (xiseq k) (xjseq k))
            (givensS (xiseq k) (xjseq k))) := by
      exact mul_nonneg (gamma_nonneg fp hvalid) (frobNorm_nonneg _)
    obtain ⟨E, hNext, hE⟩ := hraw.exists_residual_matrix_bound hcstep
    refine ⟨E, ?_, ?_⟩
    · intro i j
      rw [hAstep k hk]
      simpa [Pseq] using hNext i j
    · exact le_trans hE
        (mul_le_mul_of_nonneg_right (hstep_bound k hk)
          (frobNorm_nonneg (Aseq k)))

/-- Uniform-bound corollary for repeated computed Givens matrix applications.

    Since every exact Givens rotation is orthogonal, its Frobenius norm is
    `sqrt n`.  This removes the explicit per-step bound assumption from
    `fl_givens_sequence_backward_error`, while keeping the conservative
    `gamma fp 8` constant inherited from the computed-coefficient bridge. -/
theorem fl_givens_sequence_backward_error_uniform (fp : FPModel) {n r : ℕ}
    (Aseq : ℕ → Fin n → Fin n → ℝ)
    (pseq qseq : ℕ → Fin n)
    (xiseq xjseq : ℕ → ℝ)
    (hpq : ∀ k : ℕ, k < r → pseq k ≠ qseq k)
    (hnz : ∀ k : ℕ, k < r → xiseq k ^ 2 + xjseq k ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8)
    (hAstep : ∀ k : ℕ, k < r →
      Aseq (k + 1) =
        fl_givensApplyMatrix fp n (pseq k) (qseq k)
          (xiseq k) (xjseq k) (Aseq k)) :
    ∃ (Q : Fin n → Fin n → ℝ) (ΔA : Fin n → Fin n → ℝ),
      IsOrthogonal n Q ∧
      (∀ i j : Fin n, Aseq r i j =
        matMul n (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤
        residualAccumBound (gamma fp 8 * Real.sqrt (n : ℝ)) r *
          frobNorm (Aseq 0) := by
  apply fl_givens_sequence_backward_error fp Aseq pseq qseq xiseq xjseq
    (gamma fp 8 * Real.sqrt (n : ℝ))
  · exact mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg _)
  · exact hpq
  · exact hnz
  · exact hvalid
  · intro k hk
    have hG :=
      givensRotation_constructed_orthogonal n (pseq k) (qseq k)
        (xiseq k) (xjseq k) (hpq k hk) (hnz k hk)
    rw [hG.frobNorm_eq_sqrt_card]
  · exact hAstep

/-- Uniform-bound sequence theorem for concrete Givens column steps.

    Compared with `fl_givens_sequence_backward_error_uniform`, this theorem
    obtains each rotation's two-vector from the current matrix column
    `(Aseq k (pseq k) (colseq k), Aseq k (qseq k) (colseq k))`.  This is one
    layer closer to a full Givens QR loop; the remaining missing piece is the
    actual annihilation schedule and triangular-shape proof. -/
theorem fl_givens_column_sequence_backward_error_uniform (fp : FPModel)
    {n r : ℕ}
    (Aseq : ℕ → Fin n → Fin n → ℝ)
    (pseq qseq colseq : ℕ → Fin n)
    (hpq : ∀ k : ℕ, k < r → pseq k ≠ qseq k)
    (hnz : ∀ k : ℕ, k < r →
      Aseq k (pseq k) (colseq k) ^ 2 +
        Aseq k (qseq k) (colseq k) ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8)
    (hAstep : ∀ k : ℕ, k < r →
      Aseq (k + 1) =
        fl_givensColumnStepMatrix fp n (pseq k) (qseq k)
          (colseq k) (Aseq k)) :
    ∃ (Q : Fin n → Fin n → ℝ) (ΔA : Fin n → Fin n → ℝ),
      IsOrthogonal n Q ∧
      (∀ i j : Fin n, Aseq r i j =
        matMul n (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤
        residualAccumBound (gamma fp 8 * Real.sqrt (n : ℝ)) r *
          frobNorm (Aseq 0) := by
  apply fl_givens_sequence_backward_error_uniform fp Aseq pseq qseq
    (fun k => Aseq k (pseq k) (colseq k))
    (fun k => Aseq k (qseq k) (colseq k)) hpq hnz hvalid
  intro k hk
  simpa [fl_givensColumnStepMatrix] using hAstep k hk

/-- Rectangular-panel version of `fl_givens_sequence_backward_error`. -/
theorem fl_givens_panel_sequence_backward_error (fp : FPModel)
    {m cols r : ℕ}
    (Aseq : ℕ → Fin m → Fin cols → ℝ)
    (pseq qseq : ℕ → Fin m)
    (xiseq xjseq : ℕ → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hpq : ∀ k : ℕ, k < r → pseq k ≠ qseq k)
    (hnz : ∀ k : ℕ, k < r → xiseq k ^ 2 + xjseq k ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8)
    (hstep_bound : ∀ k : ℕ, k < r →
      gamma fp 8 *
        frobNorm (givensRotation m (pseq k) (qseq k)
          (givensC (xiseq k) (xjseq k))
          (givensS (xiseq k) (xjseq k))) ≤ c)
    (hAstep : ∀ k : ℕ, k < r →
      Aseq (k + 1) =
        fl_givensApplyMatrixRect fp m cols (pseq k) (qseq k)
          (xiseq k) (xjseq k) (Aseq k)) :
    ∃ (Q : Fin m → Fin m → ℝ) (ΔA : Fin m → Fin cols → ℝ),
      IsOrthogonal m Q ∧
      (∀ (i : Fin m) (j : Fin cols), Aseq r i j =
        matMulRect m m cols (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤ residualAccumBound c r * frobNorm (Aseq 0) := by
  let Pseq : ℕ → Fin m → Fin m → ℝ := fun k =>
    givensRotation m (pseq k) (qseq k)
      (givensC (xiseq k) (xjseq k))
      (givensS (xiseq k) (xjseq k))
  apply residual_orthogonal_sequence_backward_error_rect m cols r Aseq Pseq c hc
  · intro k hk
    exact givensRotation_constructed_orthogonal m (pseq k) (qseq k)
      (xiseq k) (xjseq k) (hpq k hk) (hnz k hk)
  · intro k hk
    have hraw :=
      fl_givensApply_computed_matrix_step_error_rect fp m cols
        (pseq k) (qseq k) (xiseq k) (xjseq k) (Aseq k)
        (hpq k hk) (hnz k hk) hvalid
    have hcstep : 0 ≤
        gamma fp 8 *
          frobNorm (givensRotation m (pseq k) (qseq k)
            (givensC (xiseq k) (xjseq k))
            (givensS (xiseq k) (xjseq k))) := by
      exact mul_nonneg (gamma_nonneg fp hvalid) (frobNorm_nonneg _)
    obtain ⟨E, hNext, hE⟩ := hraw.exists_residual_matrix_bound hcstep
    refine ⟨E, ?_, ?_⟩
    · intro i j
      rw [hAstep k hk]
      simpa [Pseq] using hNext i j
    · exact le_trans hE
        (mul_le_mul_of_nonneg_right (hstep_bound k hk)
          (frobNorm_nonneg (Aseq k)))

/-- Uniform-bound rectangular-panel corollary for repeated computed Givens
    applications. -/
theorem fl_givens_panel_sequence_backward_error_uniform (fp : FPModel)
    {m cols r : ℕ}
    (Aseq : ℕ → Fin m → Fin cols → ℝ)
    (pseq qseq : ℕ → Fin m)
    (xiseq xjseq : ℕ → ℝ)
    (hpq : ∀ k : ℕ, k < r → pseq k ≠ qseq k)
    (hnz : ∀ k : ℕ, k < r → xiseq k ^ 2 + xjseq k ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8)
    (hAstep : ∀ k : ℕ, k < r →
      Aseq (k + 1) =
        fl_givensApplyMatrixRect fp m cols (pseq k) (qseq k)
          (xiseq k) (xjseq k) (Aseq k)) :
    ∃ (Q : Fin m → Fin m → ℝ) (ΔA : Fin m → Fin cols → ℝ),
      IsOrthogonal m Q ∧
      (∀ (i : Fin m) (j : Fin cols), Aseq r i j =
        matMulRect m m cols (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤
        residualAccumBound (gamma fp 8 * Real.sqrt (m : ℝ)) r *
          frobNorm (Aseq 0) := by
  apply fl_givens_panel_sequence_backward_error fp Aseq pseq qseq xiseq xjseq
    (gamma fp 8 * Real.sqrt (m : ℝ))
  · exact mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg _)
  · exact hpq
  · exact hnz
  · exact hvalid
  · intro k hk
    have hG :=
      givensRotation_constructed_orthogonal m (pseq k) (qseq k)
        (xiseq k) (xjseq k) (hpq k hk) (hnz k hk)
    rw [hG.frobNorm_eq_sqrt_card]
  · exact hAstep

/-- Uniform-bound rectangular-panel sequence theorem for concrete Givens
    column steps. -/
theorem fl_givens_column_panel_sequence_backward_error_uniform (fp : FPModel)
    {m cols r : ℕ}
    (Aseq : ℕ → Fin m → Fin cols → ℝ)
    (pseq qseq : ℕ → Fin m)
    (colseq : ℕ → Fin cols)
    (hpq : ∀ k : ℕ, k < r → pseq k ≠ qseq k)
    (hnz : ∀ k : ℕ, k < r →
      Aseq k (pseq k) (colseq k) ^ 2 +
        Aseq k (qseq k) (colseq k) ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8)
    (hAstep : ∀ k : ℕ, k < r →
      Aseq (k + 1) =
        fl_givensColumnStepMatrixRect fp m cols (pseq k) (qseq k)
          (colseq k) (Aseq k)) :
    ∃ (Q : Fin m → Fin m → ℝ) (ΔA : Fin m → Fin cols → ℝ),
      IsOrthogonal m Q ∧
      (∀ (i : Fin m) (j : Fin cols), Aseq r i j =
        matMulRect m m cols (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤
        residualAccumBound (gamma fp 8 * Real.sqrt (m : ℝ)) r *
          frobNorm (Aseq 0) := by
  apply fl_givens_panel_sequence_backward_error_uniform fp Aseq pseq qseq
    (fun k => Aseq k (pseq k) (colseq k))
    (fun k => Aseq k (qseq k) (colseq k)) hpq hnz hvalid
  intro k hk
  simpa [fl_givensColumnStepMatrixRect] using hAstep k hk

end NumStability
