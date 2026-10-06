-- Canonical matrix-level executor bridge for Higham Theorem 19.10.
--
-- `Higham19Lemma9DisjointSweep` proves the sharp dimension-independent
-- per-stage estimate for a simultaneous column sweep.  This module proves that
-- the repository's sequential anti-diagonal `fl_givensQRStageFold` has exactly
-- that disjoint structure, including its previous-column copies, inactive
-- targets, and explicitly stored target zeros.  It then accumulates the sharp
-- stage bound and packages the literal computed R factor with Q and DeltaA.

import NumStability.Algorithms.QR.Higham19Lemma9DisjointSweep
import NumStability.Algorithms.QR.Higham19

namespace NumStability.Wave13

open scoped BigOperators Matrix.Norms.Frobenius
open NumStability

noncomputable def givensQRFixedExactTaskStep (m cols : Nat)
    (t : GivensQRTask m cols) (B X : Fin m -> Fin cols -> Real) :
    Fin m -> Fin cols -> Real :=
  matMulRect m m cols (givensQRTaskRotation m cols t B) X

noncomputable def givensQRFixedExactTaskList (m cols : Nat)
    (tasks : List (GivensQRTask m cols))
    (B X : Fin m -> Fin cols -> Real) : Fin m -> Fin cols -> Real :=
  match tasks with
  | [] => X
  | t :: ts =>
      givensQRFixedExactTaskList m cols ts B
        (givensQRFixedExactTaskStep m cols t B X)

noncomputable def givensQRFixedExactTaskProduct (m cols : Nat)
    (tasks : List (GivensQRTask m cols))
    (B : Fin m -> Fin cols -> Real) : Fin m -> Fin m -> Real :=
  match tasks with
  | [] => idMatrix m
  | t :: ts =>
      matMul m (givensQRFixedExactTaskProduct m cols ts B)
        (givensQRTaskRotation m cols t B)

theorem givensQRFixedExactTaskProduct_orthogonal (m cols : Nat)
    (tasks : List (GivensQRTask m cols))
    (B : Fin m -> Fin cols -> Real) :
    IsOrthogonal m (givensQRFixedExactTaskProduct m cols tasks B) := by
  induction tasks with
  | nil => simpa [givensQRFixedExactTaskProduct] using idMatrix_orthogonal m
  | cons t ts ih =>
      simpa [givensQRFixedExactTaskProduct] using
        ih.mul (givensQRTaskRotation_orthogonal m cols t B)

theorem givensQRFixedExactTaskList_eq_product (m cols : Nat)
    (tasks : List (GivensQRTask m cols))
    (B X : Fin m -> Fin cols -> Real) :
    givensQRFixedExactTaskList m cols tasks B X =
      matMulRect m m cols (givensQRFixedExactTaskProduct m cols tasks B) X := by
  induction tasks generalizing X with
  | nil => simp [givensQRFixedExactTaskList, givensQRFixedExactTaskProduct,
      matMulRect_id_left]
  | cons t ts ih =>
      rw [givensQRFixedExactTaskList, ih]
      simp only [givensQRFixedExactTaskStep, givensQRFixedExactTaskProduct]
      rw [matMulRect_assoc_square_left]

theorem fl_givensQRTaskStepOfTask_other_row (fp : FPModel)
    (m cols : Nat) (t : GivensQRTask m cols)
    (B : Fin m -> Fin cols -> Real) (i : Fin m)
    (hip : i ≠ t.pivot) (hiq : i ≠ t.row) :
    forall j, fl_givensQRTaskStepOfTask fp m cols t B i j = B i j := by
  intro j
  unfold fl_givensQRTaskStepOfTask fl_givensQRTaskStep
  by_cases hzero : B t.row t.col = 0
  · simp [hzero]
  · rw [if_neg hzero]
    by_cases hj : j.val < t.col.val
    · simp [hj]
    · rw [if_neg hj, if_neg hiq]
      unfold fl_givensApplyMatrixRect
      exact fl_givensApply_other fp m t.pivot t.row i _ _ _ hip hiq

theorem givensQRFixedExactTaskStep_other_row (m cols : Nat)
    (t : GivensQRTask m cols)
    (B X : Fin m -> Fin cols -> Real) (i : Fin m)
    (hip : i ≠ t.pivot) (hiq : i ≠ t.row) :
    forall j, givensQRFixedExactTaskStep m cols t B X i j = X i j := by
  intro j
  unfold givensQRFixedExactTaskStep givensQRTaskRotation matMulRect
  by_cases hzero : B t.row t.col = 0
  · simp [hzero, idMatrix]
  · rw [if_neg hzero]
    exact givensRotation_matMulVec_other m t.pivot t.row i _ _ _ hip hiq

theorem fl_givensQRTaskList_other_row (fp : FPModel)
    (m cols : Nat) (tasks : List (GivensQRTask m cols))
    (B : Fin m -> Fin cols -> Real) (i : Fin m)
    (hi : forall t, t ∈ tasks -> i ≠ t.pivot ∧ i ≠ t.row) :
    forall j, fl_givensQRTaskList fp m cols tasks B i j = B i j := by
  induction tasks generalizing B with
  | nil => simp [fl_givensQRTaskList]
  | cons t ts ih =>
      intro j
      have hit := hi t (by simp)
      have hits : forall u, u ∈ ts -> i ≠ u.pivot ∧ i ≠ u.row := by
        intro u hu
        exact hi u (by simp [hu])
      rw [fl_givensQRTaskList]
      rw [ih (B := fl_givensQRTaskStepOfTask fp m cols t B) hits]
      exact fl_givensQRTaskStepOfTask_other_row fp m cols t B i hit.1 hit.2 j

theorem givensQRFixedExactTaskList_other_row (m cols : Nat)
    (tasks : List (GivensQRTask m cols))
    (B X : Fin m -> Fin cols -> Real) (i : Fin m)
    (hi : forall t, t ∈ tasks -> i ≠ t.pivot ∧ i ≠ t.row) :
    forall j, givensQRFixedExactTaskList m cols tasks B X i j = X i j := by
  induction tasks generalizing X with
  | nil => simp [givensQRFixedExactTaskList]
  | cons t ts ih =>
      intro j
      have hit := hi t (by simp)
      have hits : forall u, u ∈ ts -> i ≠ u.pivot ∧ i ≠ u.row := by
        intro u hu
        exact hi u (by simp [hu])
      rw [givensQRFixedExactTaskList]
      rw [ih (X := givensQRFixedExactTaskStep m cols t B X) hits]
      exact givensQRFixedExactTaskStep_other_row m cols t B X i hit.1 hit.2 j

theorem fl_givensQRTaskStepOfTask_pair_congr (fp : FPModel)
    (m cols : Nat) (t : GivensQRTask m cols)
    (X Y : Fin m -> Fin cols -> Real)
    (hp : forall j, X t.pivot j = Y t.pivot j)
    (hq : forall j, X t.row j = Y t.row j) :
    (forall j,
      fl_givensQRTaskStepOfTask fp m cols t X t.pivot j =
        fl_givensQRTaskStepOfTask fp m cols t Y t.pivot j) ∧
    (forall j,
      fl_givensQRTaskStepOfTask fp m cols t X t.row j =
        fl_givensQRTaskStepOfTask fp m cols t Y t.row j) := by
  have hpcol := hp t.col
  have hqcol := hq t.col
  constructor
  · intro j
    unfold fl_givensQRTaskStepOfTask fl_givensQRTaskStep
    by_cases hzero : X t.row t.col = 0
    · have hzeroY : Y t.row t.col = 0 := by rw [← hqcol]; exact hzero
      simp [hzero, hzeroY, hp j]
    · have hzeroY : Y t.row t.col ≠ 0 := by rwa [← hqcol]
      rw [if_neg hzero, if_neg hzeroY]
      by_cases hj : j.val < t.col.val
      · simp [hj, hp j]
      · rw [if_neg hj, if_neg hj]
        have hpne : t.pivot ≠ t.row := t.pivot_ne_row
        simp only [if_neg hpne]
        unfold fl_givensApplyMatrixRect
        simp [hp, hq]
  · intro j
    unfold fl_givensQRTaskStepOfTask fl_givensQRTaskStep
    by_cases hzero : X t.row t.col = 0
    · have hzeroY : Y t.row t.col = 0 := by rw [← hqcol]; exact hzero
      simp [hzero, hzeroY, hq j]
    · have hzeroY : Y t.row t.col ≠ 0 := by rwa [← hqcol]
      rw [if_neg hzero, if_neg hzeroY]
      by_cases hj : j.val < t.col.val
      · simp [hj, hq j]
      · rw [if_neg hj, if_neg hj]
        by_cases hjcol : j = t.col
        · simp [hjcol]
        · rw [if_neg hjcol, if_neg hjcol]
          unfold fl_givensApplyMatrixRect
          simp [fl_givensApply_q, t.pivot_ne_row, hp, hq]

theorem givensQRFixedExactTaskStep_pair_congr (m cols : Nat)
    (t : GivensQRTask m cols)
    (B X Y : Fin m -> Fin cols -> Real)
    (hp : forall j, X t.pivot j = Y t.pivot j)
    (hq : forall j, X t.row j = Y t.row j) :
    (forall j,
      givensQRFixedExactTaskStep m cols t B X t.pivot j =
        givensQRFixedExactTaskStep m cols t B Y t.pivot j) ∧
    (forall j,
      givensQRFixedExactTaskStep m cols t B X t.row j =
        givensQRFixedExactTaskStep m cols t B Y t.row j) := by
  constructor
  · intro j
    unfold givensQRFixedExactTaskStep
    by_cases hzero : B t.row t.col = 0
    · simp [givensQRTaskRotation, hzero, matMulRect_id_left, hp j]
    · simp only [givensQRTaskRotation, if_neg hzero]
      change matMulVec m _ (fun k => X k j) t.pivot =
        matMulVec m _ (fun k => Y k j) t.pivot
      rw [givensRotation_matMulVec_p m t.pivot t.row _ _ _ t.pivot_ne_row]
      rw [givensRotation_matMulVec_p m t.pivot t.row _ _ _ t.pivot_ne_row]
      rw [hp j, hq j]
  · intro j
    unfold givensQRFixedExactTaskStep
    by_cases hzero : B t.row t.col = 0
    · simp [givensQRTaskRotation, hzero, matMulRect_id_left, hq j]
    · simp only [givensQRTaskRotation, if_neg hzero]
      change matMulVec m _ (fun k => X k j) t.row =
        matMulVec m _ (fun k => Y k j) t.row
      rw [givensRotation_matMulVec_q m t.pivot t.row _ _ _ t.pivot_ne_row]
      rw [givensRotation_matMulVec_q m t.pivot t.row _ _ _ t.pivot_ne_row]
      rw [hp j, hq j]

theorem fl_givensQRTaskStepOfTask_pair_sq_residual_le_gamma6
    (fp : FPModel) (m cols : Nat) (t : GivensQRTask m cols)
    (B : Fin m -> Fin cols -> Real)
    (hzero : ZeroedThrough t.stage B) (hvalid : gammaValid fp 6) :
    forall j,
      (fl_givensQRTaskStepOfTask fp m cols t B t.pivot j -
          givensQRFixedExactTaskStep m cols t B B t.pivot j) ^ 2 +
        (fl_givensQRTaskStepOfTask fp m cols t B t.row j -
          givensQRFixedExactTaskStep m cols t B B t.row j) ^ 2 <=
        2 * gamma fp 6 ^ 2 *
          (B t.pivot j ^ 2 + B t.row j ^ 2) := by
  intro j
  by_cases hactive : B t.row t.col = 0
  · have hact : fl_givensQRTaskStepOfTask fp m cols t B = B := by
      simp [fl_givensQRTaskStepOfTask, fl_givensQRTaskStep, hactive]
    have hexact : givensQRFixedExactTaskStep m cols t B B = B := by
      simp [givensQRFixedExactTaskStep, givensQRTaskRotation, hactive,
        matMulRect_id_left]
    rw [hact, hexact]
    nlinarith [sq_nonneg (gamma fp 6), sq_nonneg (B t.pivot j),
      sq_nonneg (B t.row j)]
  · have hnz : B t.pivot t.col ^ 2 + B t.row t.col ^ 2 ≠ 0 := by
      intro hsum
      have hq0 : B t.row t.col ^ 2 = 0 := by
        nlinarith [sq_nonneg (B t.pivot t.col), sq_nonneg (B t.row t.col)]
      exact hactive (sq_eq_zero_iff.mp hq0)
    have hexact_p : givensQRFixedExactTaskStep m cols t B B t.pivot j =
        givensC (B t.pivot t.col) (B t.row t.col) * B t.pivot j +
          givensS (B t.pivot t.col) (B t.row t.col) * B t.row j := by
      unfold givensQRFixedExactTaskStep
      simp only [givensQRTaskRotation, if_neg hactive]
      change matMulVec m _ (fun k => B k j) t.pivot = _
      exact givensRotation_matMulVec_p m t.pivot t.row _ _ _ t.pivot_ne_row
    have hexact_q : givensQRFixedExactTaskStep m cols t B B t.row j =
        givensC (B t.pivot t.col) (B t.row t.col) * B t.row j -
          givensS (B t.pivot t.col) (B t.row t.col) * B t.pivot j := by
      unfold givensQRFixedExactTaskStep
      simp only [givensQRTaskRotation, if_neg hactive]
      change matMulVec m _ (fun k => B k j) t.row = _
      exact givensRotation_matMulVec_q m t.pivot t.row _ _ _ t.pivot_ne_row
    have hfull := fl_givensApply_computed_pair_sq_error_le_gamma6
      fp m t.pivot t.row (B t.pivot t.col) (B t.row t.col)
        (fun i => B i j) t.pivot_ne_row hnz hvalid
    by_cases hjprev : j.val < t.col.val
    · obtain ⟨hp0, hq0⟩ :=
        ZeroedThrough.prev_pair_zero_of_task t hzero j hjprev
      have hactp := fl_givensQRTaskStep_prev_col fp m cols t.pivot t.row
        t.col j B t.pivot hjprev
      have hactq := fl_givensQRTaskStep_prev_col fp m cols t.pivot t.row
        t.col j B t.row hjprev
      rw [show fl_givensQRTaskStepOfTask fp m cols t B t.pivot j =
          B t.pivot j from hactp,
        show fl_givensQRTaskStepOfTask fp m cols t B t.row j =
          B t.row j from hactq,
        hexact_p, hexact_q, hp0, hq0]
      nlinarith [sq_nonneg (gamma fp 6)]
    · by_cases hjcol : j = t.col
      · subst j
        have hactp : fl_givensQRTaskStepOfTask fp m cols t B t.pivot t.col =
            fl_givensApply fp m t.pivot t.row
              (fl_givensC fp (B t.pivot t.col) (B t.row t.col))
              (fl_givensS fp (B t.pivot t.col) (B t.row t.col))
              (fun i => B i t.col) t.pivot := by
          unfold fl_givensQRTaskStepOfTask
          rw [fl_givensQRTaskStep_active_ne_target fp m cols t.pivot t.row
            t.col t.col B t.pivot hactive (by omega)
              (Or.inl t.pivot_ne_row)]
          rfl
        have hactq : fl_givensQRTaskStepOfTask fp m cols t B t.row t.col = 0 := by
          exact fl_givensQRTaskStep_target fp m cols t.pivot t.row t.col B
        have hexactq0 : givensQRFixedExactTaskStep m cols t B B t.row t.col = 0 := by
          unfold givensQRFixedExactTaskStep
          simp only [givensQRTaskRotation, if_neg hactive]
          exact givensRotation_constructed_matMulRect_target_zero
            m cols t.pivot t.row t.col B t.pivot_ne_row
        rw [hactp, hactq, hexact_p, hexactq0]
        have hnonneg : 0 <=
            (fl_givensApply fp m t.pivot t.row
              (fl_givensC fp (B t.pivot t.col) (B t.row t.col))
              (fl_givensS fp (B t.pivot t.col) (B t.row t.col))
              (fun i => B i t.col) t.row -
                (givensC (B t.pivot t.col) (B t.row t.col) * B t.row t.col -
                  givensS (B t.pivot t.col) (B t.row t.col) *
                    B t.pivot t.col)) ^ 2 := sq_nonneg _
        nlinarith
      · have hactp : fl_givensQRTaskStepOfTask fp m cols t B t.pivot j =
            fl_givensApply fp m t.pivot t.row
              (fl_givensC fp (B t.pivot t.col) (B t.row t.col))
              (fl_givensS fp (B t.pivot t.col) (B t.row t.col))
              (fun i => B i j) t.pivot := by
          unfold fl_givensQRTaskStepOfTask
          rw [fl_givensQRTaskStep_active_ne_target fp m cols t.pivot t.row
            t.col j B t.pivot hactive hjprev (Or.inl t.pivot_ne_row)]
          rfl
        have hactq : fl_givensQRTaskStepOfTask fp m cols t B t.row j =
            fl_givensApply fp m t.pivot t.row
              (fl_givensC fp (B t.pivot t.col) (B t.row t.col))
              (fl_givensS fp (B t.pivot t.col) (B t.row t.col))
              (fun i => B i j) t.row := by
          unfold fl_givensQRTaskStepOfTask
          rw [fl_givensQRTaskStep_active_ne_target fp m cols t.pivot t.row
            t.col j B t.row hactive hjprev (Or.inr hjcol)]
          rfl
        rw [hactp, hactq, hexact_p, hexact_q]
        exact hfull

theorem fl_givensQRTaskList_at_member_pair (fp : FPModel)
    (m cols : Nat) (tasks : List (GivensQRTask m cols))
    (B : Fin m -> Fin cols -> Real) (t : GivensQRTask m cols)
    (hnodup : tasks.Nodup)
    (hsame : forall u, u ∈ tasks -> u.stage = t.stage)
    (ht : t ∈ tasks) :
    (forall j, fl_givensQRTaskList fp m cols tasks B t.pivot j =
      fl_givensQRTaskStepOfTask fp m cols t B t.pivot j) ∧
    (forall j, fl_givensQRTaskList fp m cols tasks B t.row j =
      fl_givensQRTaskStepOfTask fp m cols t B t.row j) := by
  induction tasks generalizing B with
  | nil => simp at ht
  | cons u us ih =>
      have hnodup_us : us.Nodup := List.Nodup.of_cons hnodup
      have hnotin : u ∉ us := (List.nodup_cons.mp hnodup).1
      have hu_stage : u.stage = t.stage := hsame u (by simp)
      have husame : forall v, v ∈ us -> v.stage = t.stage := by
        intro v hv
        exact hsame v (by simp [hv])
      rcases (List.mem_cons.mp ht) with htu | htus
      · subst u
        have htail_p : forall v, v ∈ us ->
            t.pivot ≠ v.pivot ∧ t.pivot ≠ v.row := by
          intro v hv
          have hv_stage := husame v hv
          have htv : t ≠ v := by
            intro htv
            subst v
            exact hnotin hv
          have hd := GivensQRTask.same_stage_rowPair_disjoint
            hv_stage.symm htv
          exact ⟨hd.1, hd.2.1⟩
        have htail_q : forall v, v ∈ us ->
            t.row ≠ v.pivot ∧ t.row ≠ v.row := by
          intro v hv
          have hv_stage := husame v hv
          have htv : t ≠ v := by
            intro htv
            subst v
            exact hnotin hv
          have hd := GivensQRTask.same_stage_rowPair_disjoint
            hv_stage.symm htv
          exact ⟨hd.2.2.1, hd.2.2.2⟩
        constructor
        · intro j
          rw [fl_givensQRTaskList]
          exact fl_givensQRTaskList_other_row fp m cols us
            (fl_givensQRTaskStepOfTask fp m cols t B) t.pivot htail_p j
        · intro j
          rw [fl_givensQRTaskList]
          exact fl_givensQRTaskList_other_row fp m cols us
            (fl_givensQRTaskStepOfTask fp m cols t B) t.row htail_q j
      · have htu : t ≠ u := by
          intro htu
          subst t
          exact hnotin htus
        have hdisj := GivensQRTask.same_stage_rowPair_disjoint
          hu_stage.symm htu
        have hp0 : forall j,
            fl_givensQRTaskStepOfTask fp m cols u B t.pivot j = B t.pivot j :=
          fl_givensQRTaskStepOfTask_other_row fp m cols u B t.pivot
            hdisj.1 hdisj.2.1
        have hq0 : forall j,
            fl_givensQRTaskStepOfTask fp m cols u B t.row j = B t.row j :=
          fl_givensQRTaskStepOfTask_other_row fp m cols u B t.row
            hdisj.2.2.1 hdisj.2.2.2
        have hih := ih
          (B := fl_givensQRTaskStepOfTask fp m cols u B)
          hnodup_us husame htus
        have hcongr := fl_givensQRTaskStepOfTask_pair_congr fp m cols t
          (fl_givensQRTaskStepOfTask fp m cols u B) B hp0 hq0
        constructor
        · intro j
          rw [fl_givensQRTaskList]
          exact (hih.1 j).trans (hcongr.1 j)
        · intro j
          rw [fl_givensQRTaskList]
          exact (hih.2 j).trans (hcongr.2 j)

theorem givensQRFixedExactTaskList_at_member_pair (m cols : Nat)
    (tasks : List (GivensQRTask m cols))
    (B X : Fin m -> Fin cols -> Real) (t : GivensQRTask m cols)
    (hnodup : tasks.Nodup)
    (hsame : forall u, u ∈ tasks -> u.stage = t.stage)
    (ht : t ∈ tasks) :
    (forall j, givensQRFixedExactTaskList m cols tasks B X t.pivot j =
      givensQRFixedExactTaskStep m cols t B X t.pivot j) ∧
    (forall j, givensQRFixedExactTaskList m cols tasks B X t.row j =
      givensQRFixedExactTaskStep m cols t B X t.row j) := by
  induction tasks generalizing X with
  | nil => simp at ht
  | cons u us ih =>
      have hnodup_us : us.Nodup := List.Nodup.of_cons hnodup
      have hnotin : u ∉ us := (List.nodup_cons.mp hnodup).1
      have hu_stage : u.stage = t.stage := hsame u (by simp)
      have husame : forall v, v ∈ us -> v.stage = t.stage := by
        intro v hv
        exact hsame v (by simp [hv])
      rcases (List.mem_cons.mp ht) with htu | htus
      · subst u
        have htail_p : forall v, v ∈ us ->
            t.pivot ≠ v.pivot ∧ t.pivot ≠ v.row := by
          intro v hv
          have hv_stage := husame v hv
          have htv : t ≠ v := by
            intro htv
            subst v
            exact hnotin hv
          have hd := GivensQRTask.same_stage_rowPair_disjoint
            hv_stage.symm htv
          exact ⟨hd.1, hd.2.1⟩
        have htail_q : forall v, v ∈ us ->
            t.row ≠ v.pivot ∧ t.row ≠ v.row := by
          intro v hv
          have hv_stage := husame v hv
          have htv : t ≠ v := by
            intro htv
            subst v
            exact hnotin hv
          have hd := GivensQRTask.same_stage_rowPair_disjoint
            hv_stage.symm htv
          exact ⟨hd.2.2.1, hd.2.2.2⟩
        constructor
        · intro j
          rw [givensQRFixedExactTaskList]
          exact givensQRFixedExactTaskList_other_row m cols us B
            (givensQRFixedExactTaskStep m cols t B X) t.pivot htail_p j
        · intro j
          rw [givensQRFixedExactTaskList]
          exact givensQRFixedExactTaskList_other_row m cols us B
            (givensQRFixedExactTaskStep m cols t B X) t.row htail_q j
      · have htu : t ≠ u := by
          intro htu
          subst t
          exact hnotin htus
        have hdisj := GivensQRTask.same_stage_rowPair_disjoint
          hu_stage.symm htu
        have hp0 : forall j,
            givensQRFixedExactTaskStep m cols u B X t.pivot j = X t.pivot j :=
          givensQRFixedExactTaskStep_other_row m cols u B X t.pivot
            hdisj.1 hdisj.2.1
        have hq0 : forall j,
            givensQRFixedExactTaskStep m cols u B X t.row j = X t.row j :=
          givensQRFixedExactTaskStep_other_row m cols u B X t.row
            hdisj.2.2.1 hdisj.2.2.2
        have hih := ih
          (X := givensQRFixedExactTaskStep m cols u B X)
          hnodup_us husame htus
        have hcongr := givensQRFixedExactTaskStep_pair_congr m cols t B
          (givensQRFixedExactTaskStep m cols u B X) X hp0 hq0
        constructor
        · intro j
          rw [givensQRFixedExactTaskList]
          exact (hih.1 j).trans (hcongr.1 j)
        · intro j
          rw [givensQRFixedExactTaskList]
          exact (hih.2 j).trans (hcongr.2 j)

def givensQRTaskPair {m cols : Nat} (t : GivensQRTask m cols) :
    Fin m × Fin m :=
  (t.pivot, t.row)

noncomputable def givensQRStagePairFinset (m cols s : Nat) :
    Finset (Fin m × Fin m) := by
  classical
  exact (givensQRStageTasks m cols s).toFinset.image givensQRTaskPair

theorem givensQRStagePairFinset_disjoint (m cols s : Nat) :
    DisjointPairs (givensQRStagePairFinset m cols s) := by
  classical
  refine { ne_self := ?_, disj := ?_ }
  · intro pq hpq
    unfold givensQRStagePairFinset at hpq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hpq
    exact t.pivot_ne_row
  · intro pq hpq rs hrs hpqrs
    unfold givensQRStagePairFinset at hpq hrs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hpq
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hrs
    have htlist : t ∈ givensQRStageTasks m cols s := by simpa using ht
    have hulist : u ∈ givensQRStageTasks m cols s := by simpa using hu
    have hstage : t.stage = u.stage := by
      rw [givensQRStageTasks_stage t htlist,
        givensQRStageTasks_stage u hulist]
    have htu : t ≠ u := by
      intro htu
      subst u
      exact hpqrs rfl
    obtain ⟨hpp, hpq, hqp, hqq⟩ :=
      GivensQRTask.same_stage_rowPair_disjoint hstage htu
    rw [Finset.disjoint_left]
    intro i hit hiu
    simp only [pairRows, Finset.mem_insert, Finset.mem_singleton] at hit hiu
    rcases hit with rfl | rfl <;> rcases hiu with h | h
    · exact hpp h
    · exact hpq h
    · exact hqp h
    · exact hqq h

theorem mem_givensQRStagePairFinset_iff (m cols s : Nat)
    (pq : Fin m × Fin m) :
    pq ∈ givensQRStagePairFinset m cols s ↔
      ∃ t ∈ givensQRStageTasks m cols s, givensQRTaskPair t = pq := by
  classical
  unfold givensQRStagePairFinset
  simp

noncomputable def givensQRCanonicalStageExact (m cols s : Nat)
    (B : Fin m -> Fin cols -> Real) : Fin m -> Fin cols -> Real :=
  givensQRFixedExactTaskList m cols (givensQRStageTasks m cols s) B B

noncomputable def givensQRCanonicalStageResidual (fp : FPModel)
    (m cols s : Nat) (B : Fin m -> Fin cols -> Real) :
    Fin m -> Fin cols -> Real :=
  fun i j =>
    fl_givensQRTaskList fp m cols (givensQRStageTasks m cols s) B i j -
      givensQRCanonicalStageExact m cols s B i j

theorem givensQRCanonicalStageExact_eq_product (m cols s : Nat)
    (B : Fin m -> Fin cols -> Real) :
    givensQRCanonicalStageExact m cols s B =
      matMulRect m m cols
        (givensQRFixedExactTaskProduct m cols
          (givensQRStageTasks m cols s) B) B := by
  exact givensQRFixedExactTaskList_eq_product m cols
    (givensQRStageTasks m cols s) B B

theorem givensQRCanonicalStageResidual_representation (fp : FPModel)
    (m cols s : Nat) (B : Fin m -> Fin cols -> Real) :
    forall i j,
      fl_givensQRTaskList fp m cols (givensQRStageTasks m cols s) B i j =
        matMulRect m m cols
          (givensQRFixedExactTaskProduct m cols
            (givensQRStageTasks m cols s) B) B i j +
          givensQRCanonicalStageResidual fp m cols s B i j := by
  intro i j
  rw [← givensQRCanonicalStageExact_eq_product]
  unfold givensQRCanonicalStageResidual
  ring

theorem givensQRCanonicalStageResidual_zero_of_not_touched (fp : FPModel)
    (m cols s : Nat) (B : Fin m -> Fin cols -> Real)
    (i : Fin m) (hi : i ∉ touchedRows (givensQRStagePairFinset m cols s)) :
    forall j, givensQRCanonicalStageResidual fp m cols s B i j = 0 := by
  have hrows : forall t, t ∈ givensQRStageTasks m cols s ->
      i ≠ t.pivot ∧ i ≠ t.row := by
    intro t ht
    have hpair : givensQRTaskPair t ∈ givensQRStagePairFinset m cols s :=
      (mem_givensQRStagePairFinset_iff m cols s (givensQRTaskPair t)).2
        ⟨t, ht, rfl⟩
    constructor
    · intro hip
      apply hi
      unfold touchedRows
      exact Finset.mem_biUnion.mpr
        ⟨givensQRTaskPair t, hpair, by simp [pairRows, givensQRTaskPair, hip]⟩
    · intro hiq
      apply hi
      unfold touchedRows
      exact Finset.mem_biUnion.mpr
        ⟨givensQRTaskPair t, hpair, by simp [pairRows, givensQRTaskPair, hiq]⟩
  intro j
  unfold givensQRCanonicalStageResidual givensQRCanonicalStageExact
  rw [fl_givensQRTaskList_other_row fp m cols
    (givensQRStageTasks m cols s) B i hrows j]
  rw [givensQRFixedExactTaskList_other_row m cols
    (givensQRStageTasks m cols s) B B i hrows j]
  ring

theorem givensQRCanonicalStageResidual_at_task_pair (fp : FPModel)
    (m cols s : Nat) (B : Fin m -> Fin cols -> Real)
    (t : GivensQRTask m cols) (ht : t ∈ givensQRStageTasks m cols s) :
    (forall j,
      givensQRCanonicalStageResidual fp m cols s B t.pivot j =
        fl_givensQRTaskStepOfTask fp m cols t B t.pivot j -
          givensQRFixedExactTaskStep m cols t B B t.pivot j) ∧
    (forall j,
      givensQRCanonicalStageResidual fp m cols s B t.row j =
        fl_givensQRTaskStepOfTask fp m cols t B t.row j -
          givensQRFixedExactTaskStep m cols t B B t.row j) := by
  have hsame : forall u, u ∈ givensQRStageTasks m cols s ->
      u.stage = t.stage := by
    intro u hu
    rw [givensQRStageTasks_stage u hu, givensQRStageTasks_stage t ht]
  have hactual := fl_givensQRTaskList_at_member_pair fp m cols
    (givensQRStageTasks m cols s) B t
    (givensQRStageTasks_nodup m cols s) hsame ht
  have hexact := givensQRFixedExactTaskList_at_member_pair m cols
    (givensQRStageTasks m cols s) B B t
    (givensQRStageTasks_nodup m cols s) hsame ht
  constructor
  · intro j
    unfold givensQRCanonicalStageResidual givensQRCanonicalStageExact
    rw [hactual.1 j, hexact.1 j]
  · intro j
    unfold givensQRCanonicalStageResidual givensQRCanonicalStageExact
    rw [hactual.2 j, hexact.2 j]

theorem givensQRCanonicalStageResidual_columnFrob_le_of_local
    (fp : FPModel) (m cols s : Nat)
    (B : Fin m -> Fin cols -> Real) (hvalid : gammaValid fp 6)
    (hlocal : forall (t : GivensQRTask m cols),
      t ∈ givensQRStageTasks m cols s -> forall j,
        (fl_givensQRTaskStepOfTask fp m cols t B t.pivot j -
            givensQRFixedExactTaskStep m cols t B B t.pivot j) ^ 2 +
          (fl_givensQRTaskStepOfTask fp m cols t B t.row j -
            givensQRFixedExactTaskStep m cols t B B t.row j) ^ 2 <=
          2 * gamma fp 6 ^ 2 *
            (B t.pivot j ^ 2 + B t.row j ^ 2)) :
    forall j,
      columnFrob (givensQRCanonicalStageResidual fp m cols s B) j <=
        (Real.sqrt 2 * gamma fp 6) * columnFrob B j := by
  intro j
  let S := givensQRStagePairFinset m cols s
  let w : Fin m -> Real := fun i =>
    givensQRCanonicalStageResidual fp m cols s B i j
  let a : Fin m -> Real := fun i => B i j
  have hS : DisjointPairs S := givensQRStagePairFinset_disjoint m cols s
  have hsupp : forall i : Fin m, i ∉ touchedRows S -> w i = 0 := by
    intro i hi
    exact givensQRCanonicalStageResidual_zero_of_not_touched
      fp m cols s B i hi j
  have hpair : forall pq, pq ∈ S ->
      w pq.1 ^ 2 + w pq.2 ^ 2 <=
        2 * gamma fp 6 ^ 2 * (a pq.1 ^ 2 + a pq.2 ^ 2) := by
    intro pq hpq
    obtain ⟨t, ht, htpair⟩ :=
      (mem_givensQRStagePairFinset_iff m cols s pq).1 hpq
    subst pq
    have hat := givensQRCanonicalStageResidual_at_task_pair
      fp m cols s B t ht
    dsimp [w, a, givensQRTaskPair]
    rw [hat.1 j, hat.2 j]
    exact hlocal t ht j
  have hnorm := stage_columnError_le_sqrt2_gamma S hS w a
    (gamma fp 6) (gamma_nonneg fp hvalid) hsupp hpair
  simpa [w, a, columnFrob_eq_vecNorm2] using hnorm

theorem givensQRCanonicalStageResidual_columnFrob_le_gamma6
    (fp : FPModel) (m cols s : Nat)
    (B : Fin m -> Fin cols -> Real)
    (hzero : ZeroedThrough s B) (hvalid : gammaValid fp 6) :
    forall j,
      columnFrob (givensQRCanonicalStageResidual fp m cols s B) j <=
        (Real.sqrt 2 * gamma fp 6) * columnFrob B j := by
  apply givensQRCanonicalStageResidual_columnFrob_le_of_local
    fp m cols s B hvalid
  intro t ht j
  have htstage : t.stage = s := givensQRStageTasks_stage t ht
  exact fl_givensQRTaskStepOfTask_pair_sq_residual_le_gamma6
    fp m cols t B (by simpa [htstage] using hzero) hvalid j

theorem fl_givensQRStageFold_sequence_columnFrob_backward_error_gamma6_of_local
    (fp : FPModel) (m cols : Nat)
    (A : Fin m -> Fin cols -> Real) (hvalid : gammaValid fp 6)
    (hlocal : forall s, s < givensQRStageCount m cols ->
      forall (t : GivensQRTask m cols),
        t ∈ givensQRStageTasks m cols s -> forall j,
          let B := fl_givensQRStageFold fp m cols s A
          (fl_givensQRTaskStepOfTask fp m cols t B t.pivot j -
              givensQRFixedExactTaskStep m cols t B B t.pivot j) ^ 2 +
            (fl_givensQRTaskStepOfTask fp m cols t B t.row j -
              givensQRFixedExactTaskStep m cols t B B t.row j) ^ 2 <=
            2 * gamma fp 6 ^ 2 *
              (B t.pivot j ^ 2 + B t.row j ^ 2)) :
    exists (Q : Fin m -> Fin m -> Real) (dA : Fin m -> Fin cols -> Real),
      IsOrthogonal m Q ∧
      (forall i j,
        fl_givensQRStageFold fp m cols (givensQRStageCount m cols) A i j =
          matMulRect m m cols (matTranspose Q)
            (fun a b => A a b + dA a b) i j) ∧
      (forall j, columnFrob dA j <=
        gammaTildeDimIndepGamma6 fp m cols * columnFrob A j) := by
  let r := givensQRStageCount m cols
  let Aseq : Nat -> Fin m -> Fin cols -> Real := fun s =>
    fl_givensQRStageFold fp m cols s A
  let Pseq : Nat -> Fin m -> Fin m -> Real := fun s =>
    givensQRFixedExactTaskProduct m cols (givensQRStageTasks m cols s) (Aseq s)
  have hc : 0 <= Real.sqrt 2 * gamma fp 6 :=
    mul_nonneg (Real.sqrt_nonneg _) (gamma_nonneg fp hvalid)
  have hP : forall s, s < r -> IsOrthogonal m (Pseq s) := by
    intro s _hs
    exact givensQRFixedExactTaskProduct_orthogonal m cols
      (givensQRStageTasks m cols s) (Aseq s)
  have hStep : forall s, s < r ->
      exists E : Fin m -> Fin cols -> Real,
        (forall i j, Aseq (s + 1) i j =
          matMulRect m m cols (Pseq s) (Aseq s) i j + E i j) ∧
        (forall j, columnFrob E j <=
          (Real.sqrt 2 * gamma fp 6) * columnFrob (Aseq s) j) := by
    intro s hs
    let E := givensQRCanonicalStageResidual fp m cols s (Aseq s)
    refine ⟨E, ?_, ?_⟩
    · intro i j
      have hrepr := givensQRCanonicalStageResidual_representation
        fp m cols s (Aseq s) i j
      simpa [Aseq, Pseq, E, fl_givensQRStageFold] using hrepr
    · apply givensQRCanonicalStageResidual_columnFrob_le_of_local
        fp m cols s (Aseq s) hvalid
      intro t ht j
      simpa [Aseq] using hlocal s hs t ht j
  obtain ⟨Q, dA, hQ, hrepr, hbound⟩ :=
    residual_orthogonal_sequence_columnFrob_backward_error_rect
      m cols r Aseq Pseq (Real.sqrt 2 * gamma fp 6) hc hP hStep
  refine ⟨Q, dA, hQ, ?_, ?_⟩
  · intro i j
    simpa [r, Aseq] using hrepr i j
  · intro j
    simpa [r, Aseq, gammaTildeDimIndepGamma6] using hbound j

theorem fl_givensQRStageFold_sequence_columnFrob_backward_error_gamma6
    (fp : FPModel) (m cols : Nat)
    (A : Fin m -> Fin cols -> Real) (hvalid : gammaValid fp 6) :
    exists (Q : Fin m -> Fin m -> Real) (dA : Fin m -> Fin cols -> Real),
      IsOrthogonal m Q ∧
      (forall i j,
        fl_givensQRStageFold fp m cols (givensQRStageCount m cols) A i j =
          matMulRect m m cols (matTranspose Q)
            (fun a b => A a b + dA a b) i j) ∧
      (forall j, columnFrob dA j <=
        gammaTildeDimIndepGamma6 fp m cols * columnFrob A j) := by
  apply fl_givensQRStageFold_sequence_columnFrob_backward_error_gamma6_of_local
    fp m cols A hvalid
  intro s _hs t ht j
  let B := fl_givensQRStageFold fp m cols s A
  have htstage : t.stage = s := givensQRStageTasks_stage t ht
  have hzero_s : ZeroedThrough s B := by
    exact fl_givensQRStageFold_zeroedThrough fp m cols A s
  have hzero_t : ZeroedThrough t.stage B := by
    simpa [htstage] using hzero_s
  exact fl_givensQRTaskStepOfTask_pair_sq_residual_le_gamma6
    fp m cols t B hzero_t hvalid j

theorem H19_Theorem19_10_actual_matrix_executor_gamma6_of_local
    (fp : FPModel) (m n : Nat) (A : Fin m -> Fin n -> Real)
    (_hn : 0 < n) (_hnm : n <= m) (hvalid : gammaValid fp 6)
    (hlocal : forall s, s < givensQRStageCount m n ->
      forall (t : GivensQRTask m n),
        t ∈ givensQRStageTasks m n s -> forall j,
          let B := fl_givensQRStageFold fp m n s A
          (fl_givensQRTaskStepOfTask fp m n t B t.pivot j -
              givensQRFixedExactTaskStep m n t B B t.pivot j) ^ 2 +
            (fl_givensQRTaskStepOfTask fp m n t B t.row j -
              givensQRFixedExactTaskStep m n t B B t.row j) ^ 2 <=
            2 * gamma fp 6 ^ 2 *
              (B t.pivot j ^ 2 + B t.row j ^ 2)) :
    exists Q : Fin m -> Fin m -> Real,
      H19.Theorem19_10.GivensQRBackwardError m n A Q
        (fl_givensQRStageFold fp m n (givensQRStageCount m n) A)
        (gammaTildeDimIndepGamma6 fp m n) := by
  obtain ⟨Q, dA, hQ, hrepr, hbound⟩ :=
    fl_givensQRStageFold_sequence_columnFrob_backward_error_gamma6_of_local
      fp m n A hvalid hlocal
  refine ⟨Q, ?_⟩
  refine {
    upper := fl_givensQRStageFold_upper_trapezoidal fp m n A
    orth := hQ
    result := ?_
  }
  refine ⟨dA, ?_, hbound⟩
  intro i j
  let R_hat : Fin m -> Fin n -> Real :=
    fl_givensQRStageFold fp m n (givensQRStageCount m n) A
  have hRmat :
      R_hat = matMulRect m m n (matTranspose Q)
        (fun a b => A a b + dA a b) := by
    ext a b
    exact hrepr a b
  have hQQT : matMul m Q (matTranspose Q) = idMatrix m := by
    ext a b
    exact hQ.right_inv a b
  calc
    A i j + dA i j =
        matMulRect m m n (idMatrix m)
          (fun a b => A a b + dA a b) i j := by
            rw [matMulRect_id_left]
    _ = matMulRect m m n (matMul m Q (matTranspose Q))
          (fun a b => A a b + dA a b) i j := by rw [hQQT]
    _ = matMulRect m m n Q
          (matMulRect m m n (matTranspose Q)
            (fun a b => A a b + dA a b)) i j := by
            rw [matMulRect_assoc_square_left]
    _ = matMulRect m m n Q R_hat i j := by rw [← hRmat]

/-- The literal matrix-level actual-executor closure of Higham Theorem 19.10.
The returned `R_hat` is exactly the canonical anti-diagonal
`fl_givensQRStageFold`; `Q` is orthogonal; and the perturbation in
`A + DeltaA = Q R_hat` satisfies the source `m+n-2` disjoint-stage
columnwise coefficient with no residual or growth premise. -/
theorem H19_Theorem19_10_actual_matrix_executor_gamma6
    (fp : FPModel) (m n : Nat) (A : Fin m -> Fin n -> Real)
    (hn : 0 < n) (hnm : n <= m) (hvalid : gammaValid fp 6) :
    exists Q : Fin m -> Fin m -> Real,
      H19.Theorem19_10.GivensQRBackwardError m n A Q
        (fl_givensQRStageFold fp m n (givensQRStageCount m n) A)
        (gammaTildeDimIndepGamma6 fp m n) := by
  apply H19_Theorem19_10_actual_matrix_executor_gamma6_of_local
    fp m n A hn hnm hvalid
  intro s _hs t ht j
  let B := fl_givensQRStageFold fp m n s A
  have htstage : t.stage = s := givensQRStageTasks_stage t ht
  have hzero_s : ZeroedThrough s B :=
    fl_givensQRStageFold_zeroedThrough fp m n A s
  exact fl_givensQRTaskStepOfTask_pair_sq_residual_le_gamma6
    fp m n t B (by simpa [htstage] using hzero_s) hvalid j

end NumStability.Wave13
