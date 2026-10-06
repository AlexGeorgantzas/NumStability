import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.RecursiveFactorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Algorithm03
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis
import NumStability.Source.Higham.Chapter13.Theorem02.Factorization
import NumStability.Source.Higham.Chapter13.Theorem07.PivotExistence

/-!
# Source.Higham.Chapter13.Problem04.MatrixStages

This module formalizes the source-facing Chapter 13 statements for
`Problem04.MatrixStages`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Upper block factor assembled from the matrix-product Algorithm 13.3
    Schur stages. -/
noncomputable def higham13_algorithm13_3_upperFromMatrixStages {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
  fun i j =>
    if i.val ≤ j.val then
      higham13_algorithm13_3_schurStageMatrixBlock A pivotInv i.val i j
    else 0

/-- Lower block factor assembled from the matrix-product Algorithm 13.3
    Schur stages.

    The diagonal blocks are identities.  Below the diagonal, the block in
    column `j` is the stage-`j` multiplier `Aᵢⱼ^(j) Aⱼⱼ^(j)⁻¹`, represented by
    the supplied `pivotInv j`.  Above the diagonal the factor is zero. -/
noncomputable def higham13_algorithm13_3_lowerFromMatrixStages {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
  fun i j =>
    if j.val < i.val then
      higham13_algorithm13_3_schurStageMatrixBlock A pivotInv j.val i j *
        pivotInv j.val
    else if i = j then idBlock r else zeroBlock r

/-- On or above the block diagonal, the assembled matrix-stage upper factor is
    exactly the block stored at the corresponding Algorithm 13.3 stage. -/
theorem higham13_algorithm13_3_upperFromMatrixStages_eq_of_le {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {i j : Fin m} (hij : i.val ≤ j.val) :
    higham13_algorithm13_3_upperFromMatrixStages A pivotInv i j =
      higham13_algorithm13_3_schurStageMatrixBlock A pivotInv i.val i j := by
  simp [higham13_algorithm13_3_upperFromMatrixStages, hij]

/-- Below the block diagonal, the assembled matrix-stage upper factor is zero. -/
theorem higham13_algorithm13_3_upperFromMatrixStages_lower_zero {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {i j : Fin m} (hji : j.val < i.val) :
    higham13_algorithm13_3_upperFromMatrixStages A pivotInv i j = zeroBlock r := by
  have hnot : ¬ i.val ≤ j.val := Nat.not_le.mpr hji
  ext s t
  simp [higham13_algorithm13_3_upperFromMatrixStages, hnot, zeroBlock]

/-- In the assembled matrix-stage upper factor, the first block row is the
    first block row of the input matrix. -/
theorem higham13_algorithm13_3_upperFromMatrixStages_first_row {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (j : Fin (m + 1)) :
    higham13_algorithm13_3_upperFromMatrixStages A pivotInv 0 j = A 0 j := by
  simp [higham13_algorithm13_3_upperFromMatrixStages,
    higham13_algorithm13_3_schurStageMatrixBlock,
    higham13_algorithm13_3_schurStageBlock]

/-- Strictly below the block diagonal, the assembled matrix-stage lower factor
    is the stage multiplier `Aᵢⱼ^(j) Aⱼⱼ^(j)⁻¹`. -/
theorem higham13_algorithm13_3_lowerFromMatrixStages_eq_of_lt {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {i j : Fin m} (hji : j.val < i.val) :
    higham13_algorithm13_3_lowerFromMatrixStages A pivotInv i j =
      higham13_algorithm13_3_schurStageMatrixBlock A pivotInv j.val i j *
        pivotInv j.val := by
  simp [higham13_algorithm13_3_lowerFromMatrixStages, hji]

/-- The assembled matrix-stage lower factor has identity diagonal blocks. -/
theorem higham13_algorithm13_3_lowerFromMatrixStages_diag {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (i : Fin m) :
    higham13_algorithm13_3_lowerFromMatrixStages A pivotInv i i = idBlock r := by
  simp [higham13_algorithm13_3_lowerFromMatrixStages]

/-- Above the block diagonal, the assembled matrix-stage lower factor is zero. -/
theorem higham13_algorithm13_3_lowerFromMatrixStages_upper_zero {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {i j : Fin m} (hij : i.val < j.val) :
    higham13_algorithm13_3_lowerFromMatrixStages A pivotInv i j = zeroBlock r := by
  have hnot : ¬ j.val < i.val := Nat.not_lt.mpr (Nat.le_of_lt hij)
  have hne : i ≠ j := by
    intro hEq
    subst j
    exact Nat.lt_irrefl i.val hij
  ext s t
  simp [higham13_algorithm13_3_lowerFromMatrixStages, hnot, hne, zeroBlock]

/-- In the assembled matrix-stage lower factor, the first block column below
    the diagonal is the first pivot multiplier `Aᵢ₀^(0) pivotInv 0`. -/
theorem higham13_algorithm13_3_lowerFromMatrixStages_first_column {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {i : Fin (m + 1)} (hi : 0 < i.val) :
    higham13_algorithm13_3_lowerFromMatrixStages A pivotInv i 0 =
      A i 0 * pivotInv 0 := by
  simp [higham13_algorithm13_3_lowerFromMatrixStages, hi,
    higham13_algorithm13_3_schurStageMatrixBlock,
    higham13_algorithm13_3_schurStageBlock]

/-- The assembled matrix-stage upper factor is the one-step upper factor whose
    trailing block is assembled from the shifted Schur-tail stage table. -/
theorem higham13_algorithm13_3_upperFromMatrixStages_succ_eq_blockLUOneStepU
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    higham13_algorithm13_3_upperFromMatrixStages A pivotInv =
      blockLUOneStepU A
        (higham13_algorithm13_3_upperFromMatrixStages
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1))) := by
  ext i j s t
  by_cases hi : i = 0
  · subst i
    simp [blockLUOneStepU,
      higham13_algorithm13_3_upperFromMatrixStages_first_row]
  · by_cases hj : j = 0
    · subst j
      have hji : (0 : Fin (m + 1)).val < i.val := by
        have hival : i.val ≠ 0 := fun h => hi (Fin.ext h)
        simpa using Nat.pos_of_ne_zero hival
      simp [blockLUOneStepU, hi,
        higham13_algorithm13_3_upperFromMatrixStages_lower_zero A pivotInv hji,
        zeroBlock]
    · have hpred_le_iff :
          (i.pred hi).val ≤ (j.pred hj).val ↔ i.val ≤ j.val := by
        rw [Fin.val_pred, Fin.val_pred]
        have hi0 : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
        have hj0 : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))
        omega
      by_cases hij : i.val ≤ j.val
      · have htail :=
          higham13_algorithm13_3_schurStageMatrixBlock_tail_shift A pivotInv
            (i.pred hi).val (i.pred hi) (j.pred hj)
        have hidx : Fin.succ (i.pred hi) = i := Fin.succ_pred i hi
        have hstage :
            higham13_algorithm13_3_schurStageMatrixBlock
                (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1))
                (i.pred hi).val (i.pred hi) (j.pred hj) =
              higham13_algorithm13_3_schurStageMatrixBlock A pivotInv i.val i j := by
          have hi_pos : 0 < i.val :=
            Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
          have hval : i.val - 1 + 1 = i.val :=
            Nat.sub_add_cancel hi_pos
          simpa [hidx, Fin.val_pred, hval] using htail
        have hpred_le : (i.pred hi).val ≤ (j.pred hj).val :=
          hpred_le_iff.mpr hij
        have hcond : i.val ≤ j.val - 1 + 1 := by
          have hjpos : 0 < j.val :=
            Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))
          have hsub : j.val - 1 + 1 = j.val :=
            Nat.sub_add_cancel hjpos
          simpa [hsub] using hij
        simpa [blockLUOneStepU, hi, hj,
          higham13_algorithm13_3_upperFromMatrixStages, hij, hcond, Fin.val_pred]
          using congr_fun (congr_fun hstage.symm s) t
      · have hcond : ¬ i.val ≤ j.val - 1 + 1 := by
          have hjpos : 0 < j.val :=
            Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))
          have hsub : j.val - 1 + 1 = j.val :=
            Nat.sub_add_cancel hjpos
          simpa [hsub] using hij
        simp [blockLUOneStepU, hi, hj,
          higham13_algorithm13_3_upperFromMatrixStages, hij, hcond]

/-- The assembled matrix-stage lower factor is the one-step lower factor whose
    trailing block is assembled from the shifted Schur-tail stage table. -/
theorem higham13_algorithm13_3_lowerFromMatrixStages_succ_eq_blockLUOneStepL
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    higham13_algorithm13_3_lowerFromMatrixStages A pivotInv =
      blockLUOneStepL A (pivotInv 0)
        (higham13_algorithm13_3_lowerFromMatrixStages
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1))) := by
  ext i j s t
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      simp [blockLUOneStepL, higham13_algorithm13_3_lowerFromMatrixStages]
    · have h0ne : (0 : Fin (m + 1)) ≠ j := by
        intro h
        exact hj h.symm
      simp [blockLUOneStepL,
        higham13_algorithm13_3_lowerFromMatrixStages, hj, h0ne, zeroBlock]
  · by_cases hj : j = 0
    · subst j
      have hi_pos : 0 < i.val :=
        Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
      simpa [blockLUOneStepL, hi, Matrix.mul_apply] using
        congr_fun
          (congr_fun
            (higham13_algorithm13_3_lowerFromMatrixStages_first_column
              A pivotInv hi_pos) s) t
    · have hpred_lt_iff :
          (j.pred hj).val < (i.pred hi).val ↔ j.val < i.val := by
        rw [Fin.val_pred, Fin.val_pred]
        have hi0 : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
        have hj0 : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))
        omega
      by_cases hji : j.val < i.val
      · have htail :=
          higham13_algorithm13_3_schurStageMatrixBlock_tail_shift A pivotInv
            (j.pred hj).val (i.pred hi) (j.pred hj)
        have hiidx : Fin.succ (i.pred hi) = i := Fin.succ_pred i hi
        have hjidx : Fin.succ (j.pred hj) = j := Fin.succ_pred j hj
        have hj_pos : 0 < j.val :=
          Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))
        have hjval : j.val - 1 + 1 = j.val :=
          Nat.sub_add_cancel hj_pos
        have hstage :
            higham13_algorithm13_3_schurStageMatrixBlock
                (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1))
                (j.pred hj).val (i.pred hi) (j.pred hj) =
              higham13_algorithm13_3_schurStageMatrixBlock A pivotInv j.val i j := by
          simpa [hiidx, hjidx, Fin.val_pred, hjval] using htail
        have hpred_lt : (j.pred hj).val < (i.pred hi).val :=
          hpred_lt_iff.mpr hji
        have hcond : j.val - 1 < i.val - 1 := by
          simpa [Fin.val_pred] using hpred_lt
        have hprod :
            higham13_algorithm13_3_schurStageMatrixBlock
                (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1))
                (j.pred hj).val (i.pred hi) (j.pred hj) * pivotInv j.val =
              higham13_algorithm13_3_schurStageMatrixBlock A pivotInv j.val i j *
                pivotInv j.val := by
          exact congrArg (fun B => B * pivotInv j.val) hstage
        simpa [blockLUOneStepL, hi, hj,
          higham13_algorithm13_3_lowerFromMatrixStages, hji, hcond,
          Fin.val_pred, hjval]
          using congr_fun (congr_fun hprod.symm s) t
      · by_cases heq : i = j
        · subst j
          simp [blockLUOneStepL, hi, higham13_algorithm13_3_lowerFromMatrixStages]
        · have hpred_not : ¬ (j.pred hj).val < (i.pred hi).val := by
            exact fun h => hji (hpred_lt_iff.mp h)
          have hpred_ne : i.pred hi ≠ j.pred hj := by
            intro h
            apply heq
            calc
              i = Fin.succ (i.pred hi) := (Fin.succ_pred i hi).symm
              _ = Fin.succ (j.pred hj) := by rw [h]
              _ = j := Fin.succ_pred j hj
          have hcond : ¬ j.val - 1 < i.val - 1 := by
            simpa [Fin.val_pred] using hpred_not
          simp [blockLUOneStepL, hi, hj,
            higham13_algorithm13_3_lowerFromMatrixStages, hji, heq,
            hcond, hpred_ne, zeroBlock]

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    the assembled matrix-product stage factors satisfy the block-LU
    specification when every recorded pivot inverse is a left inverse of the
    corresponding active pivot block. -/
theorem higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_left_inverse
    {r : ℕ} :
    ∀ {m : ℕ}
      (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
      (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ),
      (∀ k : ℕ, ∀ hk : k < m,
        IsLeftInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k)) →
      BlockLUFactSpec m r A
        (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) := by
  intro m
  induction m with
  | zero =>
      intro A pivotInv hPivot
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ m ih =>
      intro A pivotInv hPivot
      let S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
        blockSchur A (pivotInv 0)
      let shiftedPivot : ℕ → Matrix (Fin r) (Fin r) ℝ :=
        fun q => pivotInv (q + 1)
      have hInvLeft : ∀ s t : Fin r,
          ∑ l : Fin r, pivotInv 0 s l * A 0 0 l t = if s = t then 1 else 0 := by
        intro s t
        have h0 := hPivot 0 (Nat.succ_pos m)
        exact h0 s t
      have hTailPivot : ∀ k : ℕ, ∀ hk : k < m,
          IsLeftInverse r
            (higham13_algorithm13_3_schurStageMatrixBlock S shiftedPivot k
              ⟨k, hk⟩ ⟨k, hk⟩)
            (shiftedPivot k) := by
        intro k hk s t
        have hkFull : k + 1 < m + 1 := Nat.succ_lt_succ hk
        have hshift :=
          higham13_algorithm13_3_schurStageMatrixBlock_tail_shift
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩
        have hpivot :
            (Fin.succ (⟨k, hk⟩ : Fin m) : Fin (m + 1)) =
              ⟨k + 1, hkFull⟩ := by
          ext
          rfl
        dsimp [S, shiftedPivot]
        rw [hshift, hpivot]
        exact hPivot (k + 1) hkFull s t
      have hTailFact :
          BlockLUFactSpec m r S
            (higham13_algorithm13_3_lowerFromMatrixStages S shiftedPivot)
            (higham13_algorithm13_3_upperFromMatrixStages S shiftedPivot) :=
        ih S shiftedPivot hTailPivot
      have hOne :
          BlockLUFactSpec (m + 1) r A
            (blockLUOneStepL A (pivotInv 0)
              (higham13_algorithm13_3_lowerFromMatrixStages S shiftedPivot))
            (blockLUOneStepU A
              (higham13_algorithm13_3_upperFromMatrixStages S shiftedPivot)) := by
        exact block_lu_one_step_explicit A (pivotInv 0) hInvLeft
          (higham13_algorithm13_3_lowerFromMatrixStages S shiftedPivot)
          (higham13_algorithm13_3_upperFromMatrixStages S shiftedPivot)
          hTailFact
      rw [higham13_algorithm13_3_lowerFromMatrixStages_succ_eq_blockLUOneStepL
          A pivotInv,
        higham13_algorithm13_3_upperFromMatrixStages_succ_eq_blockLUOneStepU
          A pivotInv]
      simpa [S, shiftedPivot] using hOne

/-- Product-entry form of
    `higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_left_inverse`.
    This is the source Algorithm 13.3 reconstruction equality for the assembled
    matrix-stage factors, under the explicit pivot-left-inverse certificate. -/
theorem higham13_algorithm13_3_matrixStages_product_eq_of_pivot_left_inverse
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotLeft : ∀ k : ℕ, ∀ hk : k < m,
      IsLeftInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    ∀ (i j : Fin m) (s t : Fin r),
      ∑ k : Fin m, ∑ l : Fin r,
        higham13_algorithm13_3_lowerFromMatrixStages A pivotInv i k s l *
          higham13_algorithm13_3_upperFromMatrixStages A pivotInv k j l t =
        A i j s t := by
  exact
    (higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_left_inverse
      A pivotInv hPivotLeft).product_eq

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    at Algorithm 13.3 stage zero, the active pivot is the original first
    diagonal block, so the BDD all-prefix inverse table supplies its canonical
    two-sided inverse. -/
theorem
    higham13_algorithm13_3_initial_pivot_nonsingInv_isInverse_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ} (hm : 0 < m)
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol m (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0) :
    IsInverse r
      (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0
        ⟨0, hm⟩ ⟨0, hm⟩)
      (nonsingInv r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0
          ⟨0, hm⟩ ⟨0, hm⟩)) := by
  have hDiag :=
    higham13_diag_nonsingInv_isInverse_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
      A invDiagBound hPrefix hDom hBound ⟨0, hm⟩
  simpa [higham13_algorithm13_3_schurStageMatrixBlock,
    higham13_algorithm13_3_schurStageBlock] using hDiag

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    right-inverse projection of the BDD stage-zero canonical pivot inverse. -/
theorem
    higham13_algorithm13_3_initial_pivot_nonsingInv_isRightInverse_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ} (hm : 0 < m)
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol m (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0) :
    IsRightInverse r
      (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0
        ⟨0, hm⟩ ⟨0, hm⟩)
      (nonsingInv r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0
          ⟨0, hm⟩ ⟨0, hm⟩)) :=
  (higham13_algorithm13_3_initial_pivot_nonsingInv_isInverse_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
    hm A pivotInv invDiagBound hPrefix hDom hBound).2

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    determinant nonsingularity of the stage-zero Algorithm 13.3 pivot forced by
    the all-leading-prefix BDD table. -/
theorem
    higham13_algorithm13_3_initial_pivot_det_ne_zero_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ} (hm : 0 < m)
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol m (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0) :
    Matrix.det
      (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0
        ⟨0, hm⟩ ⟨0, hm⟩) ≠ 0 := by
  have hRight :=
    higham13_algorithm13_3_initial_pivot_nonsingInv_isRightInverse_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
      hm A pivotInv invDiagBound hPrefix hDom hBound
  exact
    Matrix.det_ne_zero_of_right_inverse
      (A := higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0
        ⟨0, hm⟩ ⟨0, hm⟩)
      (B := nonsingInv r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0
          ⟨0, hm⟩ ⟨0, hm⟩))
      (by
        ext i j
        rw [Matrix.mul_apply, Matrix.one_apply]
        exact hRight i j)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    if Algorithm 13.3's supplied first pivot inverse is the canonical inverse
    forced by the BDD all-prefix table, then the first active pivot has the
    exact right-inverse certificate required by downstream pivot APIs. -/
theorem
    higham13_algorithm13_3_initial_pivot_right_inverse_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ} (hm : 0 < m)
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol m (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 = nonsingInv r (A ⟨0, hm⟩ ⟨0, hm⟩)) :
    IsRightInverse r
      (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0
        ⟨0, hm⟩ ⟨0, hm⟩)
      (pivotInv 0) := by
  have hRight :=
    higham13_algorithm13_3_initial_pivot_nonsingInv_isRightInverse_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
      hm A pivotInv invDiagBound hPrefix hDom hBound
  simpa [hPivot0, higham13_algorithm13_3_schurStageMatrixBlock,
    higham13_algorithm13_3_schurStageBlock] using hRight

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    if the supplied first pivot inverse is the BDD-forced canonical inverse,
    then it is also Mathlib's `⅟` inverse for the first-split pivot block.

    This bridges the BDD `nonsingInv` route to active-suffix APIs that state
    pivot identities using `⅟(blockMatrixFirstSplitA11 ...)`. -/
theorem
    higham13_algorithm13_3_initial_pivot_eq_invOf_blockMatrixFirstSplitA11_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    [Invertible (blockMatrixFirstSplitA11 A)]
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol (m + 1) (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 = nonsingInv r (A 0 0)) :
    pivotInv 0 = ⅟(blockMatrixFirstSplitA11 A) := by
  have hRightStage :=
    higham13_algorithm13_3_initial_pivot_right_inverse_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
      (Nat.succ_pos m) A pivotInv invDiagBound hPrefix hDom hBound hPivot0
  have hRight :
      IsRightInverse r (blockMatrixFirstSplitA11 A) (pivotInv 0) := by
    simpa [blockMatrixFirstSplitA11, higham13_algorithm13_3_schurStageMatrixBlock,
      higham13_algorithm13_3_schurStageBlock] using hRightStage
  symm
  change (⅟(blockMatrixFirstSplitA11 A) : Matrix (Fin r) (Fin r) ℝ) =
    (pivotInv 0 : Matrix (Fin r) (Fin r) ℝ)
  apply invOf_eq_right_inv
  ext i j
  simpa [Matrix.mul_apply] using hRight i j

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    the first Schur tail in Algorithm 13.3 is block-nonsingular when the
    original matrix has all nonsingular leading prefixes and the first pivot
    inverse is the BDD-forced canonical inverse of the first diagonal block.

    This is the first recursive nonsingularity handoff after the stage-zero
    pivot bridge.  It does not assert the later active Schur-stage BDD
    reciprocal/source table. -/
theorem
    higham13_algorithm13_3_first_schur_tail_blockMatrixNonsingular_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1)))) :
    BlockMatrixNonsingular (blockSchur A (pivotInv 0)) := by
  have hDiagInv :
      IsInverse r
        (A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1)))
        (nonsingInv r
          (A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1)))) :=
    higham13_diag_nonsingInv_isInverse_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
      A invDiagBound hPrefix hDom hBound (0 : Fin ((m + 1) + 1))
  have hInvLeft :
      ∀ s t : Fin r,
        ∑ l : Fin r,
          pivotInv 0 s l *
            A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1)) l t =
          if s = t then 1 else 0 := by
    simpa [hPivot0] using hDiagInv.1
  have hInvRight :
      ∀ s t : Fin r,
        ∑ l : Fin r,
          A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1)) s l *
            pivotInv 0 l t =
          if s = t then 1 else 0 := by
    simpa [hPivot0] using hDiagInv.2
  have hFull : BlockMatrixNonsingular A := by
    simpa [leadingBlockPrefix13_2] using
      hPrefix (m + 1) (Nat.lt_succ_self (m + 1))
  exact
    blockSchur_nonsingular_of_nonsingular_of_first_block_inverse
      hInvLeft hInvRight hFull

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    the all-leading-prefix nonsingularity table transfers to the first
    Algorithm 13.3 Schur tail once the BDD-forced canonical first pivot inverse
    is used.

    This is the recursive leading-principal-block handoff needed before the
    BDD route can be iterated on Schur tails. -/
theorem
    higham13_algorithm13_3_first_schur_tail_leadingPrincipalBlockNonsingular_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1)))) :
    LeadingPrincipalBlockNonsingular13_2 (blockSchur A (pivotInv 0)) := by
  have hDiagInv :
      IsInverse r
        (A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1)))
        (nonsingInv r
          (A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1)))) :=
    higham13_diag_nonsingInv_isInverse_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
      A invDiagBound hPrefix hDom hBound (0 : Fin ((m + 1) + 1))
  have hInvLeft :
      ∀ s t : Fin r,
        ∑ l : Fin r,
          pivotInv 0 s l *
            A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1)) l t =
          if s = t then 1 else 0 := by
    simpa [hPivot0] using hDiagInv.1
  have hInvRight :
      ∀ s t : Fin r,
        ∑ l : Fin r,
          A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1)) s l *
            pivotInv 0 l t =
          if s = t then 1 else 0 := by
    simpa [hPivot0] using hDiagInv.2
  have hLead : LeadingPrincipalBlockNonsingular13_2 A := by
    intro p hp
    exact hPrefix p (Nat.lt_trans (Nat.lt_succ_self p) hp)
  exact LeadingPrincipalBlockNonsingular13_2.schur hInvLeft hInvRight hLead

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    all leading prefixes of the first Algorithm 13.3 Schur tail are
    nonsingular under the BDD-derived canonical first pivot.

    This packages the preceding full-tail and leading-principal handoffs in
    the exact table shape consumed by the all-prefix BDD diagonal-inverse
    theorem. -/
theorem
    higham13_algorithm13_3_first_schur_tail_all_leadingBlockPrefixes_nonsingular_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1)))) :
    ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (blockSchur A (pivotInv 0)) p hp) := by
  intro p hp
  by_cases hpLead : p + 1 < m + 1
  · have hLeadTail :=
      higham13_algorithm13_3_first_schur_tail_leadingPrincipalBlockNonsingular_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
        A pivotInv invDiagBound hPrefix hDom hBound hPivot0
    simpa [leadingBlockPrefix13_2] using hLeadTail p hpLead
  · have hpSuccLe : p + 1 ≤ m + 1 := Nat.succ_le_of_lt hp
    have hmSuccLe : m + 1 ≤ p + 1 := Nat.le_of_not_gt hpLead
    have hpSuccEq : p + 1 = m + 1 := le_antisymm hpSuccLe hmSuccLe
    have hpEq : p = m := Nat.succ.inj hpSuccEq
    subst p
    have hTail :=
      higham13_algorithm13_3_first_schur_tail_blockMatrixNonsingular_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
        A pivotInv invDiagBound hPrefix hDom hBound hPivot0
    simpa [leadingBlockPrefix13_2] using hTail

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    tail-level canonical diagonal inverse table for the first Algorithm 13.3
    Schur complement.

    Once the first Schur tail has its own column-BDD lower-bound table, the
    preceding all-prefix handoff lets the existing BDD diagonal-inverse theorem
    produce canonical `nonsingInv` two-sided inverses for every tail diagonal
    block.  This is a recursive dependency; it does not prove the tail BDD
    table itself. -/
theorem
    higham13_algorithm13_3_first_schur_tail_diag_nonsingInv_isInverse_of_tail_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (tailInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hTailDom : IsBlockDiagDomCol (m + 1)
      (fun i j => ‖blockSchur A (pivotInv 0) i j‖) tailInvDiagBound)
    (hTailBound : ∀ j : Fin (m + 1), tailInvDiagBound j ≤ 0)
    (j : Fin (m + 1)) :
    IsInverse r
      ((blockSchur A (pivotInv 0)) j j)
      (nonsingInv r ((blockSchur A (pivotInv 0)) j j)) := by
  exact
    higham13_diag_nonsingInv_isInverse_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
      (blockSchur A (pivotInv 0)) tailInvDiagBound
      (higham13_algorithm13_3_first_schur_tail_all_leadingBlockPrefixes_nonsingular_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
        A pivotInv invDiagBound hPrefix hDom hBound hPivot0)
      hTailDom hTailBound j

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    right-inverse projection of the first-Schur-tail canonical diagonal
    inverse table. -/
theorem
    higham13_algorithm13_3_first_schur_tail_diag_nonsingInv_isRightInverse_of_tail_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (tailInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hTailDom : IsBlockDiagDomCol (m + 1)
      (fun i j => ‖blockSchur A (pivotInv 0) i j‖) tailInvDiagBound)
    (hTailBound : ∀ j : Fin (m + 1), tailInvDiagBound j ≤ 0)
    (j : Fin (m + 1)) :
    IsRightInverse r
      ((blockSchur A (pivotInv 0)) j j)
      (nonsingInv r ((blockSchur A (pivotInv 0)) j j)) :=
  (higham13_algorithm13_3_first_schur_tail_diag_nonsingInv_isInverse_of_tail_blockDiagDomCol_diagBound_nonpos
    A pivotInv invDiagBound tailInvDiagBound hPrefix hDom hBound hPivot0
    hTailDom hTailBound j).2

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    determinant form of the first-Schur-tail diagonal inverse table. -/
theorem
    higham13_algorithm13_3_first_schur_tail_diag_det_ne_zero_of_tail_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (tailInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hTailDom : IsBlockDiagDomCol (m + 1)
      (fun i j => ‖blockSchur A (pivotInv 0) i j‖) tailInvDiagBound)
    (hTailBound : ∀ j : Fin (m + 1), tailInvDiagBound j ≤ 0)
    (j : Fin (m + 1)) :
    Matrix.det ((blockSchur A (pivotInv 0)) j j) ≠ 0 := by
  have hRight :=
    higham13_algorithm13_3_first_schur_tail_diag_nonsingInv_isRightInverse_of_tail_blockDiagDomCol_diagBound_nonpos
      A pivotInv invDiagBound tailInvDiagBound hPrefix hDom hBound hPivot0
      hTailDom hTailBound j
  exact
    Matrix.det_ne_zero_of_right_inverse
      (A := (blockSchur A (pivotInv 0)) j j)
      (B := nonsingInv r ((blockSchur A (pivotInv 0)) j j))
      (by
        ext s t
        rw [Matrix.mul_apply, Matrix.one_apply]
        exact hRight s t)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    the stage-1 active pivot of the original matrix is the first diagonal
    block of the first Schur tail. -/
theorem higham13_algorithm13_3_stage1_pivot_eq_first_schur_tail_diag
    {m r : ℕ}
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 1
        (1 : Fin ((m + 1) + 1))
        (1 : Fin ((m + 1) + 1)) =
      (blockSchur A (pivotInv 0))
        (0 : Fin (m + 1)) (0 : Fin (m + 1)) := by
  let z : Fin (m + 1) := 0
  have hsucc :
      (Fin.succ z : Fin ((m + 1) + 1)) =
        (1 : Fin ((m + 1) + 1)) := by
    ext
    rfl
  have hshift :=
    higham13_algorithm13_3_schurStageMatrixBlock_tail_shift
      A pivotInv 0 z z
  simpa [z, hsucc, higham13_algorithm13_3_schurStageMatrixBlock,
    higham13_algorithm13_3_schurStageBlock] using hshift.symm

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    canonical inverse certificate for the stage-1 Algorithm 13.3 pivot from a
    BDD table on the first Schur tail. -/
theorem
    higham13_algorithm13_3_stage1_pivot_nonsingInv_isInverse_of_first_schur_tail_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (tailInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hTailDom : IsBlockDiagDomCol (m + 1)
      (fun i j => ‖blockSchur A (pivotInv 0) i j‖) tailInvDiagBound)
    (hTailBound : ∀ j : Fin (m + 1), tailInvDiagBound j ≤ 0) :
    IsInverse r
      (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 1
        (1 : Fin ((m + 1) + 1))
        (1 : Fin ((m + 1) + 1)))
      (nonsingInv r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 1
          (1 : Fin ((m + 1) + 1))
          (1 : Fin ((m + 1) + 1)))) := by
  have hstage :=
    higham13_algorithm13_3_stage1_pivot_eq_first_schur_tail_diag A pivotInv
  have hTail :=
    higham13_algorithm13_3_first_schur_tail_diag_nonsingInv_isInverse_of_tail_blockDiagDomCol_diagBound_nonpos
      A pivotInv invDiagBound tailInvDiagBound hPrefix hDom hBound hPivot0
      hTailDom hTailBound (0 : Fin (m + 1))
  rw [hstage]
  simpa using hTail

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    if the supplied stage-1 pivot inverse is the canonical inverse of the
    first Schur-tail diagonal block, then it is a right inverse of the actual
    Algorithm 13.3 stage-1 pivot. -/
theorem
    higham13_algorithm13_3_stage1_pivot_right_inverse_of_pivotInv_eq_nonsingInv_first_schur_tail_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (tailInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hTailDom : IsBlockDiagDomCol (m + 1)
      (fun i j => ‖blockSchur A (pivotInv 0) i j‖) tailInvDiagBound)
    (hTailBound : ∀ j : Fin (m + 1), tailInvDiagBound j ≤ 0)
    (hPivot1 :
      pivotInv 1 =
        nonsingInv r
          ((blockSchur A (pivotInv 0))
            (0 : Fin (m + 1)) (0 : Fin (m + 1)))) :
    IsRightInverse r
      (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 1
        (1 : Fin ((m + 1) + 1))
        (1 : Fin ((m + 1) + 1)))
      (pivotInv 1) := by
  have hstage :=
    higham13_algorithm13_3_stage1_pivot_eq_first_schur_tail_diag A pivotInv
  have hTail :=
    higham13_algorithm13_3_first_schur_tail_diag_nonsingInv_isRightInverse_of_tail_blockDiagDomCol_diagBound_nonpos
      A pivotInv invDiagBound tailInvDiagBound hPrefix hDom hBound hPivot0
      hTailDom hTailBound (0 : Fin (m + 1))
  rw [hstage]
  simpa [hPivot1] using hTail

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    if the supplied stage-1 pivot inverse is the BDD-forced canonical inverse
    of the first Schur tail's leading block, then it is also Mathlib's `⅟`
    inverse for that first-split tail block. -/
theorem
    higham13_algorithm13_3_stage1_pivot_eq_invOf_first_schur_tail_of_pivotInv_eq_nonsingInv_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (tailInvDiagBound : Fin (m + 1) → ℝ)
    [Invertible (blockMatrixFirstSplitA11 (blockSchur A (pivotInv 0)))]
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hTailDom : IsBlockDiagDomCol (m + 1)
      (fun i j => ‖blockSchur A (pivotInv 0) i j‖) tailInvDiagBound)
    (hTailBound : ∀ j : Fin (m + 1), tailInvDiagBound j ≤ 0)
    (hPivot1 :
      pivotInv 1 =
        nonsingInv r
          ((blockSchur A (pivotInv 0))
            (0 : Fin (m + 1)) (0 : Fin (m + 1)))) :
    pivotInv 1 = ⅟(blockMatrixFirstSplitA11 (blockSchur A (pivotInv 0))) := by
  have hRightStage :=
    higham13_algorithm13_3_stage1_pivot_right_inverse_of_pivotInv_eq_nonsingInv_first_schur_tail_blockDiagDomCol_diagBound_nonpos
      A pivotInv invDiagBound tailInvDiagBound hPrefix hDom hBound hPivot0
      hTailDom hTailBound hPivot1
  have hstage :=
    higham13_algorithm13_3_stage1_pivot_eq_first_schur_tail_diag A pivotInv
  have hRight :
      IsRightInverse r
        (blockMatrixFirstSplitA11 (blockSchur A (pivotInv 0))) (pivotInv 1) := by
    rw [hstage] at hRightStage
    simpa [blockMatrixFirstSplitA11] using hRightStage
  symm
  change
    (⅟(blockMatrixFirstSplitA11 (blockSchur A (pivotInv 0))) :
      Matrix (Fin r) (Fin r) ℝ) =
    (pivotInv 1 : Matrix (Fin r) (Fin r) ℝ)
  apply invOf_eq_right_inv
  ext i j
  simpa [Matrix.mul_apply] using hRight i j

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    determinant nonsingularity of the stage-1 Algorithm 13.3 pivot from a BDD
    table on the first Schur tail. -/
theorem
    higham13_algorithm13_3_stage1_pivot_det_ne_zero_of_first_schur_tail_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (tailInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hTailDom : IsBlockDiagDomCol (m + 1)
      (fun i j => ‖blockSchur A (pivotInv 0) i j‖) tailInvDiagBound)
    (hTailBound : ∀ j : Fin (m + 1), tailInvDiagBound j ≤ 0) :
    Matrix.det
      (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 1
        (1 : Fin ((m + 1) + 1))
        (1 : Fin ((m + 1) + 1))) ≠ 0 := by
  have hstage :=
    higham13_algorithm13_3_stage1_pivot_eq_first_schur_tail_diag A pivotInv
  have hTail :=
    higham13_algorithm13_3_first_schur_tail_diag_det_ne_zero_of_tail_blockDiagDomCol_diagBound_nonpos
      A pivotInv invDiagBound tailInvDiagBound hPrefix hDom hBound hPivot0
      hTailDom hTailBound (0 : Fin (m + 1))
  rw [hstage]
  simpa using hTail

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    first-two-pivots table for Algorithm 13.3 under the BDD recursive handoff.

    This packages the stage-zero canonical inverse bridge and the first Schur
    tail's stage-one bridge into the small active table shape consumed by
    downstream pivot APIs.  It is only a two-pivot dependency, not the full
    all-active Schur-stage pivot table. -/
theorem
    higham13_algorithm13_3_first_two_pivots_right_inverse_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_first_schur_tail_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (tailInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hTailDom : IsBlockDiagDomCol (m + 1)
      (fun i j => ‖blockSchur A (pivotInv 0) i j‖) tailInvDiagBound)
    (hTailBound : ∀ j : Fin (m + 1), tailInvDiagBound j ≤ 0)
    (hPivot1 :
      pivotInv 1 =
        nonsingInv r
          ((blockSchur A (pivotInv 0))
            (0 : Fin (m + 1)) (0 : Fin (m + 1)))) :
    ∀ k : Fin 2,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k.val
          ⟨k.val, by omega⟩ ⟨k.val, by omega⟩)
        (pivotInv k.val) := by
  intro k
  fin_cases k
  · have h0 :=
      higham13_algorithm13_3_initial_pivot_right_inverse_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
        (Nat.succ_pos (m + 1)) A pivotInv invDiagBound hPrefix hDom hBound
        hPivot0
    simpa using h0
  · have h1 :=
      higham13_algorithm13_3_stage1_pivot_right_inverse_of_pivotInv_eq_nonsingInv_first_schur_tail_blockDiagDomCol_diagBound_nonpos
        A pivotInv invDiagBound tailInvDiagBound hPrefix hDom hBound hPivot0
        hTailDom hTailBound hPivot1
    simpa using h1

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    determinant projection of the first-two-pivots BDD right-inverse table. -/
theorem
    higham13_algorithm13_3_first_two_pivots_det_ne_zero_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_first_schur_tail_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (tailInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hTailDom : IsBlockDiagDomCol (m + 1)
      (fun i j => ‖blockSchur A (pivotInv 0) i j‖) tailInvDiagBound)
    (hTailBound : ∀ j : Fin (m + 1), tailInvDiagBound j ≤ 0)
    (hPivot1 :
      pivotInv 1 =
        nonsingInv r
          ((blockSchur A (pivotInv 0))
            (0 : Fin (m + 1)) (0 : Fin (m + 1)))) :
    ∀ k : Fin 2,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k.val
          ⟨k.val, by omega⟩ ⟨k.val, by omega⟩) ≠ 0 := by
  intro k
  have hRight :=
    higham13_algorithm13_3_first_two_pivots_right_inverse_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_first_schur_tail_blockDiagDomCol_diagBound_nonpos
      A pivotInv invDiagBound tailInvDiagBound hPrefix hDom hBound hPivot0
      hTailDom hTailBound hPivot1 k
  exact
    Matrix.det_ne_zero_of_right_inverse
      (A := higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k.val
        ⟨k.val, by omega⟩ ⟨k.val, by omega⟩)
      (B := pivotInv k.val)
      (by
        ext i j
        rw [Matrix.mul_apply, Matrix.one_apply]
        exact hRight i j)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    product-index flattened determinant form of the BDD first-Schur-tail
    nonsingularity handoff. -/
theorem
    higham13_algorithm13_3_first_schur_tail_blockMatrixFlat_det_ne_zero_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (A (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1)))) :
    Matrix.det (blockMatrixFlat (blockSchur A (pivotInv 0))) ≠ 0 := by
  exact
    blockMatrixFlat_det_ne_zero_of_blockMatrixNonsingular
      (blockSchur A (pivotInv 0))
      (higham13_algorithm13_3_first_schur_tail_blockMatrixNonsingular_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
        A pivotInv invDiagBound hPrefix hDom hBound hPivot0)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    exact pivot right-inverse certificates also provide the pivot-left
    certificates needed by the matrix-stage reconstruction theorem. -/
theorem higham13_algorithm13_3_pivot_left_inverse_of_pivot_right_inverse
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    ∀ k : ℕ, ∀ hk : k < m,
      IsLeftInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k) := by
  intro k hk
  exact
    isLeftInverse_of_isRightInverse
      (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
        ⟨k, hk⟩ ⟨k, hk⟩)
      (pivotInv k) (hPivotRight k hk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    determinant nonsingularity of one active pivot from its exact
    right-inverse certificate. -/
theorem higham13_algorithm13_3_pivot_det_ne_zero_of_pivot_right_inverse_at
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (k : ℕ) (hk : k < m)
    (hPivotRight :
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    Matrix.det
      (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
        ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0 := by
  exact
    Matrix.det_ne_zero_of_right_inverse
      (A := higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
        ⟨k, hk⟩ ⟨k, hk⟩)
      (B := pivotInv k)
      (by
        ext i j
        rw [Matrix.mul_apply, Matrix.one_apply]
        exact hPivotRight i j)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    determinant nonsingularity of every active pivot from exact
    right-inverse certificates for those pivots. -/
theorem higham13_algorithm13_3_pivot_det_ne_zero_of_pivot_right_inverse
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0 := by
  intro k hk
  exact
    higham13_algorithm13_3_pivot_det_ne_zero_of_pivot_right_inverse_at
      A pivotInv k hk (hPivotRight k hk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    recursive tail-lift for active pivot right-inverse tables.

    If the first active pivot has its right-inverse certificate and the first
    Schur tail has the shifted active pivot table, then the original matrix has
    the full active pivot table.  This is the structural recursion bridge
    needed by BDD/source-chain routes; it does not prove the tail table itself. -/
theorem
    higham13_algorithm13_3_pivot_right_inverse_of_initial_pivot_and_first_schur_tail_pivot_right_inverse
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivot0 :
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0
          (0 : Fin (m + 1)) (0 : Fin (m + 1)))
        (pivotInv 0))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1))) :
    ∀ k : ℕ, ∀ hk : k < m + 1,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k) := by
  intro k hk
  cases k with
  | zero =>
      simpa using hPivot0
  | succ k =>
      have hkTail : k < m := Nat.succ_lt_succ_iff.mp hk
      have htail := hTail k hkTail
      have hidx :
          (Fin.succ (⟨k, hkTail⟩ : Fin m) : Fin (m + 1)) =
            (⟨k + 1, hk⟩ : Fin (m + 1)) := by
        ext
        rfl
      have hstage :=
        higham13_algorithm13_3_schurStageMatrixBlock_tail_shift
          A pivotInv k (⟨k, hkTail⟩ : Fin m) (⟨k, hkTail⟩ : Fin m)
      simpa [hidx, hstage] using htail

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    determinant projection of the recursive tail-lifted active pivot table. -/
theorem
    higham13_algorithm13_3_pivot_det_ne_zero_of_initial_pivot_and_first_schur_tail_pivot_right_inverse
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivot0 :
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0
          (0 : Fin (m + 1)) (0 : Fin (m + 1)))
        (pivotInv 0))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1))) :
    ∀ k : ℕ, ∀ hk : k < m + 1,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0 := by
  exact
    higham13_algorithm13_3_pivot_det_ne_zero_of_pivot_right_inverse A pivotInv
      (higham13_algorithm13_3_pivot_right_inverse_of_initial_pivot_and_first_schur_tail_pivot_right_inverse
        A pivotInv hPivot0 hTail)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    BDD initial-pivot specialization of the recursive active pivot-table lift.

    The all-leading-prefix BDD data and `pivotInv 0 = nonsingInv r (A 0 0)`
    discharge the first pivot.  The remaining hypothesis is exactly the shifted
    all-active pivot table for the first Schur tail. -/
theorem
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 = nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1))) :
    ∀ k : ℕ, ∀ hk : k < m + 1,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k) := by
  have h0 :=
    higham13_algorithm13_3_initial_pivot_right_inverse_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
      (Nat.succ_pos m) A pivotInv invDiagBound hPrefix hDom hBound hPivot0
  exact
    higham13_algorithm13_3_pivot_right_inverse_of_initial_pivot_and_first_schur_tail_pivot_right_inverse
      A pivotInv h0 hTail

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    determinant form of the BDD initial-pivot recursive active pivot-table
    lift. -/
theorem
    higham13_algorithm13_3_pivot_det_ne_zero_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 = nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1))) :
    ∀ k : ℕ, ∀ hk : k < m + 1,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0 := by
  exact
    higham13_algorithm13_3_pivot_det_ne_zero_of_pivot_right_inverse A pivotInv
      (higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
        A pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTail)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    if the supplied pivot inverse is Mathlib's `⅟` for each active pivot, then
    it gives the exact pivot right-inverse certificate used by the
    matrix-stage reconstruction wrappers. -/
theorem higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_invOf
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hInv : ∀ k : ℕ, ∀ hk : k < m,
      Invertible
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩))
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      letI : Invertible
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) := hInv k hk
      pivotInv k =
        ⅟(higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)) :
    ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k) := by
  intro k hk
  let pivot :=
    higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
      ⟨k, hk⟩ ⟨k, hk⟩
  letI : Invertible pivot := hInv k hk
  exact isRightInverse_of_eq_invOf pivot (pivotInv k) (hPivotInv k hk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    if the supplied pivot inverse is the repository canonical nonsingular
    inverse of each active pivot, then it gives the exact pivot right-inverse
    certificate used by the matrix-stage reconstruction and growth wrappers. -/
theorem higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv k =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)) :
    ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k) := by
  intro k hk
  rw [hPivotInv k hk]
  exact
    (isInverse_nonsingInv_of_det_ne_zero r
      (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
        ⟨k, hk⟩ ⟨k, hk⟩)
      (hPivotDet k hk)).2

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    recursive active pivot-table lift where the first Schur tail is given by
    source-style canonical `nonsingInv` pivot data.

    A stage-zero right-inverse certificate plus determinant/equality data for
    every active pivot of the first Schur tail yields the full active pivot
    table for the original matrix. -/
theorem
    higham13_algorithm13_3_pivot_right_inverse_of_initial_pivot_and_first_schur_tail_pivotInv_eq_nonsingInv
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivot0 :
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0
          (0 : Fin (m + 1)) (0 : Fin (m + 1)))
        (pivotInv 0))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩)) :
    ∀ k : ℕ, ∀ hk : k < m + 1,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k) := by
  have hTailRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1)) := by
    have hTailCanonical :=
      higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1))
        hTailDet
        (by
          intro k hk
          simpa using hTailPivotInv k hk)
    intro k hk
    simpa using hTailCanonical k hk
  exact
    higham13_algorithm13_3_pivot_right_inverse_of_initial_pivot_and_first_schur_tail_pivot_right_inverse
      A pivotInv hPivot0 hTailRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    determinant projection of the recursive canonical-tail active pivot-table
    lift. -/
theorem
    higham13_algorithm13_3_pivot_det_ne_zero_of_initial_pivot_and_first_schur_tail_pivotInv_eq_nonsingInv
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivot0 :
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0
          (0 : Fin (m + 1)) (0 : Fin (m + 1)))
        (pivotInv 0))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩)) :
    ∀ k : ℕ, ∀ hk : k < m + 1,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0 := by
  exact
    higham13_algorithm13_3_pivot_det_ne_zero_of_pivot_right_inverse A pivotInv
      (higham13_algorithm13_3_pivot_right_inverse_of_initial_pivot_and_first_schur_tail_pivotInv_eq_nonsingInv
        A pivotInv hPivot0 hTailDet hTailPivotInv)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    BDD initial-pivot specialization of the canonical-tail recursive active
    pivot-table lift.

    The all-leading-prefix BDD data and `pivotInv 0 = nonsingInv r (A 0 0)`
    discharge the first pivot.  The first Schur tail is supplied by determinant
    nonzero facts plus the canonical `nonsingInv` equality table. -/
theorem
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 = nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩)) :
    ∀ k : ℕ, ∀ hk : k < m + 1,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k) := by
  have h0 :=
    higham13_algorithm13_3_initial_pivot_right_inverse_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
      (Nat.succ_pos m) A pivotInv invDiagBound hPrefix hDom hBound hPivot0
  exact
    higham13_algorithm13_3_pivot_right_inverse_of_initial_pivot_and_first_schur_tail_pivotInv_eq_nonsingInv
      A pivotInv h0 hTailDet hTailPivotInv

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    determinant form of the BDD initial-pivot canonical-tail recursive active
    pivot-table lift. -/
theorem
    higham13_algorithm13_3_pivot_det_ne_zero_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 = nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩)) :
    ∀ k : ℕ, ∀ hk : k < m + 1,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0 := by
  exact
    higham13_algorithm13_3_pivot_det_ne_zero_of_pivot_right_inverse A pivotInv
      (higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
        A pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTailDet hTailPivotInv)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    matrix-`∞` BDD specialization of the canonical-tail recursive active
    pivot-table lift.

    This is the source-facing matrix-norm version of
    `...blockDiagDomCol_diagBound_nonpos`: it transports the `∞` operator-norm
    column-BDD hypothesis to the finite-function block norm and then reuses the
    existing first-Schur-tail canonical `nonsingInv` pivot lift. -/
theorem
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩)) :
    ∀ k : ℕ, ∀ hk : k < m + 1,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k) := by
  let Afn : Fin (m + 1) → Fin (m + 1) → Fin r → Fin r → ℝ :=
    fun i j a b => A i j a b
  let pivotFn : ℕ → Fin r → Fin r → ℝ :=
    fun k a b => pivotInv k a b
  have hPrefixFn : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 Afn p hp) := by
    intro p hp
    simpa [Afn] using hPrefix p hp
  have hDomPi : IsBlockDiagDomCol (m + 1)
      (fun i j => ‖Afn i j‖) invDiagBound := by
    simpa [Afn] using
      (higham13_blockDiagDomCol_piNorm_of_infNorm hr A invDiagBound hDom)
  have hPivot0Fn :
      pivotFn 0 =
        nonsingInv r (Afn (0 : Fin (m + 1)) (0 : Fin (m + 1))) := by
    simpa [Afn, pivotFn] using hPivot0
  have hTailDetFn : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Afn (pivotFn 0)) (fun q => pivotFn (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0 := by
    intro k hk
    simpa [Afn, pivotFn] using hTailDet k hk
  have hTailPivotInvFn : ∀ k : ℕ, ∀ hk : k < m,
      pivotFn (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur Afn (pivotFn 0)) (fun q => pivotFn (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩) := by
    intro k hk
    simpa [Afn, pivotFn] using hTailPivotInv k hk
  have hPivotRightFn :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
      Afn pivotFn invDiagBound hPrefixFn hDomPi hBound hPivot0Fn
      hTailDetFn hTailPivotInvFn
  intro k hk
  simpa [Afn, pivotFn] using hPivotRightFn k hk

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    determinant projection of the matrix-`∞` BDD canonical-tail recursive
    active pivot-table lift. -/
theorem
    higham13_algorithm13_3_pivot_det_ne_zero_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩)) :
    ∀ k : ℕ, ∀ hk : k < m + 1,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0 := by
  exact
    higham13_algorithm13_3_pivot_det_ne_zero_of_pivot_right_inverse A pivotInv
      (higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
        hr A pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTailDet
        hTailPivotInv)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    the assembled matrix-product stage factors satisfy `BlockLUFactSpec` from
    exact pivot right-inverse certificates. -/
theorem higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_right_inverse
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    BlockLUFactSpec m r A
      (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
      (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) := by
  exact
    higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_left_inverse
      A pivotInv
      (higham13_algorithm13_3_pivot_left_inverse_of_pivot_right_inverse
        A pivotInv hPivotRight)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    `BlockLUFactSpec` for the assembled matrix-product stage factors when the
    supplied pivot inverse is exactly Mathlib's `⅟` for every active pivot. -/
theorem higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivotInv_eq_invOf
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hInv : ∀ k : ℕ, ∀ hk : k < m,
      Invertible
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩))
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      letI : Invertible
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) := hInv k hk
      pivotInv k =
        ⅟(higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)) :
    BlockLUFactSpec m r A
      (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
      (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) := by
  exact
    higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_right_inverse
      A pivotInv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_invOf
        A pivotInv hInv hPivotInv)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    `BlockLUFactSpec` for the assembled matrix-product stage factors when the
    supplied pivot inverse is the repository canonical nonsingular inverse of
    every active pivot. -/
theorem higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivotInv_eq_nonsingInv
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv k =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)) :
    BlockLUFactSpec m r A
      (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
      (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) := by
  exact
    higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_right_inverse
      A pivotInv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        A pivotInv hPivotDet hPivotInv)

/-- Product-entry form of the Algorithm 13.3 matrix-stage reconstruction from
    exact pivot right-inverse certificates. -/
theorem higham13_algorithm13_3_matrixStages_product_eq_of_pivot_right_inverse
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    ∀ (i j : Fin m) (s t : Fin r),
      ∑ k : Fin m, ∑ l : Fin r,
        higham13_algorithm13_3_lowerFromMatrixStages A pivotInv i k s l *
          higham13_algorithm13_3_upperFromMatrixStages A pivotInv k j l t =
        A i j s t := by
  exact
    (higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_right_inverse
      A pivotInv hPivotRight).product_eq

/-- Product-entry form of the Algorithm 13.3 matrix-stage reconstruction when
    the supplied pivot inverse is Mathlib's `⅟` for every active pivot. -/
theorem higham13_algorithm13_3_matrixStages_product_eq_of_pivotInv_eq_invOf
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hInv : ∀ k : ℕ, ∀ hk : k < m,
      Invertible
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩))
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      letI : Invertible
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) := hInv k hk
      pivotInv k =
        ⅟(higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)) :
    ∀ (i j : Fin m) (s t : Fin r),
      ∑ k : Fin m, ∑ l : Fin r,
        higham13_algorithm13_3_lowerFromMatrixStages A pivotInv i k s l *
          higham13_algorithm13_3_upperFromMatrixStages A pivotInv k j l t =
        A i j s t := by
  exact
    (higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivotInv_eq_invOf
      A pivotInv hInv hPivotInv).product_eq

/-- Product-entry form of the Algorithm 13.3 matrix-stage reconstruction when
    the supplied pivot inverse is the repository canonical nonsingular inverse
    of every active pivot. -/
theorem higham13_algorithm13_3_matrixStages_product_eq_of_pivotInv_eq_nonsingInv
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv k =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)) :
    ∀ (i j : Fin m) (s t : Fin r),
      ∑ k : Fin m, ∑ l : Fin r,
        higham13_algorithm13_3_lowerFromMatrixStages A pivotInv i k s l *
          higham13_algorithm13_3_upperFromMatrixStages A pivotInv k j l t =
        A i j s t := by
  exact
    (higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivotInv_eq_nonsingInv
      A pivotInv hPivotDet hPivotInv).product_eq

/-- The assembled Algorithm 13.3 matrix-stage lower factor is bounded once each
    stage multiplier is bounded and the common bound also covers the identity
    diagonal. -/
theorem higham13_algorithm13_3_lowerFromMatrixStages_blockMaxNorm_bound
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {C : ℝ}
    (hId : 1 ≤ C)
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv j.val i j *
            pivotInv j.val) ≤ C) :
    blockMaxNorm hm hr
        (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv) ≤ C := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hId
  apply blockMaxNorm_le_of_entry_abs_le
  intro i j s t
  by_cases hji : j.val < i.val
  · exact le_trans
      (by
        simpa [higham13_algorithm13_3_lowerFromMatrixStages, hji] using
          entry_le_maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv j.val i j *
              pivotInv j.val) s t)
      (hLower i j hji)
  · by_cases hij : i = j
    · subst j
      by_cases hst : s = t
      · simpa [higham13_algorithm13_3_lowerFromMatrixStages, hji, idBlock, hst]
          using hId
      · simpa [higham13_algorithm13_3_lowerFromMatrixStages, hji, idBlock, hst,
          abs_of_nonneg hC0] using hC0
    · simpa [higham13_algorithm13_3_lowerFromMatrixStages, hji, hij, zeroBlock,
        abs_of_nonneg hC0] using hC0

/-- Product bound for the assembled matrix-stage Algorithm 13.3 `L` and `U`
    factors.

    This is the full-factor wrapper around
    `higham13_algorithm13_3_lowerFromMatrixStages_blockMaxNorm_bound`: per-stage
    multiplier bounds control the assembled lower factor, while any supplied
    upper-factor bound controls the assembled upper factor. -/
theorem higham13_algorithm13_3_matrixStages_LU_product_bound
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {C_L C_U : ℝ}
    (hId : 1 ≤ C_L)
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv j.val i j *
            pivotInv j.val) ≤ C_L)
    (hUpper :
      blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        C_U) :
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      C_L * C_U := by
  have hL :
      blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv) ≤
        C_L :=
    higham13_algorithm13_3_lowerFromMatrixStages_blockMaxNorm_bound
      hm hr A pivotInv hId hLower
  exact mul_le_mul hL hUpper
    (blockMaxNorm_nonneg hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv))
    (le_trans zero_le_one hId)

/-- The assembled matrix-stage Algorithm 13.3 factors satisfy the standard
    block-LU specification once their block product is known to reconstruct the
    input.  The triangular shape obligations are discharged directly from the
    definitions of `higham13_algorithm13_3_lowerFromMatrixStages` and
    `higham13_algorithm13_3_upperFromMatrixStages`; the remaining hypothesis is
    the genuine Algorithm 13.3 stage-product reconstruction fact. -/
theorem higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_product_eq
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hprod : ∀ (i j : Fin m) (s t : Fin r),
      ∑ k : Fin m, ∑ l : Fin r,
        higham13_algorithm13_3_lowerFromMatrixStages A pivotInv i k s l *
          higham13_algorithm13_3_upperFromMatrixStages A pivotInv k j l t =
        A i j s t) :
    BlockLUFactSpec m r A
      (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
      (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact higham13_algorithm13_3_lowerFromMatrixStages_diag A pivotInv i
  · intro i j hij
    exact higham13_algorithm13_3_lowerFromMatrixStages_upper_zero A pivotInv hij
  · intro i j hji
    exact higham13_algorithm13_3_upperFromMatrixStages_lower_zero A pivotInv hji
  · intro i j s t
    exact hprod i j s t

/-- Product-bound witness theorem for the assembled matrix-stage Algorithm 13.3
    factors.

    This packages the concrete assembled factors behind `BlockLUFactSpec` and
    attaches the existing `L*U` product bound.  It is intentionally conditional
    on the true reconstruction equality for the stage table. -/
theorem higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {C_L C_U : ℝ}
    (hprod : ∀ (i j : Fin m) (s t : Fin r),
      ∑ k : Fin m, ∑ l : Fin r,
        higham13_algorithm13_3_lowerFromMatrixStages A pivotInv i k s l *
          higham13_algorithm13_3_upperFromMatrixStages A pivotInv k j l t =
        A i j s t)
    (hId : 1 ≤ C_L)
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv j.val i j *
            pivotInv j.val) ≤ C_L)
    (hUpper :
      blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        C_U) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r A L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤ C_L * C_U := by
  let L : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_lowerFromMatrixStages A pivotInv
  let U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_upperFromMatrixStages A pivotInv
  refine ⟨L, U, ?_, ?_⟩
  · simpa [L, U] using
      higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_product_eq
        A pivotInv hprod
  · simpa [L, U] using
      higham13_algorithm13_3_matrixStages_LU_product_bound
        hm hr A pivotInv hId hLower hUpper

/-- Product-bound witness theorem for the assembled matrix-stage Algorithm 13.3
    factors from explicit pivot-left-inverse certificates. -/
theorem
    higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound_of_pivot_left_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {C_L C_U : ℝ}
    (hPivotLeft : ∀ k : ℕ, ∀ hk : k < m,
      IsLeftInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hId : 1 ≤ C_L)
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv j.val i j *
            pivotInv j.val) ≤ C_L)
    (hUpper :
      blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        C_U) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r A L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤ C_L * C_U := by
  exact
    higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound
      hm hr A pivotInv
      (higham13_algorithm13_3_matrixStages_product_eq_of_pivot_left_inverse
        A pivotInv hPivotLeft)
      hId hLower hUpper

/-- Product-bound witness theorem for the assembled matrix-stage Algorithm 13.3
    factors from exact pivot right-inverse certificates. -/
theorem
    higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {C_L C_U : ℝ}
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hId : 1 ≤ C_L)
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv j.val i j *
            pivotInv j.val) ≤ C_L)
    (hUpper :
      blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        C_U) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r A L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤ C_L * C_U := by
  exact
    higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound
      hm hr A pivotInv
      (higham13_algorithm13_3_matrixStages_product_eq_of_pivot_right_inverse
        A pivotInv hPivotRight)
      hId hLower hUpper

/-- Product-bound witness theorem for the assembled matrix-stage Algorithm 13.3
    factors when each supplied pivot inverse is Mathlib's `⅟` for the active
    pivot. -/
theorem
    higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound_of_pivotInv_eq_invOf
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {C_L C_U : ℝ}
    (hInv : ∀ k : ℕ, ∀ hk : k < m,
      Invertible
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩))
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      letI : Invertible
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) := hInv k hk
      pivotInv k =
        ⅟(higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩))
    (hId : 1 ≤ C_L)
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv j.val i j *
            pivotInv j.val) ≤ C_L)
    (hUpper :
      blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        C_U) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r A L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤ C_L * C_U := by
  exact
    higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound
      hm hr A pivotInv
      (higham13_algorithm13_3_matrixStages_product_eq_of_pivotInv_eq_invOf
        A pivotInv hInv hPivotInv)
      hId hLower hUpper

/-- Product-bound witness theorem for the assembled matrix-stage Algorithm 13.3
    factors when each supplied pivot inverse is the repository canonical
    nonsingular inverse of the active pivot. -/
theorem
    higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound_of_pivotInv_eq_nonsingInv
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {C_L C_U : ℝ}
    (hPivotDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv k =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩))
    (hId : 1 ≤ C_L)
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv j.val i j *
            pivotInv j.val) ≤ C_L)
    (hUpper :
      blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        C_U) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r A L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤ C_L * C_U := by
  exact
    higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound
      hm hr A pivotInv
      (higham13_algorithm13_3_matrixStages_product_eq_of_pivotInv_eq_nonsingInv
        A pivotInv hPivotDet hPivotInv)
      hId hLower hUpper

end NumStability
