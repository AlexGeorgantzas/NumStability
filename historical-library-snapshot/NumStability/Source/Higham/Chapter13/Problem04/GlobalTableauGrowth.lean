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
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Problem04.ActiveStageBounds
import NumStability.Source.Higham.Chapter13.Problem04.BlockInverseBounds
import NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauChain
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStages
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis
import NumStability.Source.Higham.Chapter13.Theorem02.Factorization
import NumStability.Source.Higham.Chapter13.Theorem07.PivotExistence

/-!
# Source.Higham.Chapter13.Problem04.GlobalTableauGrowth

This module formalizes the source-facing Chapter 13 statements for
`Problem04.GlobalTableauGrowth`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    first-split active-suffix global-tableau source obligations supply the
    mixed matrix-`∞`/max-entry upper-factor and finite-history growth endpoint.

    This composes the canonical first-Schur-tail active-suffix source-chain
    constructor with the fixed-ambient global-tableau mixed endpoint.  It
    removes the caller-supplied full global-tableau source-chain certificate
    while keeping the active-suffix source obligations and terminal pivot
    right-inverse datum explicit. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_final_right_inverse_mixed_column_mass
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk))
    (hApos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hsnAll : ∀ {q k : ℕ} (_ : k + (q + 1) ≤ (m + 1) + 1),
      (((q + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hInvSchur : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA22
            (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
              (q + 1) hkq) -
          blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                (q + 1) hkq) *
            ⅟(blockMatrixFirstSplitA11
                (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                  (q + 1) hkq)) *
              blockMatrixFirstSplitA12
                (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                  (q + 1) hkq)))
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 (blockSchur Ablk (pivotInv 0)))
      (blockMatrixFirstSplitA12 (blockSchur Ablk (pivotInv 0)))
      (blockMatrixFirstSplitA21 (blockSchur Ablk (pivotInv 0)))
      (blockMatrixFirstSplitA22 (blockSchur Ablk (pivotInv 0))))]
    (hAinv_tail :
      ∀ i j : Fin r ⊕ Fin (m * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11 (blockSchur Ablk (pivotInv 0)))
            (blockMatrixFirstSplitA12 (blockSchur Ablk (pivotInv 0)))
            (blockMatrixFirstSplitA21 (blockSchur Ablk (pivotInv 0)))
            (blockMatrixFirstSplitA22 (blockSchur Ablk (pivotInv 0)))) :
          Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hFinal :
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)
        (pivotInv (m + 1))) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos (m + 1)) hr Ablk ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
          (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr) (blockMatrixFlatFin Ablk)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)) ≤
        2 := by
  classical
  let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    blockMatrixFirstSplitFlat Ablk
  let G : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hmFull hr Ablk pivotInv
  let Ainv : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    nonsingInv (r + (m + 1) * r) A0
  have hA_le_G : maxEntryNorm hN A0 ≤ maxEntryNorm hN G := by
    exact le_trans
      (by
        simpa [A0] using
          maxEntryNorm_blockMatrixFirstSplitFlat_le_blockMaxNorm_of_hN
            hN (Nat.succ_pos m) hr Ablk)
      (by
        simpa [G, hmFull] using
          higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
            hN hmFull hr Ablk pivotInv)
  have hTail :
      Higham13Eq1322GlobalTableauSourceChain hr hN A0 G Ainv
        hApos n m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) := by
    simpa [A0, G, Ainv, hmFull] using
      Higham13Eq1322GlobalTableauSourceChain.firstSchurTail_activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa
        hr hN A0 Ainv Ablk pivotInv hApos hA_le_G
        hsnAll hInvA11 hInvSchur hpivotAll hAinv_tail
  have hcert :
      Higham13Eq1322GlobalTableauSourceChain hr hN A0 G Ainv
        hApos n (m + 1) Ablk pivotInv := by
    simpa [A0, G, Ainv, hmFull] using
      Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_first_split_exact_kappa
        hr hN Ablk pivotInv hpivot hApos hsn hTail
  simpa [A0, G, Ainv, hmFull] using
    Higham13Eq1322GlobalTableauSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_right_inverse_mixed_column_mass
      hcert invDiagBound hPrefix hDomInf hBound hFinal

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    canonical-terminal-pivot form of the first-split active-suffix
    global-tableau mixed endpoint. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_final_nonsingInv_mixed_column_mass
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk))
    (hApos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hsnAll : ∀ {q k : ℕ} (_ : k + (q + 1) ≤ (m + 1) + 1),
      (((q + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hInvSchur : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA22
            (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
              (q + 1) hkq) -
          blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                (q + 1) hkq) *
            ⅟(blockMatrixFirstSplitA11
                (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                  (q + 1) hkq)) *
              blockMatrixFirstSplitA12
                (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                  (q + 1) hkq)))
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 (blockSchur Ablk (pivotInv 0)))
      (blockMatrixFirstSplitA12 (blockSchur Ablk (pivotInv 0)))
      (blockMatrixFirstSplitA21 (blockSchur Ablk (pivotInv 0)))
      (blockMatrixFirstSplitA22 (blockSchur Ablk (pivotInv 0))))]
    (hAinv_tail :
      ∀ i j : Fin r ⊕ Fin (m * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11 (blockSchur Ablk (pivotInv 0)))
            (blockMatrixFirstSplitA12 (blockSchur Ablk (pivotInv 0)))
            (blockMatrixFirstSplitA21 (blockSchur Ablk (pivotInv 0)))
            (blockMatrixFirstSplitA22 (blockSchur Ablk (pivotInv 0)))) :
          Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hFinalDet :
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
            ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
            ⟨m + 1, Nat.lt_succ_self (m + 1)⟩) ≠ 0)
    (hFinalEq : pivotInv (m + 1) =
      nonsingInv r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos (m + 1)) hr Ablk ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
          (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr) (blockMatrixFlatFin Ablk)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)) ≤
        2 := by
  classical
  let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    blockMatrixFirstSplitFlat Ablk
  let G : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hmFull hr Ablk pivotInv
  let Ainv : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    nonsingInv (r + (m + 1) * r) A0
  have hA_le_G : maxEntryNorm hN A0 ≤ maxEntryNorm hN G := by
    exact le_trans
      (by
        simpa [A0] using
          maxEntryNorm_blockMatrixFirstSplitFlat_le_blockMaxNorm_of_hN
            hN (Nat.succ_pos m) hr Ablk)
      (by
        simpa [G, hmFull] using
          higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
            hN hmFull hr Ablk pivotInv)
  have hTail :
      Higham13Eq1322GlobalTableauSourceChain hr hN A0 G Ainv
        hApos n m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) := by
    simpa [A0, G, Ainv, hmFull] using
      Higham13Eq1322GlobalTableauSourceChain.firstSchurTail_activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa
        hr hN A0 Ainv Ablk pivotInv hApos hA_le_G
        hsnAll hInvA11 hInvSchur hpivotAll hAinv_tail
  have hcert :
      Higham13Eq1322GlobalTableauSourceChain hr hN A0 G Ainv
        hApos n (m + 1) Ablk pivotInv := by
    simpa [A0, G, Ainv, hmFull] using
      Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_first_split_exact_kappa
        hr hN Ablk pivotInv hpivot hApos hsn hTail
  simpa [A0, G, Ainv, hmFull] using
    Higham13Eq1322GlobalTableauSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_nonsingInv_mixed_column_mass
      hcert invDiagBound hPrefix hDomInf hBound hFinalDet hFinalEq

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    parent-inverse-entry handoff form of the first-split active-suffix
    global-tableau mixed endpoint.

    This refines the active-suffix mixed endpoint by deriving the first
    Schur-tail inverse-entry comparison from the parent first-split inverse
    comparison.  The source-level parent comparison remains explicit; the
    separate first-tail comparison premise is no longer required. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_parent_inverse_entry_final_right_inverse_mixed_column_mass
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk))
    (hApos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hsnAll : ∀ {q k : ℕ} (_ : k + (q + 1) ≤ (m + 1) + 1),
      (((q + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hInvSchur : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA22
            (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
              (q + 1) hkq) -
          blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                (q + 1) hkq) *
            ⅟(blockMatrixFirstSplitA11
                (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                  (q + 1) hkq)) *
              blockMatrixFirstSplitA12
                (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                  (q + 1) hkq)))
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hAinv_parent :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11 Ablk)
            (blockMatrixFirstSplitA12 Ablk)
            (blockMatrixFirstSplitA21 Ablk)
            (blockMatrixFirstSplitA22 Ablk)) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hFinal :
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)
        (pivotInv (m + 1))) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos (m + 1)) hr Ablk ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
          (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr) (blockMatrixFlatFin Ablk)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)) ≤
        2 := by
  classical
  let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    blockMatrixFirstSplitFlat Ablk
  let G : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hmFull hr Ablk pivotInv
  let Ainv : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    nonsingInv (r + (m + 1) * r) A0
  have hA_le_G : maxEntryNorm hN A0 ≤ maxEntryNorm hN G := by
    exact le_trans
      (by
        simpa [A0] using
          maxEntryNorm_blockMatrixFirstSplitFlat_le_blockMaxNorm_of_hN
            hN (Nat.succ_pos m) hr Ablk)
      (by
        simpa [G, hmFull] using
          higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
            hN hmFull hr Ablk pivotInv)
  have hTail :
      Higham13Eq1322GlobalTableauSourceChain hr hN A0 G Ainv
        hApos n m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) := by
    simpa [A0, G, Ainv, hmFull] using
      Higham13Eq1322GlobalTableauSourceChain.firstSchurTail_activeSuffix_from_matrix_stage_history_with_parent_inverse_entry_exact_kappa
        hr hN A0 Ainv Ablk pivotInv hApos hA_le_G hpivot
        hsnAll hInvA11 hInvSchur hpivotAll hAinv_parent
  have hcert :
      Higham13Eq1322GlobalTableauSourceChain hr hN A0 G Ainv
        hApos n (m + 1) Ablk pivotInv := by
    simpa [A0, G, Ainv, hmFull] using
      Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_first_split_exact_kappa
        hr hN Ablk pivotInv hpivot hApos hsn hTail
  simpa [A0, G, Ainv, hmFull] using
    Higham13Eq1322GlobalTableauSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_right_inverse_mixed_column_mass
      hcert invDiagBound hPrefix hDomInf hBound hFinal

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    canonical-terminal-pivot form of the parent-inverse-entry active-suffix
    global-tableau mixed endpoint. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_parent_inverse_entry_final_nonsingInv_mixed_column_mass
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk))
    (hApos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hsnAll : ∀ {q k : ℕ} (_ : k + (q + 1) ≤ (m + 1) + 1),
      (((q + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hInvSchur : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA22
            (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
              (q + 1) hkq) -
          blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                (q + 1) hkq) *
            ⅟(blockMatrixFirstSplitA11
                (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                  (q + 1) hkq)) *
              blockMatrixFirstSplitA12
                (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                  (q + 1) hkq)))
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hAinv_parent :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11 Ablk)
            (blockMatrixFirstSplitA12 Ablk)
            (blockMatrixFirstSplitA21 Ablk)
            (blockMatrixFirstSplitA22 Ablk)) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hFinalDet :
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
            ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
            ⟨m + 1, Nat.lt_succ_self (m + 1)⟩) ≠ 0)
    (hFinalEq : pivotInv (m + 1) =
      nonsingInv r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos (m + 1)) hr Ablk ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
          (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr) (blockMatrixFlatFin Ablk)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)) ≤
        2 := by
  classical
  let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    blockMatrixFirstSplitFlat Ablk
  let G : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hmFull hr Ablk pivotInv
  let Ainv : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    nonsingInv (r + (m + 1) * r) A0
  have hA_le_G : maxEntryNorm hN A0 ≤ maxEntryNorm hN G := by
    exact le_trans
      (by
        simpa [A0] using
          maxEntryNorm_blockMatrixFirstSplitFlat_le_blockMaxNorm_of_hN
            hN (Nat.succ_pos m) hr Ablk)
      (by
        simpa [G, hmFull] using
          higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
            hN hmFull hr Ablk pivotInv)
  have hTail :
      Higham13Eq1322GlobalTableauSourceChain hr hN A0 G Ainv
        hApos n m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) := by
    simpa [A0, G, Ainv, hmFull] using
      Higham13Eq1322GlobalTableauSourceChain.firstSchurTail_activeSuffix_from_matrix_stage_history_with_parent_inverse_entry_exact_kappa
        hr hN A0 Ainv Ablk pivotInv hApos hA_le_G hpivot
        hsnAll hInvA11 hInvSchur hpivotAll hAinv_parent
  have hcert :
      Higham13Eq1322GlobalTableauSourceChain hr hN A0 G Ainv
        hApos n (m + 1) Ablk pivotInv := by
    simpa [A0, G, Ainv, hmFull] using
      Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_first_split_exact_kappa
        hr hN Ablk pivotInv hpivot hApos hsn hTail
  simpa [A0, G, Ainv, hmFull] using
    Higham13Eq1322GlobalTableauSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_nonsingInv_mixed_column_mass
      hcert invDiagBound hPrefix hDomInf hBound hFinalDet hFinalEq

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    canonical-parent inverse-entry handoff form of the active-suffix
    global-tableau mixed endpoint.

    This specializes the parent-inverse-entry mixed endpoint by deriving the
    parent comparison from the canonical ambient `nonsingInv` of the first
    split flat matrix. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_canonical_parent_inverse_entry_final_right_inverse_mixed_column_mass
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk))
    (hApos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hsnAll : ∀ {q k : ℕ} (_ : k + (q + 1) ≤ (m + 1) + 1),
      (((q + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hInvSchur : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA22
            (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
              (q + 1) hkq) -
          blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                (q + 1) hkq) *
            ⅟(blockMatrixFirstSplitA11
                (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                  (q + 1) hkq)) *
              blockMatrixFirstSplitA12
                (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                  (q + 1) hkq)))
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hFinal :
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)
        (pivotInv (m + 1))) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos (m + 1)) hr Ablk ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
          (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr) (blockMatrixFlatFin Ablk)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)) ≤
        2 := by
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_parent_inverse_entry_final_right_inverse_mixed_column_mass
      hr hN Ablk pivotInv hpivot hApos hsn hsnAll hInvA11 hInvSchur
      hpivotAll
      (higham13_problem13_4_firstSplit_parent_inverse_entry_bound_from_nonsingInv
        hN Ablk)
      invDiagBound hPrefix hDomInf hBound hFinal

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    canonical-terminal-pivot form of the canonical-parent active-suffix
    global-tableau mixed endpoint. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_canonical_parent_inverse_entry_final_nonsingInv_mixed_column_mass
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk))
    (hApos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hsnAll : ∀ {q k : ℕ} (_ : k + (q + 1) ≤ (m + 1) + 1),
      (((q + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hInvSchur : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA22
            (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
              (q + 1) hkq) -
          blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                (q + 1) hkq) *
            ⅟(blockMatrixFirstSplitA11
                (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                  (q + 1) hkq)) *
              blockMatrixFirstSplitA12
                (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                  (q + 1) hkq)))
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hFinalDet :
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
            ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
            ⟨m + 1, Nat.lt_succ_self (m + 1)⟩) ≠ 0)
    (hFinalEq : pivotInv (m + 1) =
      nonsingInv r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos (m + 1)) hr Ablk ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
          (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr) (blockMatrixFlatFin Ablk)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)) ≤
        2 := by
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_parent_inverse_entry_final_nonsingInv_mixed_column_mass
      hr hN Ablk pivotInv hpivot hApos hsn hsnAll hInvA11 hInvSchur
      hpivotAll
      (higham13_problem13_4_firstSplit_parent_inverse_entry_bound_from_nonsingInv
        hN Ablk)
      invDiagBound hPrefix hDomInf hBound hFinalDet hFinalEq

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    determinant-table/canonical-parent active-suffix global-tableau mixed
    endpoint with an explicit final right-inverse certificate.

    The determinant tables derive the active-suffix full-tail, pivot-block, and
    Schur-complement invertibility instances internally; the pivot-identity
    table remains a source obligation. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_canonical_parent_inverse_entry_of_det_tables_final_right_inverse_mixed_column_mass
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk))
    (hApos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hFulln : (((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hDetFull : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      Matrix.det (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))) ≠ 0)
    (hDetA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Matrix.det
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)) ≠ 0)
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      [Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq))] →
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hFinal :
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)
        (pivotInv (m + 1))) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos (m + 1)) hr Ablk ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
          (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr) (blockMatrixFlatFin Ablk)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)) ≤
        2 := by
  classical
  let hsnAll : ∀ {q k : ℕ} (_ : k + (q + 1) ≤ (m + 1) + 1),
      (((q + 1) * r : ℕ) : ℝ) ≤ (n : ℝ) := by
    intro q k hkq
    exact higham13_activeSuffix_dimension_budget_of_global_bound hFulln hkq
  let hInvFull : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))) := by
    intro q k hkq
    let T : Matrix (Fin r ⊕ Fin (q * r)) (Fin r ⊕ Fin (q * r)) ℝ :=
      Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
    letI : Invertible (Matrix.det T) := invertibleOfNonzero (by
      simpa [T] using hDetFull (q := q) (k := k) hkq)
    simpa [T] using Matrix.invertibleOfDetInvertible T
  let hInvA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)) := by
    intro q k hkq
    let A11 : Matrix (Fin r) (Fin r) ℝ :=
      blockMatrixFirstSplitA11
        (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
          (q + 1) hkq)
    letI : Invertible (Matrix.det A11) := invertibleOfNonzero (by
      simpa [A11] using hDetA11 (q := q) (k := k) hkq)
    simpa [A11] using Matrix.invertibleOfDetInvertible A11
  let hInvSchur : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA22
            (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
              (q + 1) hkq) -
          blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                (q + 1) hkq) *
            ⅟(blockMatrixFirstSplitA11
                (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                  (q + 1) hkq)) *
              blockMatrixFirstSplitA12
                (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                  (q + 1) hkq)) := by
    intro q k hkq
    let Tail :=
      higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
        (q + 1) hkq
    let A11 := blockMatrixFirstSplitA11 Tail
    let A12 := blockMatrixFirstSplitA12 Tail
    let A21 := blockMatrixFirstSplitA21 Tail
    let A22 := blockMatrixFirstSplitA22 Tail
    letI : Invertible A11 := by
      simpa [Tail, A11] using hInvA11 (q := q) (k := k) hkq
    letI : Invertible (Matrix.fromBlocks A11 A12 A21 A22) := by
      simpa [Tail, A11, A12, A21, A22] using
        hInvFull (q := q + 1) (k := k) hkq
    simpa [Tail, A11, A12, A21, A22] using
      Matrix.invertibleOfFromBlocks₁₁Invertible A11 A12 A21 A22
  let hpivotAll' : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)) := by
    intro q k hkq
    letI : Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)) :=
      hInvA11 (q := q) (k := k) hkq
    exact hpivotAll hkq
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_canonical_parent_inverse_entry_final_right_inverse_mixed_column_mass
      hr hN Ablk pivotInv hpivot hApos hsn hsnAll hInvA11 hInvSchur
      hpivotAll' invDiagBound hPrefix hDomInf hBound hFinal

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    canonical-terminal-pivot form of the determinant-table/canonical-parent
    active-suffix global-tableau mixed endpoint. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_canonical_parent_inverse_entry_of_det_tables_final_nonsingInv_mixed_column_mass
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk))
    (hApos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hFulln : (((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hDetFull : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      Matrix.det (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))) ≠ 0)
    (hDetA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Matrix.det
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)) ≠ 0)
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      [Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq))] →
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hFinalDet :
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
            ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
            ⟨m + 1, Nat.lt_succ_self (m + 1)⟩) ≠ 0)
    (hFinalEq : pivotInv (m + 1) =
      nonsingInv r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos (m + 1)) hr Ablk ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
          (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr) (blockMatrixFlatFin Ablk)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)) ≤
        2 := by
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_canonical_parent_inverse_entry_of_det_tables_final_right_inverse_mixed_column_mass
      hr hN Ablk pivotInv hpivot hApos hsn hFulln hDetFull hDetA11
      hpivotAll invDiagBound hPrefix hDomInf hBound
      (by
        simpa [hFinalEq] using
          (isInverse_nonsingInv_of_det_ne_zero r
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv
              (m + 1) ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
              ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)
            hFinalDet).2)

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    BDD-initial-pivot form of the active-suffix global-tableau mixed endpoint.

    This wrapper derives the first pivot identity
    `pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk)` from the BDD canonical
    `nonsingInv` certificate and then uses the canonical-parent mixed endpoint.
    The remaining active-suffix pivot/Schur source obligations stay explicit. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_initial_pivot_nonsingInv_bdd_final_right_inverse_mixed_column_mass
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hApos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hsnAll : ∀ {q k : ℕ} (_ : k + (q + 1) ≤ (m + 1) + 1),
      (((q + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hInvSchur : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA22
            (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
              (q + 1) hkq) -
          blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                (q + 1) hkq) *
            ⅟(blockMatrixFirstSplitA11
                (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                  (q + 1) hkq)) *
              blockMatrixFirstSplitA12
                (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                  (q + 1) hkq)))
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hFinal :
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)
        (pivotInv (m + 1))) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos (m + 1)) hr Ablk ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
          (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr) (blockMatrixFlatFin Ablk)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)) ≤
        2 := by
  have hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk) :=
    higham13_algorithm13_3_initial_pivot_eq_invOf_blockMatrixFirstSplitA11_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
      Ablk pivotInv invDiagBound hPrefix
      (higham13_blockDiagDomCol_piNorm_of_infNorm hr Ablk invDiagBound hDomInf)
      hBound hPivot0
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_canonical_parent_inverse_entry_final_right_inverse_mixed_column_mass
      hr hN Ablk pivotInv hpivot hApos hsn hsnAll hInvA11 hInvSchur
      hpivotAll invDiagBound hPrefix hDomInf hBound hFinal

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    canonical-terminal-pivot form of the BDD-initial-pivot active-suffix
    global-tableau mixed endpoint. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_initial_pivot_nonsingInv_bdd_final_nonsingInv_mixed_column_mass
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hApos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hsnAll : ∀ {q k : ℕ} (_ : k + (q + 1) ≤ (m + 1) + 1),
      (((q + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hInvSchur : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA22
            (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
              (q + 1) hkq) -
          blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                (q + 1) hkq) *
            ⅟(blockMatrixFirstSplitA11
                (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                  (q + 1) hkq)) *
              blockMatrixFirstSplitA12
                (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
                  (q + 1) hkq)))
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hFinalDet :
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
            ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
            ⟨m + 1, Nat.lt_succ_self (m + 1)⟩) ≠ 0)
    (hFinalEq : pivotInv (m + 1) =
      nonsingInv r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos (m + 1)) hr Ablk ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
          (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr) (blockMatrixFlatFin Ablk)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)) ≤
        2 := by
  have hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk) :=
    higham13_algorithm13_3_initial_pivot_eq_invOf_blockMatrixFirstSplitA11_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
      Ablk pivotInv invDiagBound hPrefix
      (higham13_blockDiagDomCol_piNorm_of_infNorm hr Ablk invDiagBound hDomInf)
      hBound hPivot0
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_canonical_parent_inverse_entry_final_nonsingInv_mixed_column_mass
      hr hN Ablk pivotInv hpivot hApos hsn hsnAll hInvA11 hInvSchur
      hpivotAll invDiagBound hPrefix hDomInf hBound hFinalDet hFinalEq

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    determinant-table form of the first-split active-suffix global-tableau
    mixed endpoint.

    This wrapper uses the determinant-table first-Schur-tail source-chain
    constructor to derive the active-suffix invertibility instances internally.
    The genuine source-side pivot identities and inverse-entry comparison table
    remain explicit. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_det_tables_final_right_inverse_mixed_column_mass
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk))
    (hApos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hFulln : (((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hDetFull : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      Matrix.det (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))) ≠ 0)
    (hDetA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Matrix.det
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)) ≠ 0)
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      [Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq))] →
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hAinvEntryAll : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq)))] →
      ∀ i j : Fin r ⊕ Fin (q * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))) :
          Matrix (Fin r ⊕ Fin (q * r)) (Fin r ⊕ Fin (q * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hFinal :
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)
        (pivotInv (m + 1))) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos (m + 1)) hr Ablk ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
          (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr) (blockMatrixFlatFin Ablk)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)) ≤
        2 := by
  classical
  let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    blockMatrixFirstSplitFlat Ablk
  let G : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hmFull hr Ablk pivotInv
  let Ainv : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    nonsingInv (r + (m + 1) * r) A0
  have hA_le_G : maxEntryNorm hN A0 ≤ maxEntryNorm hN G := by
    exact le_trans
      (by
        simpa [A0] using
          maxEntryNorm_blockMatrixFirstSplitFlat_le_blockMaxNorm_of_hN
            hN (Nat.succ_pos m) hr Ablk)
      (by
        simpa [G, hmFull] using
          higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
            hN hmFull hr Ablk pivotInv)
  have hTail :
      Higham13Eq1322GlobalTableauSourceChain hr hN A0 G Ainv
        hApos n m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) := by
    simpa [A0, G, Ainv, hmFull] using
      Higham13Eq1322GlobalTableauSourceChain.firstSchurTail_activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_global_dimension_bound_of_det_tables
        hr hN A0 Ainv Ablk pivotInv hApos hA_le_G hFulln
        hDetFull hDetA11 hpivotAll hAinvEntryAll
  have hcert :
      Higham13Eq1322GlobalTableauSourceChain hr hN A0 G Ainv
        hApos n (m + 1) Ablk pivotInv := by
    simpa [A0, G, Ainv, hmFull] using
      Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_first_split_exact_kappa
        hr hN Ablk pivotInv hpivot hApos hsn hTail
  simpa [A0, G, Ainv, hmFull] using
    Higham13Eq1322GlobalTableauSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_right_inverse_mixed_column_mass
      hcert invDiagBound hPrefix hDomInf hBound hFinal

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    canonical-terminal-pivot form of the determinant-table active-suffix
    global-tableau mixed endpoint. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_det_tables_final_nonsingInv_mixed_column_mass
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk))
    (hApos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hFulln : (((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hDetFull : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      Matrix.det (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))) ≠ 0)
    (hDetA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Matrix.det
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)) ≠ 0)
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      [Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq))] →
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hAinvEntryAll : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq)))] →
      ∀ i j : Fin r ⊕ Fin (q * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))) :
          Matrix (Fin r ⊕ Fin (q * r)) (Fin r ⊕ Fin (q * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hFinalDet :
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
            ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
            ⟨m + 1, Nat.lt_succ_self (m + 1)⟩) ≠ 0)
    (hFinalEq : pivotInv (m + 1) =
      nonsingInv r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos (m + 1)) hr Ablk ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
          (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr) (blockMatrixFlatFin Ablk)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)) ≤
        2 := by
  classical
  let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    blockMatrixFirstSplitFlat Ablk
  let G : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hmFull hr Ablk pivotInv
  let Ainv : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    nonsingInv (r + (m + 1) * r) A0
  have hA_le_G : maxEntryNorm hN A0 ≤ maxEntryNorm hN G := by
    exact le_trans
      (by
        simpa [A0] using
          maxEntryNorm_blockMatrixFirstSplitFlat_le_blockMaxNorm_of_hN
            hN (Nat.succ_pos m) hr Ablk)
      (by
        simpa [G, hmFull] using
          higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
            hN hmFull hr Ablk pivotInv)
  have hTail :
      Higham13Eq1322GlobalTableauSourceChain hr hN A0 G Ainv
        hApos n m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) := by
    simpa [A0, G, Ainv, hmFull] using
      Higham13Eq1322GlobalTableauSourceChain.firstSchurTail_activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_global_dimension_bound_of_det_tables
        hr hN A0 Ainv Ablk pivotInv hApos hA_le_G hFulln
        hDetFull hDetA11 hpivotAll hAinvEntryAll
  have hcert :
      Higham13Eq1322GlobalTableauSourceChain hr hN A0 G Ainv
        hApos n (m + 1) Ablk pivotInv := by
    simpa [A0, G, Ainv, hmFull] using
      Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_first_split_exact_kappa
        hr hN Ablk pivotInv hpivot hApos hsn hTail
  simpa [A0, G, Ainv, hmFull] using
    Higham13Eq1322GlobalTableauSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_nonsingInv_mixed_column_mass
      hcert invDiagBound hPrefix hDomInf hBound hFinalDet hFinalEq

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    determinant-table/BDD-initial-pivot form of the active-suffix
    global-tableau mixed endpoint. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_initial_pivot_nonsingInv_bdd_of_det_tables_final_right_inverse_mixed_column_mass
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hApos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hFulln : (((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hDetFull : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      Matrix.det (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))) ≠ 0)
    (hDetA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Matrix.det
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)) ≠ 0)
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      [Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq))] →
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hAinvEntryAll : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq)))] →
      ∀ i j : Fin r ⊕ Fin (q * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))) :
          Matrix (Fin r ⊕ Fin (q * r)) (Fin r ⊕ Fin (q * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
    (hFinal :
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)
        (pivotInv (m + 1))) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos (m + 1)) hr Ablk ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
          (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr) (blockMatrixFlatFin Ablk)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)) ≤
        2 := by
  have hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk) :=
    higham13_algorithm13_3_initial_pivot_eq_invOf_blockMatrixFirstSplitA11_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
      Ablk pivotInv invDiagBound hPrefix
      (higham13_blockDiagDomCol_piNorm_of_infNorm hr Ablk invDiagBound hDomInf)
      hBound hPivot0
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_det_tables_final_right_inverse_mixed_column_mass
      hr hN Ablk pivotInv hpivot hApos hsn hFulln hDetFull hDetA11
      hpivotAll hAinvEntryAll invDiagBound hPrefix hDomInf hBound hFinal

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    canonical-terminal-pivot form of the determinant-table/BDD-initial-pivot
    active-suffix global-tableau mixed endpoint. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_initial_pivot_nonsingInv_bdd_of_det_tables_final_nonsingInv_mixed_column_mass
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hApos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hFulln : (((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hDetFull : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      Matrix.det (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))) ≠ 0)
    (hDetA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Matrix.det
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)) ≠ 0)
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      [Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq))] →
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hAinvEntryAll : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq)))] →
      ∀ i j : Fin r ⊕ Fin (q * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))) :
          Matrix (Fin r ⊕ Fin (q * r)) (Fin r ⊕ Fin (q * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
    (hFinalDet :
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
            ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
            ⟨m + 1, Nat.lt_succ_self (m + 1)⟩) ≠ 0)
    (hFinalEq : pivotInv (m + 1) =
      nonsingInv r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos (m + 1)) hr Ablk ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
          (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr) (blockMatrixFlatFin Ablk)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)) ≤
        2 := by
  have hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk) :=
    higham13_algorithm13_3_initial_pivot_eq_invOf_blockMatrixFirstSplitA11_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
      Ablk pivotInv invDiagBound hPrefix
      (higham13_blockDiagDomCol_piNorm_of_infNorm hr Ablk invDiagBound hDomInf)
      hBound hPivot0
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_det_tables_final_nonsingInv_mixed_column_mass
      hr hN Ablk pivotInv hpivot hApos hsn hFulln hDetFull hDetA11
      hpivotAll hAinvEntryAll invDiagBound hPrefix hDomInf hBound
      hFinalDet hFinalEq

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    determinant-table active-suffix mixed endpoint with the first-split
    positivity witness derived from the all-leading-prefix table. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_det_tables_prefix_pos_final_right_inverse_mixed_column_mass
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hFulln : (((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hDetFull : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      Matrix.det (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))) ≠ 0)
    (hDetA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Matrix.det
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)) ≠ 0)
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      [Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq))] →
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hAinvEntryAll : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq)))] →
      ∀ i j : Fin r ⊕ Fin (q * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))) :
          Matrix (Fin r ⊕ Fin (q * r)) (Fin r ⊕ Fin (q * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hFinal :
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)
        (pivotInv (m + 1))) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos (m + 1)) hr Ablk ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
          (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr) (blockMatrixFlatFin Ablk)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)) ≤
        2 := by
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_det_tables_final_right_inverse_mixed_column_mass
      hr hN Ablk pivotInv hpivot
      (maxEntryNorm_blockMatrixFirstSplitFlat_pos_of_all_leadingBlockPrefixes
        (m := m + 1) (r := r) hN Ablk hPrefix)
      hsn hFulln hDetFull hDetA11 hpivotAll hAinvEntryAll invDiagBound
      hPrefix hDomInf hBound hFinal

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    canonical-terminal-pivot determinant-table mixed endpoint with the
    first-split positivity witness derived from the all-leading-prefix table. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_det_tables_prefix_pos_final_nonsingInv_mixed_column_mass
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hFulln : (((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hDetFull : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      Matrix.det (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))) ≠ 0)
    (hDetA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Matrix.det
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)) ≠ 0)
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      [Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq))] →
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hAinvEntryAll : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq)))] →
      ∀ i j : Fin r ⊕ Fin (q * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))) :
          Matrix (Fin r ⊕ Fin (q * r)) (Fin r ⊕ Fin (q * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hFinalDet :
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
            ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
            ⟨m + 1, Nat.lt_succ_self (m + 1)⟩) ≠ 0)
    (hFinalEq : pivotInv (m + 1) =
      nonsingInv r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos (m + 1)) hr Ablk ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
          (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr) (blockMatrixFlatFin Ablk)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)) ≤
        2 := by
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_det_tables_final_nonsingInv_mixed_column_mass
      hr hN Ablk pivotInv hpivot
      (maxEntryNorm_blockMatrixFirstSplitFlat_pos_of_all_leadingBlockPrefixes
        (m := m + 1) (r := r) hN Ablk hPrefix)
      hsn hFulln hDetFull hDetA11 hpivotAll hAinvEntryAll invDiagBound
      hPrefix hDomInf hBound hFinalDet hFinalEq

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    BDD-initial-pivot/determinant-table mixed endpoint with the first-split
    positivity witness derived from the all-leading-prefix table. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_initial_pivot_nonsingInv_bdd_of_det_tables_prefix_pos_final_right_inverse_mixed_column_mass
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hFulln : (((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hDetFull : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      Matrix.det (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))) ≠ 0)
    (hDetA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Matrix.det
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)) ≠ 0)
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      [Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq))] →
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hAinvEntryAll : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq)))] →
      ∀ i j : Fin r ⊕ Fin (q * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))) :
          Matrix (Fin r ⊕ Fin (q * r)) (Fin r ⊕ Fin (q * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
    (hFinal :
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)
        (pivotInv (m + 1))) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos (m + 1)) hr Ablk ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
          (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr) (blockMatrixFlatFin Ablk)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)) ≤
        2 := by
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_initial_pivot_nonsingInv_bdd_of_det_tables_final_right_inverse_mixed_column_mass
      hr hN Ablk pivotInv invDiagBound hPrefix hDomInf hBound hPivot0
      (maxEntryNorm_blockMatrixFirstSplitFlat_pos_of_all_leadingBlockPrefixes
        (m := m + 1) (r := r) hN Ablk hPrefix)
      hsn hFulln hDetFull hDetA11 hpivotAll hAinvEntryAll hFinal

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    canonical-terminal-pivot BDD-initial-pivot/determinant-table mixed
    endpoint with the first-split positivity witness derived from the
    all-leading-prefix table. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_initial_pivot_nonsingInv_bdd_of_det_tables_prefix_pos_final_nonsingInv_mixed_column_mass
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hFulln : (((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hDetFull : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      Matrix.det (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))) ≠ 0)
    (hDetA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Matrix.det
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)) ≠ 0)
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      [Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq))] →
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k
            (q + 1) hkq)))
    (hAinvEntryAll : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq)))] →
      ∀ i j : Fin r ⊕ Fin (q * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv k q hkq))) :
          Matrix (Fin r ⊕ Fin (q * r)) (Fin r ⊕ Fin (q * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
    (hFinalDet :
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
            ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
            ⟨m + 1, Nat.lt_succ_self (m + 1)⟩) ≠ 0)
    (hFinalEq : pivotInv (m + 1) =
      nonsingInv r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (m + 1)
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
          ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos (m + 1)) hr Ablk ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
          (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr)
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos (m + 1)) hr) (blockMatrixFlatFin Ablk)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)) ≤
        2 := by
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_global_tableau_activeSuffix_matrix_stage_history_of_initial_pivot_nonsingInv_bdd_of_det_tables_final_nonsingInv_mixed_column_mass
      hr hN Ablk pivotInv invDiagBound hPrefix hDomInf hBound hPivot0
      (maxEntryNorm_blockMatrixFirstSplitFlat_pos_of_all_leadingBlockPrefixes
        (m := m + 1) (r := r) hN Ablk hPrefix)
      hsn hFulln hDetFull hDetA11 hpivotAll hAinvEntryAll
      hFinalDet hFinalEq

end NumStability
