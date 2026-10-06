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
import NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauChain
import NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauProducts.ActiveSuffix
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.RecursiveBudgetChains
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis

/-!
# Source.Higham.Chapter13.Problem04.GlobalTableauProducts.TailChain

This module formalizes the source-facing Chapter 13 statements for
`Problem04.GlobalTableauProducts.TailChain`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    first-split point-row product witness from the fixed-ambient
    global-tableau source chain, with the `rho <= 2` side condition supplied
    by the source-strength product-bound/diagonal-update BDD route.

    The BDD theorem is stated for the uniform flat block matrix.  This wrapper
    transports the matrix-stage growth factor across the first-split/uniform
    representation bridge and then calls the raw global-tableau Eq.13.23
    witness theorem. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa_of_product_bound_diag_update
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
    (hRight :
      IsRightInverse (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ)
    (hDom :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin ((m + 1) + 1),
      invDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hInitInv : ∀ j : Fin ((m + 1) + 1),
      stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < (m + 1) + 1,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < (m + 1) + 1,
      ∀ i j : Fin ((m + 1) + 1),
        k + 1 ≤ i.val → k + 1 ≤ j.val →
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
              ⟨k, hk⟩ *
              pivotInv k *
              higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j) ≤
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
                ⟨k, hk⟩) *
            maxEntryNorm hr (pivotInv k) *
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)))
    (hTail :
      Higham13Eq1322GlobalTableauSourceChain hr hN
        (blockMatrixFirstSplitFlat Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))
        hApos n m (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
        Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
            blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  classical
  let hmTail : 0 < m + 1 := Nat.succ_pos m
  let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  let hSplit : 0 < r + (m + 1) * r := Nat.add_pos_left hr ((m + 1) * r)
  let hFlat : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
  have hSplitPos :
      0 < maxEntryNorm hSplit (blockMatrixFirstSplitFlat Ablk) := by
    simpa [hSplit] using hApos
  have hFlatPos :
      0 < maxEntryNorm hFlat (blockMatrixFlatFin Ablk) := by
    rw [← maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin
      hmTail hr Ablk]
    simpa [hSplit, hFlat] using hSplitPos
  have hRhoFlat :
      growthFactorEntry hFlat (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hFlat hmFull hr Ablk pivotInv) hFlatPos ≤
        2 := by
    simpa [hFlat, hmFull] using
      higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hmFull hr Ablk pivotInv hFlatPos invDiagBound stageInvDiagBound
        hDom hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate
  have hRhoSplitStd :
      growthFactorEntry hSplit (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hSplit hmFull hr Ablk pivotInv) hSplitPos ≤
        2 := by
    have hEq :=
      growthFactorEntry_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin
        (m := m + 1) (r := r) hmTail hr Ablk pivotInv hSplitPos hFlatPos
    rw [hEq]
    exact hRhoFlat
  have hRhoSplit :
      growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hmFull hr Ablk pivotInv) hApos ≤
        2 := by
    simpa [hSplit, hmFull] using hRhoSplitStd
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa
      hr hN Ablk pivotInv hpivot hApos hRight hsn hNn
      hRhoSplit hTail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table version of the first-split global-tableau Eq.13.23
    product witness.

    This is the source-shaped companion to
    `..._of_product_bound_diag_update`: callers may supply the active
    reciprocal pivot table from Theorem 13.7 instead of the scalar pivot-product
    inequality. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal
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
    (hRight :
      IsRightInverse (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ)
    (hDom :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin ((m + 1) + 1),
      invDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hInitInv : ∀ j : Fin ((m + 1) + 1),
      stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < (m + 1) + 1,
      ∀ i j : Fin ((m + 1) + 1),
        k + 1 ≤ i.val → k + 1 ≤ j.val →
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
              ⟨k, hk⟩ *
              pivotInv k *
              higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j) ≤
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
                ⟨k, hk⟩) *
            maxEntryNorm hr (pivotInv k) *
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)))
    (hTail :
      Higham13Eq1322GlobalTableauSourceChain hr hN
        (blockMatrixFirstSplitFlat Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))
        hApos n m (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
        Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
            blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa_of_product_bound_diag_update
      hr hN Ablk pivotInv hpivot hApos hRight hsn hNn
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate hTail

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero first-split product witness from the fixed-ambient
    global-tableau source chain.

    This specializes
    `higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa`
    to the canonical `nonsingInv` ambient inverse, deriving the required exact
    right-inverse certificate from `det A != 0`. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa_of_det_ne_zero
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
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hTail :
      Higham13Eq1322GlobalTableauSourceChain hr hN
        (blockMatrixFirstSplitFlat Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))
        hApos n m (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
        Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
            blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
          (n : ℝ) *
            (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos) ^ 3 *
            (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  exact
    higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa
      hr hN Ablk pivotInv hpivot hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero
        Ablk hdet)
      hsn hNn hTail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero point-row first-split product witness from the
    fixed-ambient global-tableau source chain.

    This is the Eq.13.23 companion to
    `higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa_of_det_ne_zero`;
    the source-side `rho <= 2` proof remains an explicit BDD/product-update
    obligation. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa_of_det_ne_zero
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
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hRho_le_two :
      growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos ≤ 2)
    (hTail :
      Higham13Eq1322GlobalTableauSourceChain hr hN
        (blockMatrixFirstSplitFlat Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))
        hApos n m (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
        Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
            blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa
      hr hN Ablk pivotInv hpivot hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero
        Ablk hdet)
      hsn hNn hRho_le_two hTail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero first-split global-tableau product witness with the
    `rho <= 2` side condition supplied by the source-strength
    product-bound/diagonal-update route.

    This combines the determinant-to-`nonsingInv` right-inverse bridge with
    `..._of_product_bound_diag_update`, so callers do not need to provide a
    separate ambient right-inverse certificate. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
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
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ)
    (hDom :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin ((m + 1) + 1),
      invDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hInitInv : ∀ j : Fin ((m + 1) + 1),
      stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < (m + 1) + 1,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < (m + 1) + 1,
      ∀ i j : Fin ((m + 1) + 1),
        k + 1 ≤ i.val → k + 1 ≤ j.val →
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
              ⟨k, hk⟩ *
              pivotInv k *
              higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j) ≤
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
                ⟨k, hk⟩) *
            maxEntryNorm hr (pivotInv k) *
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)))
    (hTail :
      Higham13Eq1322GlobalTableauSourceChain hr hN
        (blockMatrixFirstSplitFlat Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))
        hApos n m (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
        Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
            blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa_of_product_bound_diag_update
      hr hN Ablk pivotInv hpivot hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero
        Ablk hdet)
      hsn hNn invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hPivotInvBound hProduct hDiagUpdate hTail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero reciprocal-table version of the first-split
    global-tableau product-update witness.

    This is the source-shaped companion to
    `..._of_product_bound_diag_update_of_det_ne_zero`, accepting the active
    reciprocal pivot table instead of the scalar pivot-product bound. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_ne_zero
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
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (invDiagBound : Fin ((m + 1) + 1) → ℝ)
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ)
    (hDom :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin ((m + 1) + 1),
      invDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hInitInv : ∀ j : Fin ((m + 1) + 1),
      stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < (m + 1) + 1,
      ∀ i j : Fin ((m + 1) + 1),
        k + 1 ≤ i.val → k + 1 ≤ j.val →
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
              ⟨k, hk⟩ *
              pivotInv k *
              higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j) ≤
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
                ⟨k, hk⟩) *
            maxEntryNorm hr (pivotInv k) *
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)))
    (hTail :
      Higham13Eq1322GlobalTableauSourceChain hr hN
        (blockMatrixFirstSplitFlat Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))
        hApos n m (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
        Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
            blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal
      hr hN Ablk pivotInv hpivot hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero
        Ablk hdet)
      hsn hNn invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hReciprocal hProduct hDiagUpdate hTail

end NumStability
