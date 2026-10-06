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
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStages
import NumStability.Source.Higham.Chapter13.Problem04.RecursiveBudgetChains
import NumStability.Source.Higham.Chapter13.Section01.NormConventions
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis
import NumStability.Source.Higham.Chapter13.Theorem02.Factorization
import NumStability.Source.Higham.Chapter13.Theorem07.PivotExistence

/-!
# Source.Higham.Chapter13.Problem04.GlobalTableauProducts.DiagonalUpdate

This module formalizes the source-facing Chapter 13 statements for
`Problem04.GlobalTableauProducts.DiagonalUpdate`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    first-split matrix-stage growth factor bound from the product-bound and
    diagonal-update BDD source data.

    The source-strength BDD theorem is stated for the uniform flat block matrix.
    This helper transports that `rho <= 2` certificate to the first-split flat
    representation used by the global-tableau Eq.13.23 wrappers. -/
theorem
    higham13_algorithm13_3_firstSplitStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
    {m r : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk))
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
      (fun k => maxEntryNorm hr (pivotInv k))) :
    growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos ≤
      2 := by
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
  simpa [hSplit, hmFull] using hRhoSplitStd

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table form of the first-split product-update `rho <= 2` bridge. -/
theorem
    higham13_algorithm13_3_firstSplitStageHistoryGrowthFactor_le_two_of_product_bound_diag_update_reciprocal
    {m r : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk))
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
      (fun k => maxEntryNorm hr (pivotInv k))) :
    growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos ≤
      2 := by
  exact
    higham13_algorithm13_3_firstSplitStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
      hr hN Ablk pivotInv hApos invDiagBound stageInvDiagBound hDom
      hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    first-split active-suffix point-row product witness whose `rho <= 2` side
    condition is supplied by the source-strength product-bound/diagonal-update
    BDD route. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update
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
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) :
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
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa
      hr hN Ablk pivotInv hpivot hApos hRight hsn hNn
      (higham13_algorithm13_3_firstSplitStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hr hN Ablk pivotInv hApos invDiagBound stageInvDiagBound hDom
        hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate)
      hsnAll hInvA11 hInvSchur hpivotAll hAinv_tail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table version of the active-suffix first-split Eq.13.23
    product-update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal
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
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) :
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
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update
      hr hN Ablk pivotInv hpivot hApos hRight hsn hNn
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate hsnAll hInvA11 hInvSchur hpivotAll hAinv_tail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    canonical-parent version of the active-suffix first-split Eq.13.23
    product-update witness.

    This composes the source-strength product-bound/diagonal-update proof of
    `rho <= 2` with the canonical parent inverse-entry handoff, so callers no
    longer need to supply the first Schur-tail inverse-entry comparison
    separately. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_canonical_parent_inverse_entry
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
            (q + 1) hkq))) :
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
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_canonical_parent_inverse_entry
      hr hN Ablk pivotInv hpivot hApos hRight hsn hNn
      (higham13_algorithm13_3_firstSplitStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hr hN Ablk pivotInv hApos invDiagBound stageInvDiagBound hDom
        hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate)
      hsnAll hInvA11 hInvSchur hpivotAll

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table/canonical-parent version of the active-suffix first-split
    Eq.13.23 product-update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal_of_canonical_parent_inverse_entry
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
            (q + 1) hkq))) :
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
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_canonical_parent_inverse_entry
      hr hN Ablk pivotInv hpivot hApos hRight hsn hNn
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate hsnAll hInvA11 hInvSchur hpivotAll

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero canonical-parent version of the active-suffix
    first-split Eq.13.23 product-update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_canonical_parent_inverse_entry_of_det_ne_zero
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
            (q + 1) hkq))) :
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
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_canonical_parent_inverse_entry
      hr hN Ablk pivotInv hpivot hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero
        Ablk hdet)
      hsn hNn invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hPivotInvBound hProduct hDiagUpdate hsnAll hInvA11 hInvSchur hpivotAll

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero reciprocal-table/canonical-parent version of the
    active-suffix first-split Eq.13.23 product-update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal_of_canonical_parent_inverse_entry_of_det_ne_zero
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
            (q + 1) hkq))) :
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
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal_of_canonical_parent_inverse_entry
      hr hN Ablk pivotInv hpivot hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero
        Ablk hdet)
      hsn hNn invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hReciprocal hProduct hDiagUpdate hsnAll hInvA11 hInvSchur hpivotAll

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    max-entry BDD/canonical-parent version of the determinant-nonzero
    active-suffix product-update witness.

    This derives the initial pivot identity, first-split positivity,
    determinant nonsingularity, and diagonal-bound premise from the
    all-leading-prefix and max-entry BDD hypotheses, while using the
    canonical-parent inverse-entry handoff.  Thus it avoids the first-tail
    inverse-entry comparison at this consumer surface. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_bdd_of_product_bound_diag_update_of_canonical_parent_inverse_entry_of_det_ne_zero
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
    (hDom :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ)
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
            (q + 1) hkq))) :
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
  have hDomPi :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j => ‖(fun a b => Ablk i j a b : Fin r → Fin r → ℝ)‖)
        invDiagBound := by
    simpa [higham13_block_norm_eq_maxEntryNorm hr] using hDom
  have hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk) := by
    simpa using
      higham13_algorithm13_3_initial_pivot_eq_invOf_blockMatrixFirstSplitA11_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
        (fun i j a b => Ablk i j a b) pivotInv invDiagBound
        hPrefix hDomPi hBound hPivot0
  have hApos :
      0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk) :=
    maxEntryNorm_blockMatrixFirstSplitFlat_pos_of_all_leadingBlockPrefixes
      (m := m + 1) (r := r) hN Ablk hPrefix
  have hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0 :=
    det_ne_zero_blockMatrixFirstSplitFlat_of_blockMatrixFlatFin Ablk
      (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
        (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)
  have hDiagBound : ∀ j : Fin ((m + 1) + 1),
      invDiagBound j ≤ maxEntryNorm hr (Ablk j j) := by
    intro j
    exact le_trans (hBound j) (maxEntryNorm_nonneg hr (Ablk j j))
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_canonical_parent_inverse_entry_of_det_ne_zero
      hr hN Ablk pivotInv hpivot hApos hdet hsn hNn
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hPivotInvBound hProduct hDiagUpdate hsnAll hInvA11 hInvSchur hpivotAll

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table companion to the max-entry BDD/canonical-parent
    determinant-nonzero active-suffix product-update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_bdd_of_product_bound_diag_update_reciprocal_of_canonical_parent_inverse_entry_of_det_ne_zero
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
    (hDom :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ)
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
            (q + 1) hkq))) :
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
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_bdd_of_product_bound_diag_update_of_canonical_parent_inverse_entry_of_det_ne_zero
      hr hN Ablk pivotInv invDiagBound hPrefix hDom hBound hPivot0
      hsn hNn stageInvDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate hsnAll hInvA11 hInvSchur hpivotAll

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    matrix-`∞` BDD/canonical-parent version of the active-suffix first-split
    product-update witness.

    This is the source-facing companion to the determinant-table wrappers below:
    it derives the initial pivot identity, first-split positivity, determinant
    nonsingularity, max-entry BDD table, and diagonal-bound premise from the
    all-leading-prefix and matrix-`∞` BDD hypotheses, while using the
    canonical-parent inverse-entry handoff.  Thus it does not require the
    stronger all-active-suffix inverse-entry table. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_infNorm_bdd_of_product_bound_diag_update_of_canonical_parent_inverse_entry_of_det_ne_zero
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
    (hDomInf :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ)
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
            (q + 1) hkq))) :
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
  have hDomPi :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j => ‖(fun a b => Ablk i j a b : Fin r → Fin r → ℝ)‖)
        invDiagBound := by
    simpa using higham13_blockDiagDomCol_piNorm_of_infNorm
      hr Ablk invDiagBound hDomInf
  have hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk) := by
    simpa using
      higham13_algorithm13_3_initial_pivot_eq_invOf_blockMatrixFirstSplitA11_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
        (fun i j a b => Ablk i j a b) pivotInv invDiagBound
        hPrefix hDomPi hBound hPivot0
  have hApos :
      0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk) :=
    maxEntryNorm_blockMatrixFirstSplitFlat_pos_of_all_leadingBlockPrefixes
      (m := m + 1) (r := r) hN Ablk hPrefix
  have hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0 :=
    det_ne_zero_blockMatrixFirstSplitFlat_of_blockMatrixFlatFin Ablk
      (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
        (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)
  have hDomMax :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound :=
    higham13_blockDiagDomCol_maxEntry_of_infNorm
      hr Ablk invDiagBound hDomInf
  have hDiagBound : ∀ j : Fin ((m + 1) + 1),
      invDiagBound j ≤ maxEntryNorm hr (Ablk j j) := by
    intro j
    exact le_trans (hBound j) (maxEntryNorm_nonneg hr (Ablk j j))
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_canonical_parent_inverse_entry_of_det_ne_zero
      hr hN Ablk pivotInv hpivot hApos hdet hsn hNn
      invDiagBound stageInvDiagBound hDomMax hDiagBound hInitInv
      hPivotInvBound hProduct hDiagUpdate hsnAll hInvA11 hInvSchur hpivotAll

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table/matrix-`∞` BDD/canonical-parent version of the
    active-suffix first-split product-update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_infNorm_bdd_of_product_bound_diag_update_reciprocal_of_canonical_parent_inverse_entry_of_det_ne_zero
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
    (hDomInf :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ)
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
            (q + 1) hkq))) :
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
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_infNorm_bdd_of_product_bound_diag_update_of_canonical_parent_inverse_entry_of_det_ne_zero
      hr hN Ablk pivotInv invDiagBound hPrefix hDomInf hBound hPivot0
      hsn hNn stageInvDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate hsnAll hInvA11 hInvSchur hpivotAll

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-table/matrix-`∞` BDD/canonical-parent version of the
    active-suffix first-split product-update witness.

    This derives the active-suffix full-tail, pivot-block, and
    Schur-complement invertibility instances from determinant-nonzero source
    tables, supplies the resulting typeclass instances to the pivot-identity
    table, and then reuses the canonical-parent matrix-`∞` BDD product-update
    wrapper. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_infNorm_bdd_of_product_bound_diag_update_of_canonical_parent_inverse_entry_of_det_tables
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
    (hDomInf :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ)
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
            (q + 1) hkq))) :
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
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_infNorm_bdd_of_product_bound_diag_update_of_canonical_parent_inverse_entry_of_det_ne_zero
      hr hN Ablk pivotInv invDiagBound hPrefix hDomInf hBound hPivot0
      hsn hNn stageInvDiagBound hInitInv hPivotInvBound hProduct
      hDiagUpdate hsnAll hInvA11 hInvSchur hpivotAll'

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table/determinant-table/matrix-`∞` BDD/canonical-parent
    version of the active-suffix first-split product-update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_infNorm_bdd_of_product_bound_diag_update_reciprocal_of_canonical_parent_inverse_entry_of_det_tables
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
    (hDomInf :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ)
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
            (q + 1) hkq))) :
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
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_infNorm_bdd_of_product_bound_diag_update_of_canonical_parent_inverse_entry_of_det_tables
      hr hN Ablk pivotInv invDiagBound hPrefix hDomInf hBound hPivot0
      hsn hNn stageInvDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate hFulln hDetFull hDetA11 hpivotAll

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-table version of the active-suffix first-split Eq.13.23
    product-update witness.

    This combines the source product-bound/diagonal-update `rho <= 2` route
    with the determinant-table active-suffix product wrapper, so callers no
    longer need to expose active-suffix invertibility instances separately. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_tables
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
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) :
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
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_det_tables
      hr hN Ablk pivotInv hpivot hApos hRight hsn hNn
      (higham13_algorithm13_3_firstSplitStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hr hN Ablk pivotInv hApos invDiagBound stageInvDiagBound hDom
        hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate)
      hFulln hDetFull hDetA11 hpivotAll hAinvEntryAll

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table/determinant-table version of the active-suffix first-split
    Eq.13.23 product-update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_tables
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
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) :
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
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_tables
      hr hN Ablk pivotInv hpivot hApos hRight hsn hNn
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate hFulln hDetFull hDetA11 hpivotAll hAinvEntryAll

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    BDD-initial-pivot/determinant-table version of the active-suffix
    first-split Eq.13.23 product-update witness.

    This derives the first pivot identity, the positive first-split
    denominator, the canonical ambient right-inverse certificate, and the
    diagonal-bound premise from the all-prefix BDD data.  The genuine
    product-bound/diagonal-update source tables remain explicit. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_bdd_of_product_bound_diag_update_of_det_tables
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
    (hDom :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ)
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
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) :
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
  have hDomPi :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j => ‖(fun a b => Ablk i j a b : Fin r → Fin r → ℝ)‖)
        invDiagBound := by
    simpa [higham13_block_norm_eq_maxEntryNorm hr] using hDom
  have hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk) := by
    simpa using
      higham13_algorithm13_3_initial_pivot_eq_invOf_blockMatrixFirstSplitA11_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
        (fun i j a b => Ablk i j a b) pivotInv invDiagBound
        hPrefix hDomPi hBound hPivot0
  have hApos :
      0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk) :=
    maxEntryNorm_blockMatrixFirstSplitFlat_pos_of_all_leadingBlockPrefixes
      (m := m + 1) (r := r) hN Ablk hPrefix
  have hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0 :=
    det_ne_zero_blockMatrixFirstSplitFlat_of_blockMatrixFlatFin Ablk
      (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
        (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)
  have hRight :
      IsRightInverse (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)) :=
    higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero
      Ablk hdet
  have hDiagBound : ∀ j : Fin ((m + 1) + 1),
      invDiagBound j ≤ maxEntryNorm hr (Ablk j j) := by
    intro j
    exact le_trans (hBound j) (maxEntryNorm_nonneg hr (Ablk j j))
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_tables
      hr hN Ablk pivotInv hpivot hApos hRight hsn hNn
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hPivotInvBound hProduct hDiagUpdate hFulln hDetFull hDetA11
      hpivotAll hAinvEntryAll

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table/BDD-initial-pivot/determinant-table version of the
    active-suffix first-split Eq.13.23 product-update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_bdd_of_product_bound_diag_update_reciprocal_of_det_tables
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
    (hDom :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ)
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
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) :
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
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_bdd_of_product_bound_diag_update_of_det_tables
      hr hN Ablk pivotInv invDiagBound hPrefix hDom hBound hPivot0
      hsn hNn stageInvDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate hFulln hDetFull hDetA11 hpivotAll hAinvEntryAll

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    matrix-`∞` BDD version of the active-suffix determinant-table
    product-update witness.

    The source column BDD hypothesis is stated with matrix `∞` block norms.
    This wrapper derives the max-entry BDD table consumed by the existing
    product-update route, while leaving the product/update, determinant-table,
    and inverse-entry/source-comparison obligations explicit. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_infNorm_bdd_of_product_bound_diag_update_of_det_tables
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
    (hDomInf :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ)
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
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) :
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
  have hDomMax :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound :=
    higham13_blockDiagDomCol_maxEntry_of_infNorm
      hr Ablk invDiagBound hDomInf
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_bdd_of_product_bound_diag_update_of_det_tables
      hr hN Ablk pivotInv invDiagBound hPrefix hDomMax hBound hPivot0
      hsn hNn stageInvDiagBound hInitInv hPivotInvBound hProduct
      hDiagUpdate hFulln hDetFull hDetA11 hpivotAll hAinvEntryAll

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table/matrix-`∞` BDD version of the active-suffix
    determinant-table product-update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_infNorm_bdd_of_product_bound_diag_update_reciprocal_of_det_tables
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
    (hDomInf :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ)
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
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) :
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
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_infNorm_bdd_of_product_bound_diag_update_of_det_tables
      hr hN Ablk pivotInv invDiagBound hPrefix hDomInf hBound hPivot0
      hsn hNn stageInvDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate hFulln hDetFull hDetA11 hpivotAll hAinvEntryAll

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero first-split product witness from canonical
    active-suffix source obligations.

    This packages the canonical `nonsingInv` right-inverse certificate, so
    callers that already carry the source-level determinant hypothesis do not
    need to expose a separate ambient right-inverse premise. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_det_ne_zero
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
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) :
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
    higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa
      hr hN Ablk pivotInv hpivot hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero
        Ablk hdet)
      hsn hNn hsnAll hInvA11 hInvSchur hpivotAll hAinv_tail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero point-row first-split product witness from canonical
    active-suffix source obligations.

    The source-side `rho <= 2` proof remains explicit; only the ambient
    `nonsingInv` right-inverse certificate is derived from `det A != 0`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_det_ne_zero
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
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) :
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
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa
      hr hN Ablk pivotInv hpivot hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero
        Ablk hdet)
      hsn hNn hRho_le_two hsnAll hInvA11 hInvSchur hpivotAll hAinv_tail

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero active-suffix product witness with the initial pivot
    identity derived from the BDD canonical `nonsingInv` certificate.

    This consumes the BDD all-leading-prefix bridge to remove the separate
    first-pivot `⅟(blockMatrixFirstSplitA11 ...)` proof artifact from the
    Eq.13.22 active-suffix product witness. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_bdd_of_det_ne_zero
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
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
      BlockMatrixNonsingular (leadingBlockPrefix13_2 Ablk p hp))
    (hDom : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j => ‖(Ablk i j : Fin r → Fin r → ℝ)‖) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hApos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk))
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
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
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) :
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
  have hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk) :=
    higham13_algorithm13_3_initial_pivot_eq_invOf_blockMatrixFirstSplitA11_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
      Ablk pivotInv invDiagBound hPrefix hDom hBound hPivot0
  exact
    higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_det_ne_zero
      hr hN Ablk pivotInv hpivot hApos hdet hsn hNn hsnAll hInvA11
      hInvSchur hpivotAll hAinv_tail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero point-row active-suffix product witness with the
    initial pivot identity derived from the BDD canonical `nonsingInv`
    certificate.

    The source-side `rho <= 2` proof remains explicit; this wrapper only
    removes the separate first-pivot `⅟(blockMatrixFirstSplitA11 ...)`
    identification premise. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_bdd_of_det_ne_zero
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
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
      BlockMatrixNonsingular (leadingBlockPrefix13_2 Ablk p hp))
    (hDom : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j => ‖(Ablk i j : Fin r → Fin r → ℝ)‖) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
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
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) :
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
  have hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk) :=
    higham13_algorithm13_3_initial_pivot_eq_invOf_blockMatrixFirstSplitA11_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
      Ablk pivotInv invDiagBound hPrefix hDom hBound hPivot0
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_det_ne_zero
      hr hN Ablk pivotInv hpivot hApos hdet hsn hNn hRho_le_two
      hsnAll hInvA11 hInvSchur hpivotAll hAinv_tail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero active-suffix first-split product witness whose
    `rho <= 2` side condition is supplied by the source-strength
    product-bound/diagonal-update BDD route. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
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
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) :
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
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update
      hr hN Ablk pivotInv hpivot hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero
        Ablk hdet)
      hsn hNn invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hPivotInvBound hProduct hDiagUpdate hsnAll hInvA11 hInvSchur hpivotAll
      hAinv_tail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero reciprocal-table version of the active-suffix
    first-split Eq.13.23 product-update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_ne_zero
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
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) :
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
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal
      hr hN Ablk pivotInv hpivot hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero
        Ablk hdet)
      hsn hNn invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hReciprocal hProduct hDiagUpdate hsnAll hInvA11 hInvSchur hpivotAll
      hAinv_tail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    max-entry BDD/determinant-nonzero active-suffix product-update witness.

    This derives the initial pivot identity, positive first-split denominator,
    determinant/right-inverse bridge, and diagonal-bound premise from the
    all-leading-prefix and max-entry BDD source data, while keeping the
    product/update and recursive active-suffix source obligations explicit. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_bdd_of_product_bound_diag_update_of_det_ne_zero
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
    (hDom :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ)
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
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) :
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
  have hDomPi :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j => ‖(fun a b => Ablk i j a b : Fin r → Fin r → ℝ)‖)
        invDiagBound := by
    simpa [higham13_block_norm_eq_maxEntryNorm hr] using hDom
  have hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk) := by
    simpa using
      higham13_algorithm13_3_initial_pivot_eq_invOf_blockMatrixFirstSplitA11_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
        (fun i j a b => Ablk i j a b) pivotInv invDiagBound
        hPrefix hDomPi hBound hPivot0
  have hApos :
      0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk) :=
    maxEntryNorm_blockMatrixFirstSplitFlat_pos_of_all_leadingBlockPrefixes
      (m := m + 1) (r := r) hN Ablk hPrefix
  have hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0 :=
    det_ne_zero_blockMatrixFirstSplitFlat_of_blockMatrixFlatFin Ablk
      (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
        (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)
  have hDiagBound : ∀ j : Fin ((m + 1) + 1),
      invDiagBound j ≤ maxEntryNorm hr (Ablk j j) := by
    intro j
    exact le_trans (hBound j) (maxEntryNorm_nonneg hr (Ablk j j))
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
      hr hN Ablk pivotInv hpivot hApos hdet hsn hNn
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hPivotInvBound hProduct hDiagUpdate hsnAll hInvA11 hInvSchur
      hpivotAll hAinv_tail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table companion to the max-entry BDD/determinant-nonzero
    active-suffix product-update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_bdd_of_product_bound_diag_update_reciprocal_of_det_ne_zero
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
    (hDom :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ)
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
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) :
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
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_bdd_of_product_bound_diag_update_of_det_ne_zero
      hr hN Ablk pivotInv invDiagBound hPrefix hDom hBound hPivot0
      hsn hNn stageInvDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate hsnAll hInvA11 hInvSchur hpivotAll hAinv_tail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    matrix-`infNorm` BDD/determinant-nonzero active-suffix product-update
    witness.

    This derives the initial pivot identity, positive first-split denominator,
    determinant certificate, max-entry BDD table, and diagonal-bound premise
    from the all-leading-prefix and matrix-`infNorm` BDD source data, while
    keeping the product/update and recursive active-suffix source obligations
    explicit. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_infNorm_bdd_of_product_bound_diag_update_of_det_ne_zero
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
    (hDomInf :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ)
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
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) :
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
  have hDomPi :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j => ‖(fun a b => Ablk i j a b : Fin r → Fin r → ℝ)‖)
        invDiagBound :=
    higham13_blockDiagDomCol_piNorm_of_infNorm
      hr Ablk invDiagBound hDomInf
  have hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk) := by
    simpa using
      higham13_algorithm13_3_initial_pivot_eq_invOf_blockMatrixFirstSplitA11_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
        (fun i j a b => Ablk i j a b) pivotInv invDiagBound
        hPrefix hDomPi hBound hPivot0
  have hApos :
      0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk) :=
    maxEntryNorm_blockMatrixFirstSplitFlat_pos_of_all_leadingBlockPrefixes
      (m := m + 1) (r := r) hN Ablk hPrefix
  have hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0 :=
    det_ne_zero_blockMatrixFirstSplitFlat_of_blockMatrixFlatFin Ablk
      (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
        (Nat.succ_pos (m + 1)) (fun i j a b => Ablk i j a b) hPrefix)
  have hDomMax :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound :=
    higham13_blockDiagDomCol_maxEntry_of_infNorm
      hr Ablk invDiagBound hDomInf
  have hDiagBound : ∀ j : Fin ((m + 1) + 1),
      invDiagBound j ≤ maxEntryNorm hr (Ablk j j) := by
    intro j
    exact le_trans (hBound j) (maxEntryNorm_nonneg hr (Ablk j j))
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
      hr hN Ablk pivotInv hpivot hApos hdet hsn hNn
      invDiagBound stageInvDiagBound hDomMax hDiagBound hInitInv
      hPivotInvBound hProduct hDiagUpdate hsnAll hInvA11 hInvSchur
      hpivotAll hAinv_tail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table companion to the matrix-`infNorm`
    BDD/determinant-nonzero active-suffix product-update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_infNorm_bdd_of_product_bound_diag_update_reciprocal_of_det_ne_zero
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
    (hDomInf :
      IsBlockDiagDomCol ((m + 1) + 1)
        (fun i j : Fin ((m + 1) + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin ((m + 1) + 1), invDiagBound j ≤ 0)
    (hPivot0 :
      pivotInv 0 =
        nonsingInv r
          (Ablk (0 : Fin ((m + 1) + 1)) (0 : Fin ((m + 1) + 1))))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ)
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
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) :
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
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_initial_pivot_nonsingInv_infNorm_bdd_of_product_bound_diag_update_of_det_ne_zero
      hr hN Ablk pivotInv invDiagBound hPrefix hDomInf hBound hPivot0
      hsn hNn stageInvDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate hsnAll hInvA11 hInvSchur hpivotAll hAinv_tail

end NumStability
