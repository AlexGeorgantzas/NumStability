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
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Problem04.ActiveStageBounds
import NumStability.Source.Higham.Chapter13.Problem04.BlockInverseBounds
import NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauChain
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.RecursiveBudgetChains

/-!
# Source.Higham.Chapter13.Problem04.GlobalTableauProducts.ActiveSuffix

This module formalizes the source-facing Chapter 13 statements for
`Problem04.GlobalTableauProducts.ActiveSuffix`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    first-split product witness from the fixed-ambient global-tableau source
    chain and the concrete Algorithm 13.3 matrix-stage history.

    Compared with the raw global-tableau API, this wrapper derives the ambient
    initial containment and builds the first successor certificate from the
    recorded first-split matrix-stage history.  The recursive Schur-tail
    global-tableau certificate remains the explicit source obligation. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa
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
  have hcert :
      Higham13Eq1322GlobalTableauSourceChain hr hN A0 G Ainv
        hApos n (m + 1) Ablk pivotInv := by
    simpa [A0, G, Ainv, hmFull] using
      Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_first_split_exact_kappa
        hr hN Ablk pivotInv hpivot hApos hsn hTail
  simpa [A0, G, Ainv, hmFull] using
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_22_product_exact_kappa_of_right_inverse
      (r := r) (N := r + (m + 1) * r) (n := n)
      hr hN A0 G Ainv hApos (by simpa [A0, Ainv] using hRight)
      hNn hA_le_G hcert

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    first-split product witness from canonical active-suffix source obligations.

    This refines
    `higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa`
    by constructing its recursive Schur-tail global-tableau certificate from
    the canonical active-suffix source-chain theorem.  The old caller-supplied `hTail`
    premise is replaced by the visible first Schur-tail inverse-entry
    comparison and the per-stage active-suffix invertibility, pivot, and
    dimension obligations. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa
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
  exact
    higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa
      hr hN Ablk pivotInv hpivot hApos hRight hsn hNn hTail

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    first-split product witness with parent inverse-entry handoff.

    This refines
    `higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa`:
    the visible first Schur-tail inverse-entry premise is derived internally
    from the parent first-split inverse-entry comparison by the block inverse
    formula.  The remaining inverse-entry comparison is the source-level parent
    comparison for the current split. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_parent_inverse_entry
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
        hr hN A0 Ainv Ablk pivotInv hApos hA_le_G
        hpivot hsnAll hInvA11 hInvSchur hpivotAll hAinv_parent
  exact
    higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa
      hr hN Ablk pivotInv hpivot hApos hRight hsn hNn hTail

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    first-split product witness with canonical parent inverse-entry handoff.

    This refines the parent-inverse-entry wrapper by deriving the parent
    first-split inverse-entry comparison from the canonical ambient `nonsingInv`
    of `blockMatrixFirstSplitFlat Ablk`. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_canonical_parent_inverse_entry
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
          (n : ℝ) *
            (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos) ^ 3 *
            (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  classical
  have hAinv_parent :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11 Ablk)
            (blockMatrixFirstSplitA12 Ablk)
            (blockMatrixFirstSplitA21 Ablk)
            (blockMatrixFirstSplitA22 Ablk)) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)) := by
    exact higham13_problem13_4_firstSplit_parent_inverse_entry_bound_from_nonsingInv
      hN Ablk
  exact
    higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_parent_inverse_entry
      hr hN Ablk pivotInv hpivot hApos hRight hsn hNn
      hsnAll hInvA11 hInvSchur hpivotAll hAinv_parent

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero first-split product witness with canonical parent
    inverse-entry handoff.

    This combines
    `..._of_canonical_parent_inverse_entry` with the determinant-to-canonical
    `nonsingInv` right-inverse bridge, so the source-level determinant
    hypothesis supplies both the ambient right-inverse certificate and the
    parent first-split inverse-entry comparison. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_canonical_parent_inverse_entry_of_det_ne_zero
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
            (q + 1) hkq))) :
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
    higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_canonical_parent_inverse_entry
      hr hN Ablk pivotInv hpivot hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero
        Ablk hdet)
      hsn hNn hsnAll hInvA11 hInvSchur hpivotAll

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-table first-split product witness from canonical active-suffix
    source obligations.

    This is the determinant-table companion of
    `higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa`.
    A single ambient dimension budget and per-tail determinant-nonzero tables
    derive the active-suffix invertibility instances internally; callers still
    supply the source inverse-entry comparisons and the ambient right-inverse
    certificate. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_det_tables
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
          (n : ℝ) *
            (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos) ^ 3 *
            (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
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
  exact
    higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa
      hr hN Ablk pivotInv hpivot hApos hRight hsn hNn hTail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    first-split point-row product witness from the fixed-ambient
    global-tableau source chain and the concrete Algorithm 13.3 stage history.

    This is the Eq.13.23 companion of
    `higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa`;
    it keeps the source-side `rho <= 2` theorem as the explicit remaining
    BDD/product-update obligation. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa
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
  have hcert :
      Higham13Eq1322GlobalTableauSourceChain hr hN A0 G Ainv
        hApos n (m + 1) Ablk pivotInv := by
    simpa [A0, G, Ainv, hmFull] using
      Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_first_split_exact_kappa
        hr hN Ablk pivotInv hpivot hApos hsn hTail
  simpa [A0, G, Ainv, hmFull] using
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse
      (r := r) (N := r + (m + 1) * r) (n := n)
      hr hN A0 G Ainv hApos (by simpa [A0, Ainv] using hRight)
      hNn hA_le_G (by simpa [A0, G, hmFull] using hRho_le_two) hcert

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    first-split point-row product witness from canonical active-suffix source
    obligations.

    This refines
    `higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa`
    in the same way as the Eq.13.22 active-suffix wrapper: the recursive
    Schur-tail global-tableau certificate is built from the canonical
    first-Schur-tail active-suffix theorem.  The `rho <= 2` premise remains the
    source-side BDD/product-update obligation for Eq.13.23. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa
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
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa
      hr hN Ablk pivotInv hpivot hApos hRight hsn hNn hRho_le_two hTail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    first-split point-row product witness with parent inverse-entry handoff.

    This is the Eq.13.23 companion of
    `higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_parent_inverse_entry`.
    It keeps the source-side `rho <= 2` theorem explicit while deriving the
    first Schur-tail inverse-entry comparison from the parent block inverse. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_parent_inverse_entry
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
        hr hN A0 Ainv Ablk pivotInv hApos hA_le_G
        hpivot hsnAll hInvA11 hInvSchur hpivotAll hAinv_parent
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa
      hr hN Ablk pivotInv hpivot hApos hRight hsn hNn hRho_le_two hTail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    first-split point-row product witness with canonical parent inverse-entry
    handoff.

    This is the Eq.13.23 companion of the canonical Eq.13.22 wrapper.  It
    derives the parent first-split inverse-entry comparison from the canonical
    ambient `nonsingInv`, while keeping the source-side `rho <= 2` theorem
    explicit. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_canonical_parent_inverse_entry
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
  have hAinv_parent :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11 Ablk)
            (blockMatrixFirstSplitA12 Ablk)
            (blockMatrixFirstSplitA21 Ablk)
            (blockMatrixFirstSplitA22 Ablk)) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)) := by
    exact higham13_problem13_4_firstSplit_parent_inverse_entry_bound_from_nonsingInv
      hN Ablk
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_parent_inverse_entry
      hr hN Ablk pivotInv hpivot hApos hRight hsn hNn hRho_le_two
      hsnAll hInvA11 hInvSchur hpivotAll hAinv_parent

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero point-row product witness with canonical parent
    inverse-entry handoff.

    The source-side `rho <= 2` proof remains explicit; the source-level
    determinant hypothesis now also supplies the ambient canonical
    `nonsingInv` right-inverse certificate. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_canonical_parent_inverse_entry_of_det_ne_zero
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
      hr hN Ablk pivotInv hpivot hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero
        Ablk hdet)
      hsn hNn hRho_le_two hsnAll hInvA11 hInvSchur hpivotAll

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-table first-split point-row product witness from canonical
    active-suffix source obligations.

    This is the Eq.13.23 companion of
    `higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_det_tables`.
    The determinant tables package the active-suffix invertibility data; the
    source-side `rho <= 2` theorem remains explicit. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_det_tables
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
    (hRho_le_two :
      growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos ≤ 2)
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
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa
      hr hN Ablk pivotInv hpivot hApos hRight hsn hNn hRho_le_two hTail

end NumStability
