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
import NumStability.Source.Higham.Chapter13.Equation22
import NumStability.Source.Higham.Chapter13.Equation23
import NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauProducts.DiagonalUpdate
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.RecursiveBudgetChains
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis

/-!
# Source.Higham.Chapter13.Problem04.DeterminantChainProducts

This module formalizes the source-facing Chapter 13 statements for
`Problem04.DeterminantChainProducts`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    uniform-flat determinant-nonzero successor product witness from an ambient
    recursive tail chain.

    This packages
    `higham13_eq13_22_blockLUBudgetChain_succ_from_flat_matrix_stage_history_exact_kappa_of_det_ne_zero`
    through the chain-to-product theorem, keeping the final product bound
    entirely in the uniform `blockMatrixFlatFin Ablk` representation. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_flat_tail_chain_matrix_stage_history_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ)
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
    (hdetFlat :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (((m + 1) + 1) * r)) (Fin (((m + 1) + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
    let hNFull : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
    let A0 : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      blockMatrixFlatFin Ablk
    let G : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFull hmFull hr Ablk pivotInv
    let Ainv : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      nonsingInv (((m + 1) + 1) * r) A0
    let hApos : 0 < maxEntryNorm hNFull A0 :=
      maxEntryNorm_pos_of_det_ne_zero hNFull A0 hdetFlat
    Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFull A0 G hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull Ainv))
        (growthFactorEntry hNFull A0 G hApos *
          maxEntryNormRect hNFull hNFull A0)
        m (blockSchur Ablk (pivotInv 0)) (fun k => pivotInv (k + 1)) →
      ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
              blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            (n : ℝ) * (growthFactorEntry hNFull A0 G hApos) ^ 3 *
              (maxEntryNormRect hNFull hNFull A0 *
                maxEntryNormRect hNFull hNFull Ainv) *
              maxEntryNormRect hNFull hNFull A0 := by
  dsimp only
  intro hTail
  let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  let hNFull : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
  let A0 : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    blockMatrixFlatFin Ablk
  let G : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      hNFull hmFull hr Ablk pivotInv
  let Ainv : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    nonsingInv (((m + 1) + 1) * r) A0
  let hApos : 0 < maxEntryNorm hNFull A0 :=
    maxEntryNorm_pos_of_det_ne_zero hNFull A0 hdetFlat
  have hchain :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFull A0 G hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull Ainv))
        (growthFactorEntry hNFull A0 G hApos *
          maxEntryNormRect hNFull hNFull A0)
        (m + 1) Ablk pivotInv := by
    simpa [hmFull, hNFull, A0, G, Ainv, hApos] using
      higham13_eq13_22_blockLUBudgetChain_succ_from_flat_matrix_stage_history_exact_kappa_of_det_ne_zero
        hr Ablk pivotInv hpivot hdetFlat n hsn hNn hTail
  simpa [hmFull, hNFull, A0, G, Ainv, hApos] using
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_22_product_exact_kappa
      (r := r) hr (hN := hNFull) (A0 := A0) (G := G) (Ainv := Ainv)
      hApos n hchain

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    uniform-flat determinant-nonzero point-row successor product witness from
    an ambient recursive tail chain.

    This is the Eq.13.23 companion of the preceding theorem.  It keeps the
    source-side `rho <= 2` obligation visible while expressing the final
    `8 n kappa(A) ||A||` bound in the uniform flat representation. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_flat_tail_chain_matrix_stage_history_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ)
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
    (hdetFlat :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (((m + 1) + 1) * r)) (Fin (((m + 1) + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
    let hNFull : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
    let A0 : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      blockMatrixFlatFin Ablk
    let G : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFull hmFull hr Ablk pivotInv
    let Ainv : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      nonsingInv (((m + 1) + 1) * r) A0
    let hApos : 0 < maxEntryNorm hNFull A0 :=
      maxEntryNorm_pos_of_det_ne_zero hNFull A0 hdetFlat
    growthFactorEntry hNFull A0 G hApos ≤ 2 →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFull A0 G hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull Ainv))
        (growthFactorEntry hNFull A0 G hApos *
          maxEntryNormRect hNFull hNFull A0)
        m (blockSchur Ablk (pivotInv 0)) (fun k => pivotInv (k + 1)) →
      ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
              blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hNFull hNFull A0 *
                maxEntryNormRect hNFull hNFull Ainv) *
              maxEntryNormRect hNFull hNFull A0 := by
  dsimp only
  intro hRho_le_two hTail
  let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  let hNFull : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
  let A0 : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    blockMatrixFlatFin Ablk
  let G : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      hNFull hmFull hr Ablk pivotInv
  let Ainv : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    nonsingInv (((m + 1) + 1) * r) A0
  let hApos : 0 < maxEntryNorm hNFull A0 :=
    maxEntryNorm_pos_of_det_ne_zero hNFull A0 hdetFlat
  have hchain :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFull A0 G hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull Ainv))
        (growthFactorEntry hNFull A0 G hApos *
          maxEntryNormRect hNFull hNFull A0)
        (m + 1) Ablk pivotInv := by
    simpa [hmFull, hNFull, A0, G, Ainv, hApos] using
      higham13_eq13_22_blockLUBudgetChain_succ_from_flat_matrix_stage_history_exact_kappa_of_det_ne_zero
        hr Ablk pivotInv hpivot hdetFlat n hsn hNn hTail
  simpa [hmFull, hNFull, A0, G, Ainv, hApos] using
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_23_product_exact_kappa
      (r := r) hr (hN := hNFull) (A0 := A0) (G := G) (Ainv := Ainv)
      hApos n hchain hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    determinant-nonzero variant of the tail-local inverse-ratio successor chain. -/
theorem
    higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r)
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
    (hTailPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))))
    (hApos :
      0 < maxEntryNorm (Nat.add_pos_left hr ((m + 1) * r))
        (blockMatrixFirstSplitFlat Ablk))
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNFull : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let Gfull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv
    let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) A0
    (maxEntryNormRect hNTail hNTail AinvTail *
          maxEntryNormRect hNFull hNFull A0 ≤
        maxEntryNormRect hNFull hNFull AinvFull *
          maxEntryNormRect hNTail hNTail Atail) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull))
        (growthFactorEntry hNFull A0 Gfull hApos *
          maxEntryNormRect hNFull hNFull A0)
        (m + 1) Ablk pivotInv := by
  exact
    higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa
      hr Ablk pivotInv hpivot hTailPos hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero Ablk hdet)
      n hsn hNn

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    determinant-nonzero variant of the tail-local lower-comparison successor chain. -/
theorem
    higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r)
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
    (hTailPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))))
    (hApos :
      0 < maxEntryNorm (Nat.add_pos_left hr ((m + 1) * r))
        (blockMatrixFirstSplitFlat Ablk))
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNFull : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let Gfull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv
    let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) A0
    ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail) ≤
        (n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull))
        (growthFactorEntry hNFull A0 Gfull hApos *
          maxEntryNormRect hNFull hNFull A0)
        (m + 1) Ablk pivotInv := by
  exact
    higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa
      hr Ablk pivotInv hpivot hTailPos hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero Ablk hdet)
      n hsn hNn

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero successor product witness from an ambient tail chain. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_chain_matrix_stage_history_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ)
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
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hTail :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN
              (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))))
        (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos *
          maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk))
        m (blockSchur Ablk (pivotInv 0)) (fun k => pivotInv (k + 1))) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
            blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
          (n : ℝ) *
            (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos) ^ 3 *
            (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  exact
    higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_chain_matrix_stage_history_exact_kappa
      hr hN Ablk pivotInv hpivot hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero Ablk hdet)
      n hsn hNn hTail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero point-row successor product witness from an ambient tail chain. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_chain_matrix_stage_history_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ)
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
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hRho_le_two :
      growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos ≤ 2)
    (hTail :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN
              (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))))
        (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos *
          maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk))
        m (blockSchur Ablk (pivotInv 0)) (fun k => pivotInv (k + 1))) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
            blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_chain_matrix_stage_history_exact_kappa
      hr hN Ablk pivotInv hpivot hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero Ablk hdet)
      n hsn hNn hRho_le_two hTail

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero successor product witness from a tail-local chain plus
    the source inverse-ratio comparison. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r)
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
    (hTailPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))))
    (hApos :
      0 < maxEntryNorm (Nat.add_pos_left hr ((m + 1) * r))
        (blockMatrixFirstSplitFlat Ablk))
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNFull : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let Gfull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv
    let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) A0
    (maxEntryNormRect hNTail hNTail AinvTail *
          maxEntryNormRect hNFull hNFull A0 ≤
        maxEntryNormRect hNFull hNFull AinvFull *
          maxEntryNormRect hNTail hNTail Atail) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
              blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            (n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 3 *
              (maxEntryNormRect hNFull hNFull A0 *
                maxEntryNormRect hNFull hNFull AinvFull) *
              maxEntryNormRect hNFull hNFull A0 := by
  exact
    higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa
      hr Ablk pivotInv hpivot hTailPos hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero Ablk hdet)
      n hsn hNn

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero point-row successor product witness from a tail-local
    chain plus the source inverse-ratio comparison. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r)
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
    (hTailPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))))
    (hApos :
      0 < maxEntryNorm (Nat.add_pos_left hr ((m + 1) * r))
        (blockMatrixFirstSplitFlat Ablk))
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hRho_le_two :
      growthFactorEntry (Nat.add_pos_left hr ((m + 1) * r))
          (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.add_pos_left hr ((m + 1) * r))
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos ≤ 2) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNFull : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) A0
    (maxEntryNormRect hNTail hNTail AinvTail *
          maxEntryNormRect hNFull hNFull A0 ≤
        maxEntryNormRect hNFull hNFull AinvFull *
          maxEntryNormRect hNTail hNTail Atail) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
              blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hNFull hNFull A0 *
                maxEntryNormRect hNFull hNFull AinvFull) *
              maxEntryNormRect hNFull hNFull A0 := by
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa
      hr Ablk pivotInv hpivot hTailPos hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero Ablk hdet)
      n hsn hNn hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero successor product witness from a tail-local chain plus
    the direct lower-budget comparison. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r)
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
    (hTailPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))))
    (hApos :
      0 < maxEntryNorm (Nat.add_pos_left hr ((m + 1) * r))
        (blockMatrixFirstSplitFlat Ablk))
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNFull : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let Gfull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv
    let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) A0
    ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail) ≤
        (n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
              blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            (n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 3 *
              (maxEntryNormRect hNFull hNFull A0 *
                maxEntryNormRect hNFull hNFull AinvFull) *
              maxEntryNormRect hNFull hNFull A0 := by
  exact
    higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa
      hr Ablk pivotInv hpivot hTailPos hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero Ablk hdet)
      n hsn hNn

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero point-row successor product witness from a tail-local
    chain plus the direct lower-budget comparison. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r)
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
    (hTailPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))))
    (hApos :
      0 < maxEntryNorm (Nat.add_pos_left hr ((m + 1) * r))
        (blockMatrixFirstSplitFlat Ablk))
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hRho_le_two :
      growthFactorEntry (Nat.add_pos_left hr ((m + 1) * r))
          (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.add_pos_left hr ((m + 1) * r))
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos ≤ 2) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNFull : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let Gfull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv
    let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) A0
    ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail) ≤
        (n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
              blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hNFull hNFull A0 *
                maxEntryNormRect hNFull hNFull AinvFull) *
              maxEntryNormRect hNFull hNFull A0 := by
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa
      hr Ablk pivotInv hpivot hTailPos hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero Ablk hdet)
      n hsn hNn hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    determinant-nonzero inverse-ratio successor chain with the Schur-tail
    positivity premise derived from first-split Schur-complement invertibility. -/
theorem
    higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa_of_det_ne_zero_of_schur_invertible
    {m r : ℕ} (hr : 0 < r)
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
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNFull : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let Gfull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv
    let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) A0
    let hApos : 0 < maxEntryNorm hNFull A0 :=
      maxEntryNorm_pos_of_det_ne_zero hNFull A0 hdet
    let hTailPos : 0 < maxEntryNorm hNTail Atail :=
      maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
        hr Ablk pivotInv hpivot
    (maxEntryNormRect hNTail hNTail AinvTail *
          maxEntryNormRect hNFull hNFull A0 ≤
        maxEntryNormRect hNFull hNFull AinvFull *
          maxEntryNormRect hNTail hNTail Atail) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull))
        (growthFactorEntry hNFull A0 Gfull hApos *
          maxEntryNormRect hNFull hNFull A0)
        (m + 1) Ablk pivotInv := by
  dsimp only
  intro hInvRatio hTailLocal
  let hTailPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))) :=
    maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
      hr Ablk pivotInv hpivot
  let hApos :
      0 < maxEntryNorm (Nat.add_pos_left hr ((m + 1) * r))
        (blockMatrixFirstSplitFlat Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero
      (Nat.add_pos_left hr ((m + 1) * r)) (blockMatrixFirstSplitFlat Ablk) hdet
  simpa [hTailPos, hApos] using
    higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa_of_det_ne_zero
      hr Ablk pivotInv hpivot hTailPos hApos hdet n hsn hNn hInvRatio hTailLocal

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    determinant-nonzero lower-comparison successor chain with the Schur-tail
    positivity premise derived from first-split Schur-complement invertibility. -/
theorem
    higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa_of_det_ne_zero_of_schur_invertible
    {m r : ℕ} (hr : 0 < r)
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
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNFull : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let Gfull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv
    let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) A0
    let hApos : 0 < maxEntryNorm hNFull A0 :=
      maxEntryNorm_pos_of_det_ne_zero hNFull A0 hdet
    let hTailPos : 0 < maxEntryNorm hNTail Atail :=
      maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
        hr Ablk pivotInv hpivot
    ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail) ≤
        (n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull))
        (growthFactorEntry hNFull A0 Gfull hApos *
          maxEntryNormRect hNFull hNFull A0)
        (m + 1) Ablk pivotInv := by
  dsimp only
  intro hLower hTailLocal
  let hTailPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))) :=
    maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
      hr Ablk pivotInv hpivot
  let hApos :
      0 < maxEntryNorm (Nat.add_pos_left hr ((m + 1) * r))
        (blockMatrixFirstSplitFlat Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero
      (Nat.add_pos_left hr ((m + 1) * r)) (blockMatrixFirstSplitFlat Ablk) hdet
  simpa [hTailPos, hApos] using
    higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa_of_det_ne_zero
      hr Ablk pivotInv hpivot hTailPos hApos hdet n hsn hNn hLower hTailLocal

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero inverse-ratio successor product witness with the
    Schur-tail positivity premise derived from first-split Schur-complement
    invertibility. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa_of_det_ne_zero_of_schur_invertible
    {m r : ℕ} (hr : 0 < r)
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
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNFull : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let Gfull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv
    let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) A0
    let hApos : 0 < maxEntryNorm hNFull A0 :=
      maxEntryNorm_pos_of_det_ne_zero hNFull A0 hdet
    let hTailPos : 0 < maxEntryNorm hNTail Atail :=
      maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
        hr Ablk pivotInv hpivot
    (maxEntryNormRect hNTail hNTail AinvTail *
          maxEntryNormRect hNFull hNFull A0 ≤
        maxEntryNormRect hNFull hNFull AinvFull *
          maxEntryNormRect hNTail hNTail Atail) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
              blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            (n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 3 *
              (maxEntryNormRect hNFull hNFull A0 *
                maxEntryNormRect hNFull hNFull AinvFull) *
              maxEntryNormRect hNFull hNFull A0 := by
  dsimp only
  intro hInvRatio hTailLocal
  let hTailPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))) :=
    maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
      hr Ablk pivotInv hpivot
  let hApos :
      0 < maxEntryNorm (Nat.add_pos_left hr ((m + 1) * r))
        (blockMatrixFirstSplitFlat Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero
      (Nat.add_pos_left hr ((m + 1) * r)) (blockMatrixFirstSplitFlat Ablk) hdet
  simpa [hTailPos, hApos] using
    higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa_of_det_ne_zero
      hr Ablk pivotInv hpivot hTailPos hApos hdet n hsn hNn hInvRatio hTailLocal

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero inverse-ratio point-row successor product witness with
    the Schur-tail positivity premise derived from first-split Schur-complement
    invertibility. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa_of_det_ne_zero_of_schur_invertible
    {m r : ℕ} (hr : 0 < r)
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
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNFull : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) A0
    let hApos : 0 < maxEntryNorm hNFull A0 :=
      maxEntryNorm_pos_of_det_ne_zero hNFull A0 hdet
    let hTailPos : 0 < maxEntryNorm hNTail Atail :=
      maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
        hr Ablk pivotInv hpivot
    growthFactorEntry hNFull A0
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos ≤ 2 →
      (maxEntryNormRect hNTail hNTail AinvTail *
          maxEntryNormRect hNFull hNFull A0 ≤
        maxEntryNormRect hNFull hNFull AinvFull *
          maxEntryNormRect hNTail hNTail Atail) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
              blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hNFull hNFull A0 *
                maxEntryNormRect hNFull hNFull AinvFull) *
              maxEntryNormRect hNFull hNFull A0 := by
  dsimp only
  intro hRho_le_two hInvRatio hTailLocal
  let hTailPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))) :=
    maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
      hr Ablk pivotInv hpivot
  let hApos :
      0 < maxEntryNorm (Nat.add_pos_left hr ((m + 1) * r))
        (blockMatrixFirstSplitFlat Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero
      (Nat.add_pos_left hr ((m + 1) * r)) (blockMatrixFirstSplitFlat Ablk) hdet
  simpa [hTailPos, hApos] using
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa_of_det_ne_zero
      hr Ablk pivotInv hpivot hTailPos hApos hdet n hsn hNn
      hRho_le_two hInvRatio hTailLocal

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero inverse-ratio point-row successor product witness
    whose `rho <= 2` side condition is supplied by the source-strength
    product-bound/diagonal-update BDD route.

    This is the product-update companion to
    `..._of_det_ne_zero_of_schur_invertible`: it keeps the source
    inverse-ratio comparison explicit, but no longer asks callers to provide
    the raw full first-split growth-factor bound separately. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_ne_zero_of_schur_invertible
    {m r : ℕ} (hr : 0 < r)
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
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNFull : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) A0
    let hTailPos : 0 < maxEntryNorm hNTail Atail :=
      maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
        hr Ablk pivotInv hpivot
    (invDiagBound : Fin ((m + 1) + 1) → ℝ) →
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ) →
    IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin ((m + 1) + 1),
      invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin ((m + 1) + 1),
      stageInvDiagBound 0 j = invDiagBound j) →
    (∀ k : ℕ, ∀ hk : k < (m + 1) + 1,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1) →
    (∀ k : ℕ, ∀ hk : k < (m + 1) + 1, ∀ i j : Fin ((m + 1) + 1),
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
              ⟨k, hk⟩ j)) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)) →
    (maxEntryNormRect hNTail hNTail AinvTail *
          maxEntryNormRect hNFull hNFull A0 ≤
        maxEntryNormRect hNFull hNFull AinvFull *
          maxEntryNormRect hNTail hNTail Atail) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
              blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hNFull hNFull A0 *
                maxEntryNormRect hNFull hNFull AinvFull) *
              maxEntryNormRect hNFull hNFull A0 := by
  dsimp only
  intro invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hPivotInvBound hProduct hDiagUpdate hInvRatio hTailLocal
  let hApos :
      0 < maxEntryNorm (Nat.add_pos_left hr ((m + 1) * r))
        (blockMatrixFirstSplitFlat Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero
      (Nat.add_pos_left hr ((m + 1) * r)) (blockMatrixFirstSplitFlat Ablk) hdet
  have hRho_le_two :
      growthFactorEntry (Nat.add_pos_left hr ((m + 1) * r))
          (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.add_pos_left hr ((m + 1) * r))
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos ≤
        2 := by
    simpa [hApos] using
      higham13_algorithm13_3_firstSplitStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hr (Nat.add_pos_left hr ((m + 1) * r)) Ablk pivotInv hApos
        invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
        hPivotInvBound hProduct hDiagUpdate
  simpa [hApos] using
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa_of_det_ne_zero_of_schur_invertible
      hr Ablk pivotInv hpivot hdet n hsn hNn hRho_le_two hInvRatio hTailLocal

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table form of the tail-local inverse-ratio product-update
    successor product witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_ne_zero_of_schur_invertible
    {m r : ℕ} (hr : 0 < r)
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
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNFull : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) A0
    let hTailPos : 0 < maxEntryNorm hNTail Atail :=
      maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
        hr Ablk pivotInv hpivot
    (invDiagBound : Fin ((m + 1) + 1) → ℝ) →
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ) →
    IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin ((m + 1) + 1),
      invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin ((m + 1) + 1),
      stageInvDiagBound 0 j = invDiagBound j) →
    SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) →
    (∀ k : ℕ, ∀ hk : k < (m + 1) + 1, ∀ i j : Fin ((m + 1) + 1),
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
              ⟨k, hk⟩ j)) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)) →
    (maxEntryNormRect hNTail hNTail AinvTail *
          maxEntryNormRect hNFull hNFull A0 ≤
        maxEntryNormRect hNFull hNFull AinvFull *
          maxEntryNormRect hNTail hNTail Atail) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
              blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hNFull hNFull A0 *
                maxEntryNormRect hNFull hNFull AinvFull) *
              maxEntryNormRect hNFull hNFull A0 := by
  dsimp only
  intro invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hReciprocal hProduct hDiagUpdate hInvRatio hTailLocal
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_ne_zero_of_schur_invertible
      hr Ablk pivotInv hpivot hdet n hsn hNn
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate hInvRatio hTailLocal

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero lower-comparison successor product witness with the
    Schur-tail positivity premise derived from first-split Schur-complement
    invertibility. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa_of_det_ne_zero_of_schur_invertible
    {m r : ℕ} (hr : 0 < r)
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
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNFull : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let Gfull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv
    let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) A0
    let hApos : 0 < maxEntryNorm hNFull A0 :=
      maxEntryNorm_pos_of_det_ne_zero hNFull A0 hdet
    let hTailPos : 0 < maxEntryNorm hNTail Atail :=
      maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
        hr Ablk pivotInv hpivot
    ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail) ≤
        (n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
              blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            (n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 3 *
              (maxEntryNormRect hNFull hNFull A0 *
                maxEntryNormRect hNFull hNFull AinvFull) *
              maxEntryNormRect hNFull hNFull A0 := by
  dsimp only
  intro hLower hTailLocal
  let hTailPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))) :=
    maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
      hr Ablk pivotInv hpivot
  let hApos :
      0 < maxEntryNorm (Nat.add_pos_left hr ((m + 1) * r))
        (blockMatrixFirstSplitFlat Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero
      (Nat.add_pos_left hr ((m + 1) * r)) (blockMatrixFirstSplitFlat Ablk) hdet
  simpa [hTailPos, hApos] using
    higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa_of_det_ne_zero
      hr Ablk pivotInv hpivot hTailPos hApos hdet n hsn hNn hLower hTailLocal

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero lower-comparison point-row successor product witness
    with the Schur-tail positivity premise derived from first-split
    Schur-complement invertibility. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa_of_det_ne_zero_of_schur_invertible
    {m r : ℕ} (hr : 0 < r)
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
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNFull : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let Gfull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv
    let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) A0
    let hApos : 0 < maxEntryNorm hNFull A0 :=
      maxEntryNorm_pos_of_det_ne_zero hNFull A0 hdet
    let hTailPos : 0 < maxEntryNorm hNTail Atail :=
      maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
        hr Ablk pivotInv hpivot
    growthFactorEntry hNFull A0 Gfull hApos ≤ 2 →
      ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail) ≤
        (n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
              blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hNFull hNFull A0 *
                maxEntryNormRect hNFull hNFull AinvFull) *
              maxEntryNormRect hNFull hNFull A0 := by
  dsimp only
  intro hRho_le_two hLower hTailLocal
  let hTailPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))) :=
    maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
      hr Ablk pivotInv hpivot
  let hApos :
      0 < maxEntryNorm (Nat.add_pos_left hr ((m + 1) * r))
        (blockMatrixFirstSplitFlat Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero
      (Nat.add_pos_left hr ((m + 1) * r)) (blockMatrixFirstSplitFlat Ablk) hdet
  simpa [hTailPos, hApos] using
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa_of_det_ne_zero
      hr Ablk pivotInv hpivot hTailPos hApos hdet n hsn hNn
      hRho_le_two hLower hTailLocal

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero lower-comparison point-row successor product witness
    whose `rho <= 2` side condition is supplied by the source-strength
    product-bound/diagonal-update BDD route.

    This is the product-update companion to
    `..._of_det_ne_zero_of_schur_invertible`: it keeps the direct
    tail-local lower-budget comparison explicit, but no longer asks callers to
    provide the raw full first-split growth-factor bound separately. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_ne_zero_of_schur_invertible
    {m r : ℕ} (hr : 0 < r)
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
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNFull : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let Gfull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv
    let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) A0
    let hApos : 0 < maxEntryNorm hNFull A0 :=
      maxEntryNorm_pos_of_det_ne_zero hNFull A0 hdet
    let hTailPos : 0 < maxEntryNorm hNTail Atail :=
      maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
        hr Ablk pivotInv hpivot
    (invDiagBound : Fin ((m + 1) + 1) → ℝ) →
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ) →
    IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin ((m + 1) + 1),
      invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin ((m + 1) + 1),
      stageInvDiagBound 0 j = invDiagBound j) →
    (∀ k : ℕ, ∀ hk : k < (m + 1) + 1,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1) →
    (∀ k : ℕ, ∀ hk : k < (m + 1) + 1, ∀ i j : Fin ((m + 1) + 1),
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
              ⟨k, hk⟩ j)) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)) →
    ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail) ≤
        (n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
              blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hNFull hNFull A0 *
                maxEntryNormRect hNFull hNFull AinvFull) *
              maxEntryNormRect hNFull hNFull A0 := by
  dsimp only
  intro invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hPivotInvBound hProduct hDiagUpdate hLower hTailLocal
  let hApos :
      0 < maxEntryNorm (Nat.add_pos_left hr ((m + 1) * r))
        (blockMatrixFirstSplitFlat Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero
      (Nat.add_pos_left hr ((m + 1) * r)) (blockMatrixFirstSplitFlat Ablk) hdet
  have hRho_le_two :
      growthFactorEntry (Nat.add_pos_left hr ((m + 1) * r))
          (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.add_pos_left hr ((m + 1) * r))
            (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos ≤
        2 := by
    simpa [hApos] using
      higham13_algorithm13_3_firstSplitStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hr (Nat.add_pos_left hr ((m + 1) * r)) Ablk pivotInv hApos
        invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
        hPivotInvBound hProduct hDiagUpdate
  simpa [hApos] using
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa_of_det_ne_zero_of_schur_invertible
      hr Ablk pivotInv hpivot hdet n hsn hNn hRho_le_two hLower hTailLocal

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table form of the tail-local lower-comparison product-update
    successor product witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_ne_zero_of_schur_invertible
    {m r : ℕ} (hr : 0 < r)
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
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNFull : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let Gfull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv
    let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) A0
    let hApos : 0 < maxEntryNorm hNFull A0 :=
      maxEntryNorm_pos_of_det_ne_zero hNFull A0 hdet
    let hTailPos : 0 < maxEntryNorm hNTail Atail :=
      maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
        hr Ablk pivotInv hpivot
    (invDiagBound : Fin ((m + 1) + 1) → ℝ) →
    (stageInvDiagBound : ℕ → Fin ((m + 1) + 1) → ℝ) →
    IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin ((m + 1) + 1),
      invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin ((m + 1) + 1),
      stageInvDiagBound 0 j = invDiagBound j) →
    SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) →
    (∀ k : ℕ, ∀ hk : k < (m + 1) + 1, ∀ i j : Fin ((m + 1) + 1),
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
              ⟨k, hk⟩ j)) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)) →
    ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail) ≤
        (n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
              blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hNFull hNFull A0 *
                maxEntryNormRect hNFull hNFull AinvFull) *
              maxEntryNormRect hNFull hNFull A0 := by
  dsimp only
  intro invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hReciprocal hProduct hDiagUpdate hLower hTailLocal
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_ne_zero_of_schur_invertible
      hr Ablk pivotInv hpivot hdet n hsn hNn
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate hLower hTailLocal

end NumStability
