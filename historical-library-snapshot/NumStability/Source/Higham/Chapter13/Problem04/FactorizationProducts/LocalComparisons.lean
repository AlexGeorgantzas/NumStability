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
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Problem04.FactorizationProducts.LowerBlockBudgets
import NumStability.Source.Higham.Chapter13.Problem04.LocalGrowth
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStages
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis

/-!
# Source.Higham.Chapter13.Problem04.FactorizationProducts.LocalComparisons

This module formalizes the source-facing Chapter 13 statements for
`Problem04.FactorizationProducts.LocalComparisons`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ `BlockLUFactSpec` witness from the canonical stage-local-growth
    source comparison route and exact pivot right-inverse certificates.

    Compared with the source-lower-block-budget witness, this wrapper no
    longer asks for the local lower-block estimates as hypotheses: they are
    supplied by the canonical local Problem 13.4 growth object.  The remaining
    visible source obligations are the local-to-full scalar comparison table. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hPivotRightAll : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hRhoLocal_le : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji) ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          (n : ℝ) *
            (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 3 *
            (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
                (blockMatrixFlatFin Ablk) *
              maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
            maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
              (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn
      (higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_source_comparisons_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn hInvPivot hInvSchur hInvFull
        (fun i j _hji => hPivotRightAll j.val j.isLt)
        hLocalApos hRhoLocal_le hKappaLocal_le)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ `BlockLUFactSpec` witness from the canonical
    stage-local-growth source comparison route, exact pivot right-inverse
    certificates, and the source `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hPivotRightAll : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hRhoLocal_le : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji) ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv))
    (hRho_le_two :
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos ≤ 2) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
                (blockMatrixFlatFin Ablk) *
              maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
            maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
              (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn
      (higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_source_comparisons_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn hInvPivot hInvSchur hInvFull
        (fun i j _hji => hPivotRightAll j.val j.isLt)
        hLocalApos hRhoLocal_le hKappaLocal_le)
      hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ `BlockLUFactSpec` witness from canonical stage-local growth,
    source comparisons, and canonical active pivots
    `pivotInv k = nonsingInv pivot_k`.

    This removes the explicit active-pivot right-inverse certificate from the
    source-comparison witness surface.  The local invertibility, local-to-full
    growth, and source condition-comparison tables remain explicit source
    obligations. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hPivotDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv k =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hRhoLocal_le : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji) ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          (n : ℝ) *
            (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 3 *
            (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
                (blockMatrixFlatFin Ablk) *
              maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
            maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
              (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hLocalApos hRhoLocal_le hKappaLocal_le

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ `BlockLUFactSpec` witness from canonical stage-local
    growth, source comparisons, canonical active pivots, and the source
    `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hPivotDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv k =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hRhoLocal_le : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji) ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv))
    (hRho_le_two :
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos ≤ 2) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
                (blockMatrixFlatFin Ablk) *
              maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
            maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
              (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hLocalApos hRhoLocal_le hKappaLocal_le
      hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ `BlockLUFactSpec` witness from canonical stage-local growth,
    exact pivot right-inverse certificates, an explicit local/global base
    comparison, and the source condition comparison. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hPivotRightAll : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hBaseLocal : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk) ≤
        maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hKappaLocal_le : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          (n : ℝ) *
            (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 3 *
            (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
                (blockMatrixFlatFin Ablk) *
              maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
            maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
              (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn
      (higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_base_comparisons_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn hInvPivot hInvSchur hInvFull
        (fun i j _hji => hPivotRightAll j.val j.isLt)
        hLocalApos hBaseLocal hKappaLocal_le)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ `BlockLUFactSpec` witness from canonical stage-local
    growth, exact pivot right-inverse certificates, an explicit local/global
    base comparison, the source condition comparison, and `rho <= 2`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hPivotRightAll : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hBaseLocal : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk) ≤
        maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hKappaLocal_le : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv))
    (hRho_le_two :
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos ≤ 2) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
                (blockMatrixFlatFin Ablk) *
              maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
            maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
              (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn
      (higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_base_comparisons_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn hInvPivot hInvSchur hInvFull
        (fun i j _hji => hPivotRightAll j.val j.isLt)
        hLocalApos hBaseLocal hKappaLocal_le)
      hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ `BlockLUFactSpec` witness from canonical stage-local growth,
    canonical active pivots, an explicit local/global base comparison, and the
    source condition comparison. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hPivotDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv k =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hBaseLocal : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk) ≤
        maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hKappaLocal_le : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          (n : ℝ) *
            (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 3 *
            (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
                (blockMatrixFlatFin Ablk) *
              maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
            maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
              (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hApos hRight n hNn hInvPivot hInvSchur hInvFull hLocalApos
      hBaseLocal hKappaLocal_le

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ `BlockLUFactSpec` witness from canonical stage-local
    growth, canonical active pivots, an explicit local/global base comparison,
    the source condition comparison, and `rho <= 2`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hPivotDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv k =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hBaseLocal : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk) ≤
        maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hKappaLocal_le : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv))
    (hRho_le_two :
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos ≤ 2) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
                (blockMatrixFlatFin Ablk) *
              maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
            maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
              (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hApos hRight n hNn hInvPivot hInvSchur hInvFull hLocalApos
      hBaseLocal hKappaLocal_le hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero exact-κ `BlockLUFactSpec` witness from the
    stage-local-growth base-comparison route and canonical active pivots.

    This uses the source-facing full inverse
    `nonsingInv (m*r) (blockMatrixFlatFin Ablk)` and derives the full positive
    denominator/right-inverse certificate from `det(blockMatrixFlatFin Ablk) ≠ 0`.
    The base and condition comparisons remain explicit source obligations. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv k =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)) :
    let hN : 0 < m * r := Nat.mul_pos hm hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNorm hN (blockMatrixFlatFin Ablk) ≤
        maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) →
    (∀ i j : Fin m, ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv (m * r) (blockMatrixFlatFin Ablk)))) →
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          (n : ℝ) *
            (growthFactorEntry hN (blockMatrixFlatFin Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN hm hr Ablk pivotInv) hApos) ^ 3 *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hBaseLocal hKappaLocal_le
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  let hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
    higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
      hr Ablk pivotInv hInvFull
  have hRight :
      IsRightInverse (m * r) (blockMatrixFlatFin Ablk)
        (nonsingInv (m * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      (m * r) (blockMatrixFlatFin Ablk) hdet).2
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hPivotDet hPivotInv hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hLocalApos hBaseLocal hKappaLocal_le

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero point-row exact-κ `BlockLUFactSpec` witness from the
    stage-local-growth base-comparison route, canonical active pivots, and the
    source `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv k =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)) :
    let hN : 0 < m * r := Nat.mul_pos hm hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNorm hN (blockMatrixFlatFin Ablk) ≤
        maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) →
    (∀ i j : Fin m, ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv (m * r) (blockMatrixFlatFin Ablk)))) →
    growthFactorEntry hN (blockMatrixFlatFin Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN hm hr Ablk pivotInv) hApos ≤ 2 →
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hBaseLocal hKappaLocal_le hRho_le_two
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  let hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
    higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
      hr Ablk pivotInv hInvFull
  have hRight :
      IsRightInverse (m * r) (blockMatrixFlatFin Ablk)
        (nonsingInv (m * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      (m * r) (blockMatrixFlatFin Ablk) hdet).2
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hPivotDet hPivotInv hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hLocalApos hBaseLocal hKappaLocal_le
      hRho_le_two

end NumStability
