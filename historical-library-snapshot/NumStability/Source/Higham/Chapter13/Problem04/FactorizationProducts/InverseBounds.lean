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
import NumStability.Source.Higham.Chapter13.Problem04.FactorizationProducts.LowerBlockBudgets
import NumStability.Source.Higham.Chapter13.Problem04.InfNormGrowth
import NumStability.Source.Higham.Chapter13.Problem04.LocalGrowth
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStages
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis
import NumStability.Source.Higham.Chapter13.Theorem02.Factorization

/-!
# Source.Higham.Chapter13.Problem04.FactorizationProducts.InverseBounds

This module formalizes the source-facing Chapter 13 statements for
`Problem04.FactorizationProducts.InverseBounds`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ `BlockLUFactSpec` witness from canonical stage-local growth, exact
    pivot right-inverse certificates, and an explicit local-inverse upper
    bound.

    This is the concrete witness counterpart of
    `higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa`.
    It keeps the source inverse comparison visible while discharging the
    multiplier and factor assembly bookkeeping. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_pivot_right_inverse
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
    (hInvLocal_le : ∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) :
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
      (higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_inverse_bound_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn hInvPivot hInvSchur hInvFull
        (fun i j _hji => hPivotRightAll j.val j.isLt) hInvLocal_le)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ `BlockLUFactSpec` witness from canonical stage-local
    growth, exact pivot right-inverse certificates, an explicit local-inverse
    upper bound, and the source `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_pivot_right_inverse
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
    (hInvLocal_le : ∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)
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
      (higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_inverse_bound_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn hInvPivot hInvSchur hInvFull
        (fun i j _hji => hPivotRightAll j.val j.isLt) hInvLocal_le)
      hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    `BlockLUFactSpec` witness from the direct stage-local inverse-bound route
    and the source-strength conditional active-stage product-bound/diagonal-
    update layer. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
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
    (hInvLocal_le : ∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le
      (higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hm hr Ablk pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
        hInitInv hPivotInvBound hProduct hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    `BlockLUFactSpec` witness from the direct inverse-bound product/update
    route with a reciprocal-table pivot certificate. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_product_bound_diag_update_reciprocal_of_pivot_right_inverse
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
    (hInvLocal_le : ∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le invDiagBound stageInvDiagBound
      hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    dimension-aware `BlockLUFactSpec` witness from the direct stage-local
    inverse-bound route and the diagonal lower-update layer. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_with_dim_factor_of_diag_update_of_pivot_right_inverse
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
    (hInvLocal_le : ∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      ((r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k)) *
          stageInvDiagBound k ⟨k, hk⟩ ≤
        1)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => (r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k))) :
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le
      (higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_with_dim_factor_of_diag_update
        hm hr Ablk pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
        hInitInv hPivotInvBound hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero exact-κ `BlockLUFactSpec` witness from the direct
    stage-local inverse-bound route.

    This is the canonical-inverse variant of
    `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_pivot_right_inverse`:
    it uses `nonsingInv (m*r) (blockMatrixFlatFin Ablk)` and derives the full
    positive denominator and right-inverse certificate from
    `det(blockMatrixFlatFin Ablk) != 0`. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRightAll : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
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
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos *
          maxEntryNormRect hN hN
            (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) →
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
  intro hInvLocal_le
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  have hRight :
      IsRightInverse (m * r) (blockMatrixFlatFin Ablk)
        (nonsingInv (m * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      (m * r) (blockMatrixFlatFin Ablk) hdet).2
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero point-row exact-κ `BlockLUFactSpec` witness from the
    direct stage-local inverse-bound route and the source `rho <= 2` side
    condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRightAll : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
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
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos *
          maxEntryNormRect hN hN
            (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) →
    (growthFactorEntry hN (blockMatrixFlatFin Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN hm hr Ablk pivotInv) hApos ≤ 2) →
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hInvLocal_le hRho_le_two
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  have hRight :
      IsRightInverse (m * r) (blockMatrixFlatFin Ablk)
        (nonsingInv (m * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      (m * r) (blockMatrixFlatFin Ablk) hdet).2
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero exact-κ `BlockLUFactSpec` witness from the direct
    inverse-bound route and the source-strength product-bound/diagonal-update
    proof layer. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRightAll : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
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
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos *
          maxEntryNormRect hN hN
            (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) →
    (invDiagBound : Fin m → ℝ) →
    (stageInvDiagBound : ℕ → Fin m → ℝ) →
    IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j) →
    (∀ k : ℕ, ∀ hk : k < m,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1) →
    (∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j)) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)) →
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hPivotInvBound hProduct hDiagUpdate
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  have hRight :
      IsRightInverse (m * r) (blockMatrixFlatFin Ablk)
        (nonsingInv (m * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      (m * r) (blockMatrixFlatFin Ablk) hdet).2
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le invDiagBound
      stageInvDiagBound hDom hDiagBound hInitInv hPivotInvBound hProduct
      hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero `BlockLUFactSpec` witness from the direct
    inverse-bound product/update route with a reciprocal-table pivot
    certificate. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_product_bound_diag_update_reciprocal_of_pivot_right_inverse_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRightAll : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
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
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos *
          maxEntryNormRect hN hN
            (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) →
    (invDiagBound : Fin m → ℝ) →
    (stageInvDiagBound : ℕ → Fin m → ℝ) →
    IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j) →
    SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) →
    (∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j)) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)) →
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hReciprocal hProduct hDiagUpdate
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse_of_det_ne_zero
      hm hr Ablk pivotInv hPivotRightAll hdet n hNn hInvPivot hInvSchur hInvFull
      hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero exact-κ `BlockLUFactSpec` witness from the direct
    inverse-bound route and the dimension-aware diagonal-update layer. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_with_dim_factor_of_diag_update_of_pivot_right_inverse_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRightAll : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
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
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos *
          maxEntryNormRect hN hN
            (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) →
    (invDiagBound : Fin m → ℝ) →
    (stageInvDiagBound : ℕ → Fin m → ℝ) →
    IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j) →
    (∀ k : ℕ, ∀ hk : k < m,
      ((r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k)) *
          stageInvDiagBound k ⟨k, hk⟩ ≤
        1) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => (r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k)) →
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hPivotInvBound hDiagUpdate
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  have hRight :
      IsRightInverse (m * r) (blockMatrixFlatFin Ablk)
        (nonsingInv (m * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      (m * r) (blockMatrixFlatFin Ablk) hdet).2
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_with_dim_factor_of_diag_update_of_pivot_right_inverse
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le invDiagBound
      stageInvDiagBound hDom hDiagBound hInitInv hPivotInvBound hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equations (13.22) and Problem 13.4:
    BDD first-Schur-tail determinant-nonzero direct stage-local inverse-bound
    witness.  The shifted recursive tail right-inverse table builds the
    all-active pivot right-inverse certificate internally. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (bddInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hBDDDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) bddInvDiagBound)
    (hBDDBound : ∀ j : Fin (m + 1), bddInvDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (Ablk (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1)))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv (m + 1) r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) →
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          (n : ℝ) *
            (growthFactorEntry hN (blockMatrixFlatFin Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 3 *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) :=
  higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
    (Nat.succ_pos m) hr Ablk pivotInv
    (higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTail)
    hdet n hNn hInvPivot hInvSchur hInvFull

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    BDD first-Schur-tail determinant-nonzero direct inverse-bound witness with
    a raw `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (bddInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hBDDDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) bddInvDiagBound)
    (hBDDBound : ∀ j : Fin (m + 1), bddInvDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (Ablk (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1)))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv (m + 1) r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) →
    (growthFactorEntry hN (blockMatrixFlatFin Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos m) hr Ablk pivotInv) hApos ≤ 2) →
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) :=
  higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
    (Nat.succ_pos m) hr Ablk pivotInv
    (higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTail)
    hdet n hNn hInvPivot hInvSchur hInvFull

/-- Higham, 2nd ed., Chapter 13, equations (13.22) and Problem 13.4:
    canonical-tail BDD first-Schur-tail determinant-nonzero direct
    stage-local inverse-bound witness. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (bddInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hBDDDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) bddInvDiagBound)
    (hBDDBound : ∀ j : Fin (m + 1), bddInvDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (Ablk (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv (m + 1) r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) →
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          (n : ℝ) *
            (growthFactorEntry hN (blockMatrixFlatFin Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 3 *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) :=
  higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
    (Nat.succ_pos m) hr Ablk pivotInv
    (higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0
      hTailDet hTailPivotInv)
    hdet n hNn hInvPivot hInvSchur hInvFull

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    canonical-tail BDD first-Schur-tail determinant-nonzero direct
    inverse-bound witness with a raw `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (bddInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hBDDDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) bddInvDiagBound)
    (hBDDBound : ∀ j : Fin (m + 1), bddInvDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (Ablk (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv (m + 1) r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) →
    (growthFactorEntry hN (blockMatrixFlatFin Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos m) hr Ablk pivotInv) hApos ≤ 2) →
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) :=
  higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
    (Nat.succ_pos m) hr Ablk pivotInv
    (higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0
      hTailDet hTailPivotInv)
    hdet n hNn hInvPivot hInvSchur hInvFull

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    BDD first-Schur-tail determinant-nonzero direct inverse-bound witness with
    product/update data deriving `rho <= 2`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (bddInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hBDDDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) bddInvDiagBound)
    (hBDDBound : ∀ j : Fin (m + 1), bddInvDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (Ablk (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1)))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv (m + 1) r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) →
    (invDiagBound : Fin (m + 1) → ℝ) →
    (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
    IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin (m + 1), invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin (m + 1), stageInvDiagBound 0 j = invDiagBound j) →
    (∀ k : ℕ, ∀ hk : k < m + 1,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1) →
    (∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j)) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)) →
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) :=
  higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse_of_det_ne_zero
    (Nat.succ_pos m) hr Ablk pivotInv
    (higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTail)
    hdet n hNn hInvPivot hInvSchur hInvFull

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    BDD first-Schur-tail determinant-nonzero direct inverse-bound witness with
    reciprocal-table product/update data.

    This is the reciprocal-table companion to the scalar shifted-tail wrapper:
    it builds the all-active pivot right-inverse certificate from the BDD tail
    data and lets the generic direct reciprocal route recover the scalar
    pivot-product premise. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update_reciprocal
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (bddInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hBDDDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) bddInvDiagBound)
    (hBDDBound : ∀ j : Fin (m + 1), bddInvDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (Ablk (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1)))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv (m + 1) r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) →
    (invDiagBound : Fin (m + 1) → ℝ) →
    (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
    IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin (m + 1), invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin (m + 1), stageInvDiagBound 0 j = invDiagBound j) →
    SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) →
    (∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j)) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)) →
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) :=
  higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_product_bound_diag_update_reciprocal_of_pivot_right_inverse_of_det_ne_zero
    (Nat.succ_pos m) hr Ablk pivotInv
    (higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTail)
    hdet n hNn hInvPivot hInvSchur hInvFull

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    canonical-tail BDD first-Schur-tail determinant-nonzero direct
    inverse-bound witness with product/update data deriving `rho <= 2`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (bddInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hBDDDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) bddInvDiagBound)
    (hBDDBound : ∀ j : Fin (m + 1), bddInvDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (Ablk (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv (m + 1) r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) →
    (invDiagBound : Fin (m + 1) → ℝ) →
    (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
    IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin (m + 1), invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin (m + 1), stageInvDiagBound 0 j = invDiagBound j) →
    (∀ k : ℕ, ∀ hk : k < m + 1,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1) →
    (∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j)) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)) →
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) :=
  higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse_of_det_ne_zero
    (Nat.succ_pos m) hr Ablk pivotInv
    (higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0
      hTailDet hTailPivotInv)
    hdet n hNn hInvPivot hInvSchur hInvFull

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    canonical-tail BDD first-Schur-tail determinant-nonzero direct
    inverse-bound witness with reciprocal-table product/update data. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update_reciprocal
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (bddInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hBDDDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) bddInvDiagBound)
    (hBDDBound : ∀ j : Fin (m + 1), bddInvDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (Ablk (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv (m + 1) r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) →
    (invDiagBound : Fin (m + 1) → ℝ) →
    (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
    IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin (m + 1), invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin (m + 1), stageInvDiagBound 0 j = invDiagBound j) →
    SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) →
    (∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j)) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)) →
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) :=
  higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_product_bound_diag_update_reciprocal_of_pivot_right_inverse_of_det_ne_zero
    (Nat.succ_pos m) hr Ablk pivotInv
    (higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0
      hTailDet hTailPivotInv)
    hdet n hNn hInvPivot hInvSchur hInvFull

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-kappa `BlockLUFactSpec` witness from canonical stage-local growth,
    exact pivot right-inverse certificates, and a plain local-inverse
    comparison.

    This is the concrete witness counterpart of
    `higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa`.
    It exposes the sharper source obligation
    `||A_local^{-1}||_max <= ||A^{-1}||_max`, while discharging the multiplier
    and factor-assembly bookkeeping. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse
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
    (hInvLocal_le : ∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) :
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
      (higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_plain_inverse_bound_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn hInvPivot hInvSchur hInvFull
        (fun i j _hji => hPivotRightAll j.val j.isLt) hInvLocal_le)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-kappa `BlockLUFactSpec` witness from canonical stage-local
    growth, exact pivot right-inverse certificates, a plain local-inverse
    comparison, and the source `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse
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
    (hInvLocal_le : ∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)
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
      (higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_plain_inverse_bound_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn hInvPivot hInvSchur hInvFull
        (fun i j _hji => hPivotRightAll j.val j.isLt) hInvLocal_le)
      hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero exact-kappa `BlockLUFactSpec` witness from the plain
    local-inverse comparison route.

    This is the canonical-inverse variant of
    `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse`:
    it uses `nonsingInv (m*r) (blockMatrixFlatFin Ablk)` and derives the full
    positive denominator and right-inverse certificate from
    `det(blockMatrixFlatFin Ablk) != 0`. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRightAll : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
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
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect hN hN
          (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) →
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
  intro hInvLocal_le
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  have hRight :
      IsRightInverse (m * r) (blockMatrixFlatFin Ablk)
        (nonsingInv (m * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      (m * r) (blockMatrixFlatFin Ablk) hdet).2
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero point-row exact-kappa `BlockLUFactSpec` witness from
    the plain local-inverse comparison route and the source `rho <= 2` side
    condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRightAll : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
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
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect hN hN
          (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) →
    (growthFactorEntry hN (blockMatrixFlatFin Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN hm hr Ablk pivotInv) hApos ≤ 2) →
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hInvLocal_le hRho_le_two
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  have hRight :
      IsRightInverse (m * r) (blockMatrixFlatFin Ablk)
        (nonsingInv (m * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      (m * r) (blockMatrixFlatFin Ablk) hdet).2
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    `BlockLUFactSpec` witness from the plain stage-local inverse-comparison
    route and the source-strength conditional active-stage product-bound/
    diagonal-update layer. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
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
    (hInvLocal_le : ∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le
      (higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hm hr Ablk pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
        hInitInv hPivotInvBound hProduct hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    `BlockLUFactSpec` witness from the plain stage-local inverse-comparison
    route and reciprocal-table product/update data. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_reciprocal_of_pivot_right_inverse
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
    (hInvLocal_le : ∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le invDiagBound
      stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    dimension-aware `BlockLUFactSpec` witness from the plain stage-local
    inverse-comparison route and the diagonal lower-update layer. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_with_dim_factor_of_diag_update_of_pivot_right_inverse
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
    (hInvLocal_le : ∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      ((r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k)) *
          stageInvDiagBound k ⟨k, hk⟩ ≤
        1)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => (r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k))) :
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le
      (higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_with_dim_factor_of_diag_update
        hm hr Ablk pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
        hInitInv hPivotInvBound hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero exact-κ `BlockLUFactSpec` witness from the plain
    inverse-comparison route and the source-strength product-bound/
    diagonal-update proof layer. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRightAll : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
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
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect hN hN
          (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) →
    (invDiagBound : Fin m → ℝ) →
    (stageInvDiagBound : ℕ → Fin m → ℝ) →
    IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j) →
    (∀ k : ℕ, ∀ hk : k < m,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1) →
    (∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j)) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)) →
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hPivotInvBound hProduct hDiagUpdate
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  have hRight :
      IsRightInverse (m * r) (blockMatrixFlatFin Ablk)
        (nonsingInv (m * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      (m * r) (blockMatrixFlatFin Ablk) hdet).2
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le invDiagBound
      stageInvDiagBound hDom hDiagBound hInitInv hPivotInvBound hProduct
      hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero exact-κ `BlockLUFactSpec` witness from the plain
    inverse-comparison route and reciprocal-table product/update data. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_reciprocal_of_pivot_right_inverse_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRightAll : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
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
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect hN hN
          (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) →
    (invDiagBound : Fin m → ℝ) →
    (stageInvDiagBound : ℕ → Fin m → ℝ) →
    IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j) →
    SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) →
    (∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j)) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)) →
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hReciprocal hProduct hDiagUpdate
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse_of_det_ne_zero
      hm hr Ablk pivotInv hPivotRightAll hdet n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le invDiagBound
      stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero exact-κ `BlockLUFactSpec` witness from the plain
    inverse-comparison route and the dimension-aware diagonal-update layer. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_with_dim_factor_of_diag_update_of_pivot_right_inverse_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRightAll : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
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
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect hN hN
          (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) →
    (invDiagBound : Fin m → ℝ) →
    (stageInvDiagBound : ℕ → Fin m → ℝ) →
    IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j) →
    (∀ k : ℕ, ∀ hk : k < m,
      ((r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k)) *
          stageInvDiagBound k ⟨k, hk⟩ ≤
        1) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => (r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k)) →
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hPivotInvBound hDiagUpdate
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  have hRight :
      IsRightInverse (m * r) (blockMatrixFlatFin Ablk)
        (nonsingInv (m * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      (m * r) (blockMatrixFlatFin Ablk) hdet).2
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_with_dim_factor_of_diag_update_of_pivot_right_inverse
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le invDiagBound
      stageInvDiagBound hDom hDiagBound hInitInv hPivotInvBound hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-kappa `BlockLUFactSpec` witness from canonical stage-local growth,
    canonical active pivots, and a plain local-inverse comparison.

    This removes the explicit active-pivot right-inverse certificate from
    `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse`. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivotInv_eq_nonsingInv
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
    (hInvLocal_le : ∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) :
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
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-kappa `BlockLUFactSpec` witness from canonical
    stage-local growth, canonical active pivots, a plain local-inverse
    comparison, and the source `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivotInv_eq_nonsingInv
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
    (hInvLocal_le : ∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero exact-kappa `BlockLUFactSpec` witness from the plain
    local-inverse comparison route and canonical active pivots. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivotInv_eq_nonsingInv_of_det_ne_zero
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
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect hN hN
          (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) →
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
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
      hm hr Ablk pivotInv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hdet n hNn hInvPivot hInvSchur hInvFull

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero point-row exact-kappa `BlockLUFactSpec` witness from
    the plain local-inverse comparison route, canonical active pivots, and the
    source `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivotInv_eq_nonsingInv_of_det_ne_zero
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
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect hN hN
          (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) →
    (growthFactorEntry hN (blockMatrixFlatFin Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN hm hr Ablk pivotInv) hApos ≤ 2) →
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
      hm hr Ablk pivotInv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hdet n hNn hInvPivot hInvSchur hInvFull

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    `BlockLUFactSpec` witness from the plain stage-local inverse-comparison
    route, canonical active pivots, and the source-strength conditional
    active-stage product-bound/diagonal-update layer. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivotInv_eq_nonsingInv
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
    (hInvLocal_le : ∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le invDiagBound
      stageInvDiagBound hDom hDiagBound hInitInv hPivotInvBound hProduct
      hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    `BlockLUFactSpec` witness from the plain stage-local inverse-comparison
    route, canonical active pivots, and reciprocal-table product/update data. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_reciprocal_of_pivotInv_eq_nonsingInv
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
    (hInvLocal_le : ∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivotInv_eq_nonsingInv
      hm hr Ablk pivotInv Ainv hPivotDet hPivotInv hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le invDiagBound
      stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    dimension-aware `BlockLUFactSpec` witness from the plain stage-local
    inverse-comparison route, canonical active pivots, and the diagonal lower
    update layer. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_with_dim_factor_of_diag_update_of_pivotInv_eq_nonsingInv
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
    (hInvLocal_le : ∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      ((r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k)) *
          stageInvDiagBound k ⟨k, hk⟩ ≤
        1)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => (r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k))) :
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_with_dim_factor_of_diag_update_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le invDiagBound
      stageInvDiagBound hDom hDiagBound hInitInv hPivotInvBound hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero exact-kappa `BlockLUFactSpec` witness from the plain
    inverse-comparison route, canonical active pivots, and the source-strength
    product-bound/diagonal-update proof layer. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivotInv_eq_nonsingInv_of_det_ne_zero
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
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect hN hN
          (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) →
    (invDiagBound : Fin m → ℝ) →
    (stageInvDiagBound : ℕ → Fin m → ℝ) →
    IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j) →
    (∀ k : ℕ, ∀ hk : k < m,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1) →
    (∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j)) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)) →
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse_of_det_ne_zero
      hm hr Ablk pivotInv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hdet n hNn hInvPivot hInvSchur hInvFull

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero exact-kappa `BlockLUFactSpec` witness from the plain
    inverse-comparison route, canonical active pivots, and reciprocal-table
    product/update data. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_reciprocal_of_pivotInv_eq_nonsingInv_of_det_ne_zero
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
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect hN hN
          (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) →
    (invDiagBound : Fin m → ℝ) →
    (stageInvDiagBound : ℕ → Fin m → ℝ) →
    IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j) →
    SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) →
    (∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j)) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)) →
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hReciprocal hProduct hDiagUpdate
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivotInv_eq_nonsingInv_of_det_ne_zero
      hm hr Ablk pivotInv hPivotDet hPivotInv hdet n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le invDiagBound
      stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero exact-kappa `BlockLUFactSpec` witness from the plain
    inverse-comparison route, canonical active pivots, and the
    dimension-aware diagonal-update proof layer. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_with_dim_factor_of_diag_update_of_pivotInv_eq_nonsingInv_of_det_ne_zero
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
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect hN hN
          (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) →
    (invDiagBound : Fin m → ℝ) →
    (stageInvDiagBound : ℕ → Fin m → ℝ) →
    IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j) →
    (∀ k : ℕ, ∀ hk : k < m,
      ((r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k)) *
          stageInvDiagBound k ⟨k, hk⟩ ≤
        1) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => (r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k)) →
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_with_dim_factor_of_diag_update_of_pivot_right_inverse_of_det_ne_zero
      hm hr Ablk pivotInv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hdet n hNn hInvPivot hInvSchur hInvFull

/-- Higham, 2nd ed., Chapter 13, equations (13.22) and Problem 13.4:
    BDD first-Schur-tail determinant-nonzero stage-local-growth
    plain-inverse witness.

    The BDD prefix data and shifted recursive tail right-inverse table build
    the all-active pivot right-inverse certificate internally.  The ambient
    exact-kappa object is the canonical full `nonsingInv`, while the sharper
    local inverse comparison remains the visible source obligation. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (bddInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hBDDDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) bddInvDiagBound)
    (hBDDBound : ∀ j : Fin (m + 1), bddInvDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (Ablk (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1)))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv (m + 1) r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect hN hN
          (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) →
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          (n : ℝ) *
            (growthFactorEntry hN (blockMatrixFlatFin Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 3 *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hInvLocal_le
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTail
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
      (Nat.succ_pos m) hr Ablk pivotInv hPivotRight hdet n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    BDD first-Schur-tail determinant-nonzero stage-local-growth
    plain-inverse witness with a raw `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (bddInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hBDDDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) bddInvDiagBound)
    (hBDDBound : ∀ j : Fin (m + 1), bddInvDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (Ablk (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1)))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv (m + 1) r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect hN hN
          (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) →
    (growthFactorEntry hN (blockMatrixFlatFin Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos m) hr Ablk pivotInv) hApos ≤ 2) →
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hInvLocal_le hRho_le_two
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTail
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
      (Nat.succ_pos m) hr Ablk pivotInv hPivotRight hdet n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equations (13.22) and Problem 13.4:
    canonical-tail version of the BDD first-Schur-tail determinant-nonzero
    stage-local-growth plain-inverse witness. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (bddInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hBDDDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) bddInvDiagBound)
    (hBDDBound : ∀ j : Fin (m + 1), bddInvDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (Ablk (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv (m + 1) r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect hN hN
          (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) →
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          (n : ℝ) *
            (growthFactorEntry hN (blockMatrixFlatFin Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 3 *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hInvLocal_le
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0
      hTailDet hTailPivotInv
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
      (Nat.succ_pos m) hr Ablk pivotInv hPivotRight hdet n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    canonical-tail version of the BDD first-Schur-tail determinant-nonzero
    stage-local-growth plain-inverse witness with `rho <= 2`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (bddInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hBDDDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) bddInvDiagBound)
    (hBDDBound : ∀ j : Fin (m + 1), bddInvDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (Ablk (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv (m + 1) r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect hN hN
          (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) →
    (growthFactorEntry hN (blockMatrixFlatFin Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos m) hr Ablk pivotInv) hApos ≤ 2) →
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hInvLocal_le hRho_le_two
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0
      hTailDet hTailPivotInv
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
      (Nat.succ_pos m) hr Ablk pivotInv hPivotRight hdet n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    BDD first-Schur-tail determinant-nonzero stage-local-growth
    plain-inverse witness with product/update data.

    The shifted recursive tail right-inverse table builds the all-active pivot
    certificate internally, while the product-bound/diagonal-update data
    supplies the Eq.13.23 `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (bddInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hBDDDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) bddInvDiagBound)
    (hBDDBound : ∀ j : Fin (m + 1), bddInvDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (Ablk (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1)))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv (m + 1) r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect hN hN
          (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) →
    (invDiagBound : Fin (m + 1) → ℝ) →
    (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
    IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin (m + 1), invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin (m + 1), stageInvDiagBound 0 j = invDiagBound j) →
    (∀ k : ℕ, ∀ hk : k < m + 1,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1) →
    (∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j)) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)) →
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hPivotInvBound hProduct hDiagUpdate
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTail
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse_of_det_ne_zero
      (Nat.succ_pos m) hr Ablk pivotInv hPivotRight hdet n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le invDiagBound
      stageInvDiagBound hDom hDiagBound hInitInv hPivotInvBound hProduct
      hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    canonical-tail BDD first-Schur-tail determinant-nonzero stage-local-growth
    plain-inverse witness with product/update data. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (bddInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hBDDDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) bddInvDiagBound)
    (hBDDBound : ∀ j : Fin (m + 1), bddInvDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (Ablk (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv (m + 1) r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect hN hN
          (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) →
    (invDiagBound : Fin (m + 1) → ℝ) →
    (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
    IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin (m + 1), invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin (m + 1), stageInvDiagBound 0 j = invDiagBound j) →
    (∀ k : ℕ, ∀ hk : k < m + 1,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1) →
    (∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j)) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)) →
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hPivotInvBound hProduct hDiagUpdate
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0
      hTailDet hTailPivotInv
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse_of_det_ne_zero
      (Nat.succ_pos m) hr Ablk pivotInv hPivotRight hdet n hNn
      hInvPivot hInvSchur hInvFull hInvLocal_le invDiagBound
      stageInvDiagBound hDom hDiagBound hInitInv hPivotInvBound hProduct
      hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    BDD first-Schur-tail determinant-nonzero stage-local-growth
    plain-inverse witness with reciprocal-table product/update data.

    This is the reciprocal-table companion to the scalar product/update
    shifted-tail witness: the Theorem 13.7-style reciprocal table supplies the
    scalar pivot-product premise used by the `rho <= 2` bridge. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update_reciprocal
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (bddInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hBDDDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) bddInvDiagBound)
    (hBDDBound : ∀ j : Fin (m + 1), bddInvDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (Ablk (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1)))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv (m + 1) r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect hN hN
          (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) →
    (invDiagBound : Fin (m + 1) → ℝ) →
    (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
    IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin (m + 1), invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin (m + 1), stageInvDiagBound 0 j = invDiagBound j) →
    SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) →
    (∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j)) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)) →
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hReciprocal hProduct hDiagUpdate
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0
      hTail hdet n hNn hInvPivot hInvSchur hInvFull hInvLocal_le
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    canonical-tail BDD first-Schur-tail determinant-nonzero
    stage-local-growth plain-inverse witness with reciprocal-table
    product/update data. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update_reciprocal
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (bddInvDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hBDDDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) bddInvDiagBound)
    (hBDDBound : ∀ j : Fin (m + 1), bddInvDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (Ablk (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv (m + 1) r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin (m + 1), j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect hN hN
          (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) →
    (invDiagBound : Fin (m + 1) → ℝ) →
    (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
    IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin (m + 1), invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin (m + 1), stageInvDiagBound 0 j = invDiagBound j) →
    SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) →
    (∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k ⟨k, hk⟩ j)) →
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k)) →
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hReciprocal hProduct hDiagUpdate
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0
      hTailDet hTailPivotInv hdet n hNn hInvPivot hInvSchur hInvFull
      hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

end NumStability
