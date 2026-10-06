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
import NumStability.Source.Higham.Chapter13.Problem04.InfNormGrowth
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStages
import NumStability.Source.Higham.Chapter13.Problem04.ProductBounds
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis
import NumStability.Source.Higham.Chapter13.Theorem02.Factorization

/-!
# Source.Higham.Chapter13.Problem04.FactorizationProducts.LowerBlockBudgets

This module formalizes the source-facing Chapter 13 statements for
`Problem04.FactorizationProducts.LowerBlockBudgets`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ matrix-stage-history `BlockLUFactSpec` witness from per-stage
    multiplier bounds.

    This is the witness version of
    `higham13_eq13_22_matrix_stage_history_product_from_multiplier_bounds_exact_kappa`.
    It keeps the true assembled product equality explicit. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hprod : ∀ (i j : Fin m) (s t : Fin r),
      ∑ k : Fin m, ∑ l : Fin r,
        higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv i k s l *
          higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv k j l t =
        Ablk i j s t)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) *
          (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
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
  let L : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv
  let U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv
  refine ⟨L, U, ?_, ?_⟩
  · simpa [L, U] using
      higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_product_eq
        Ablk pivotInv hprod
  · simpa [L, U] using
      higham13_eq13_22_matrix_stage_history_product_from_multiplier_bounds_exact_kappa
        hm hr Ablk pivotInv Ainv hApos hRight n hNn hLower

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    exact-κ point-row matrix-stage-history `BlockLUFactSpec` witness from
    per-stage multiplier bounds and `ρ_n <= 2`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hprod : ∀ (i j : Fin m) (s t : Fin r),
      ∑ k : Fin m, ∑ l : Fin r,
        higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv i k s l *
          higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv k j l t =
        Ablk i j s t)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) *
          (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
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
  let L : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv
  let U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv
  refine ⟨L, U, ?_, ?_⟩
  · simpa [L, U] using
      higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_product_eq
        Ablk pivotInv hprod
  · simpa [L, U] using
      higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa
        hm hr Ablk pivotInv Ainv hApos hRight n hNn hLower hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ matrix-stage-history `BlockLUFactSpec` witness from per-stage
    multiplier bounds and explicit pivot-left-inverse certificates. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivot_left_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hPivotLeft : ∀ k : ℕ, ∀ hk : k < m,
      IsLeftInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) *
          (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
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
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_matrixStages_product_eq_of_pivot_left_inverse
        Ablk pivotInv hPivotLeft)
      hApos hRight n hNn hLower

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    exact-κ point-row matrix-stage-history `BlockLUFactSpec` witness from
    per-stage multiplier bounds, explicit pivot-left-inverse certificates, and
    `ρ_n <= 2`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivot_left_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hPivotLeft : ∀ k : ℕ, ∀ hk : k < m,
      IsLeftInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) *
          (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_matrixStages_product_eq_of_pivot_left_inverse
        Ablk pivotInv hPivotLeft)
      hApos hRight n hNn hLower hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ matrix-stage-history `BlockLUFactSpec` witness from per-stage
    multiplier bounds and exact pivot right-inverse certificates. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) *
          (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
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
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivot_left_inverse
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_pivot_left_inverse_of_pivot_right_inverse
        Ablk pivotInv hPivotRight)
      hApos hRight n hNn hLower

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    exact-κ point-row matrix-stage-history `BlockLUFactSpec` witness from
    per-stage multiplier bounds, exact pivot right-inverse certificates, and
    `ρ_n <= 2`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) *
          (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivot_left_inverse
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_pivot_left_inverse_of_pivot_right_inverse
        Ablk pivotInv hPivotRight)
      hApos hRight n hNn hLower hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ matrix-stage-history `BlockLUFactSpec` witness from per-stage
    multiplier bounds and canonical active pivots
    `pivotInv k = nonsingInv pivot_k`. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivotInv_eq_nonsingInv
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
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) *
          (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
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
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hApos hRight n hNn hLower

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    exact-κ point-row matrix-stage-history `BlockLUFactSpec` witness from
    per-stage multiplier bounds, `ρ_n <= 2`, and canonical active pivots
    `pivotInv k = nonsingInv pivot_k`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivotInv_eq_nonsingInv
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
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) *
          (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
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
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hApos hRight n hNn hLower hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ `BlockLUFactSpec` witness from source-shaped local Problem 13.4
    lower-block budgets and exact pivot right-inverse certificates.

    This removes the black-box per-stage multiplier-bound hypothesis from the
    pivot-right witness surface, replacing it by local lower-block estimates
    `r * rhoLocal * kappaLocal` and the scalar comparisons used in the book's
    Eq.13.22 derivation. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (rhoLocal kappaLocal : Fin m → Fin m → ℝ)
    (hLocal : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j)
    (hRhoLocal_nonneg : ∀ i j : Fin m, j.val < i.val → 0 ≤ rhoLocal i j)
    (hRhoLocal_le : ∀ i j : Fin m, j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin m, j.val < i.val →
      kappaLocal i j ≤
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
      hm hr Ablk pivotInv Ainv hPivotRight hApos hRight n hNn
      (higham13_algorithm13_3_multiplier_bounds_from_source_lblock_budgets_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn rhoLocal kappaLocal
        hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ `BlockLUFactSpec` witness from source-shaped local
    Problem 13.4 lower-block budgets, exact pivot right-inverse certificates,
    and the source `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (rhoLocal kappaLocal : Fin m → Fin m → ℝ)
    (hLocal : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j)
    (hRhoLocal_nonneg : ∀ i j : Fin m, j.val < i.val → 0 ≤ rhoLocal i j)
    (hRhoLocal_le : ∀ i j : Fin m, j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin m, j.val < i.val →
      kappaLocal i j ≤
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
      hm hr Ablk pivotInv Ainv hPivotRight hApos hRight n hNn
      (higham13_algorithm13_3_multiplier_bounds_from_source_lblock_budgets_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn rhoLocal kappaLocal
        hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le)
      hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ `BlockLUFactSpec` witness from source-shaped local Problem 13.4
    lower-block budgets and canonical active pivots.

    This is the canonical active-pivot variant of
    `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivot_right_inverse`. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivotInv_eq_nonsingInv
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
    (rhoLocal kappaLocal : Fin m → Fin m → ℝ)
    (hLocal : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j)
    (hRhoLocal_nonneg : ∀ i j : Fin m, j.val < i.val → 0 ≤ rhoLocal i j)
    (hRhoLocal_le : ∀ i j : Fin m, j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin m, j.val < i.val →
      kappaLocal i j ≤
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
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hApos hRight n hNn rhoLocal kappaLocal
      hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ `BlockLUFactSpec` witness from source-shaped local
    Problem 13.4 lower-block budgets, canonical active pivots, and the source
    `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivotInv_eq_nonsingInv
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
    (rhoLocal kappaLocal : Fin m → Fin m → ℝ)
    (hLocal : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j)
    (hRhoLocal_nonneg : ∀ i j : Fin m, j.val < i.val → 0 ≤ rhoLocal i j)
    (hRhoLocal_le : ∀ i j : Fin m, j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin m, j.val < i.val →
      kappaLocal i j ≤
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hApos hRight n hNn rhoLocal kappaLocal
      hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ `BlockLUFactSpec` witness from source-shaped local
    Problem 13.4 lower-block budgets, exact pivot right-inverse certificates,
    and the matrix-stage BDD `rho <= 2` proof layer.

    This is the non-determinant witness companion to
    `higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update`:
    the full inverse certificate remains explicit, while the final
    growth-factor bound is derived from the supplied diagonal-update/product
    data instead of being taken as a raw `rho <= 2` hypothesis. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (rhoLocal kappaLocal : Fin m → Fin m → ℝ)
    (hLocal : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j)
    (hRhoLocal_nonneg : ∀ i j : Fin m, j.val < i.val → 0 ≤ rhoLocal i j)
    (hRhoLocal_le : ∀ i j : Fin m, j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin m, j.val < i.val →
      kappaLocal i j ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv))
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
  let L : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv
  let U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv
  refine ⟨L, U, ?_, ?_⟩
  · simpa [L, U] using
      higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_product_eq
        Ablk pivotInv
        (higham13_algorithm13_3_matrixStages_product_eq_of_pivot_right_inverse
          Ablk pivotInv hPivotRight)
  · simpa [L, U] using
      higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update
        hm hr Ablk pivotInv Ainv hApos hRight n hNn rhoLocal kappaLocal
        hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
        invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
        hPivotInvBound hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ `BlockLUFactSpec` witness from source-shaped local
    Problem 13.4 lower-block budgets, canonical active pivots, and the
    matrix-stage BDD `rho <= 2` proof layer.

    This removes the explicit active pivot right-inverse table from the
    preceding non-determinant product-update witness, deriving it from active
    pivot determinant nonzero plus `pivotInv = nonsingInv`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update_of_pivotInv_eq_nonsingInv
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
    (rhoLocal kappaLocal : Fin m → Fin m → ℝ)
    (hLocal : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j)
    (hRhoLocal_nonneg : ∀ i j : Fin m, j.val < i.val → 0 ≤ rhoLocal i j)
    (hRhoLocal_le : ∀ i j : Fin m, j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin m, j.val < i.val →
      kappaLocal i j ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv))
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hApos hRight n hNn rhoLocal kappaLocal
      hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hPivotInvBound hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table `BlockLUFactSpec` witness from source-shaped local
    Problem 13.4 lower-block budgets and exact pivot right-inverse
    certificates.

    This is the source-style companion to
    `..._of_product_bound_diag_update_of_pivot_right_inverse`: callers may
    provide the active reciprocal pivot table used in the printed BDD proof
    instead of the scalar pivot-product bound. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update_reciprocal_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (rhoLocal kappaLocal : Fin m → Fin m → ℝ)
    (hLocal : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j)
    (hRhoLocal_nonneg : ∀ i j : Fin m, j.val < i.val → 0 ≤ rhoLocal i j)
    (hRhoLocal_le : ∀ i j : Fin m, j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin m, j.val < i.val →
      kappaLocal i j ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv))
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
  let L : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv
  let U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv
  refine ⟨L, U, ?_, ?_⟩
  · simpa [L, U] using
      higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_product_eq
        Ablk pivotInv
        (higham13_algorithm13_3_matrixStages_product_eq_of_pivot_right_inverse
          Ablk pivotInv hPivotRight)
  · simpa [L, U] using
      higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update_reciprocal
        hm hr Ablk pivotInv Ainv hApos hRight n hNn rhoLocal kappaLocal
        hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
        invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
        hReciprocal hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table `BlockLUFactSpec` witness from source-shaped local
    Problem 13.4 lower-block budgets and canonical active pivots.

    This removes both the explicit active pivot right-inverse table and the
    scalar pivot-product proof artifact from the source-lower-block
    product/update surface. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update_reciprocal_of_pivotInv_eq_nonsingInv
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
    (rhoLocal kappaLocal : Fin m → Fin m → ℝ)
    (hLocal : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j)
    (hRhoLocal_nonneg : ∀ i j : Fin m, j.val < i.val → 0 ≤ rhoLocal i j)
    (hRhoLocal_le : ∀ i j : Fin m, j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin m, j.val < i.val →
      kappaLocal i j ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv))
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update_reciprocal_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hApos hRight n hNn rhoLocal kappaLocal
      hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hReciprocal hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equations (13.22) and Problem 13.4:
    exact-κ `BlockLUFactSpec` witness from source-shaped lower-block budgets
    and matrix-`∞` BDD first-Schur-tail data.

    This is the first-tail BDD variant of the source-lower-block Eq.13.22
    product witness.  The BDD hypotheses and shifted tail right-inverse table
    build the all-active pivot right-inverse certificate internally; the
    genuine source obligations remain the local lower-block estimates and the
    scalar comparison table. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (Ablk (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1)))
    (hApos : 0 < maxEntryNorm
      (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse ((m + 1) * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (rhoLocal kappaLocal : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hLocal : ∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j)
    (hRhoLocal_nonneg : ∀ i j : Fin (m + 1), j.val < i.val → 0 ≤ rhoLocal i j)
    (hRhoLocal_le : ∀ i j : Fin (m + 1), j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin (m + 1), j.val < i.val →
      kappaLocal i j ≤
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
            (Nat.mul_pos (Nat.succ_pos m) hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
            (Nat.mul_pos (Nat.succ_pos m) hr) Ainv)) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          (n : ℝ) *
            (growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 3 *
            (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
                (Nat.mul_pos (Nat.succ_pos m) hr)
                (blockMatrixFlatFin Ablk) *
              maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
                (Nat.mul_pos (Nat.succ_pos m) hr) Ainv) *
            maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
              (Nat.mul_pos (Nat.succ_pos m) hr)
              (blockMatrixFlatFin Ablk) := by
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTail
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv Ainv hPivotRight hApos hRight n hNn
      rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    point-row exact-κ source-lower-block witness from matrix-`∞` BDD
    first-Schur-tail data and the explicit source `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (Ablk (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1)))
    (hApos : 0 < maxEntryNorm
      (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse ((m + 1) * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (rhoLocal kappaLocal : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hLocal : ∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j)
    (hRhoLocal_nonneg : ∀ i j : Fin (m + 1), j.val < i.val → 0 ≤ rhoLocal i j)
    (hRhoLocal_le : ∀ i j : Fin (m + 1), j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin (m + 1), j.val < i.val →
      kappaLocal i j ≤
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
            (Nat.mul_pos (Nat.succ_pos m) hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
            (Nat.mul_pos (Nat.succ_pos m) hr) Ainv))
    (hRho_le_two :
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos ≤ 2) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
                (Nat.mul_pos (Nat.succ_pos m) hr)
                (blockMatrixFlatFin Ablk) *
              maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
                (Nat.mul_pos (Nat.succ_pos m) hr) Ainv) *
            maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
              (Nat.mul_pos (Nat.succ_pos m) hr)
              (blockMatrixFlatFin Ablk) := by
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTail
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv Ainv hPivotRight hApos hRight n hNn
      rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
      hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equations (13.22) and Problem 13.4:
    canonical-pivot version of the BDD first-Schur-tail source-lower-block
    exact-κ product witness.  The tail stores each pivot as `nonsingInv`;
    this wrapper derives the all-active right-inverse table before invoking
    the generic source-lower-block Eq.13.22 witness. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
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
    (hApos : 0 < maxEntryNorm
      (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse ((m + 1) * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (rhoLocal kappaLocal : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hLocal : ∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j)
    (hRhoLocal_nonneg : ∀ i j : Fin (m + 1), j.val < i.val → 0 ≤ rhoLocal i j)
    (hRhoLocal_le : ∀ i j : Fin (m + 1), j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin (m + 1), j.val < i.val →
      kappaLocal i j ≤
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
            (Nat.mul_pos (Nat.succ_pos m) hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
            (Nat.mul_pos (Nat.succ_pos m) hr) Ainv)) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          (n : ℝ) *
            (growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 3 *
            (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
                (Nat.mul_pos (Nat.succ_pos m) hr)
                (blockMatrixFlatFin Ablk) *
              maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
                (Nat.mul_pos (Nat.succ_pos m) hr) Ainv) *
            maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
              (Nat.mul_pos (Nat.succ_pos m) hr)
              (blockMatrixFlatFin Ablk) := by
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTailDet hTailPivotInv
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv Ainv hPivotRight hApos hRight n hNn
      rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    canonical-pivot BDD first-Schur-tail source-lower-block point-row witness
    with the source `rho <= 2` condition kept explicit. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
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
    (hApos : 0 < maxEntryNorm
      (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse ((m + 1) * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (rhoLocal kappaLocal : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hLocal : ∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j)
    (hRhoLocal_nonneg : ∀ i j : Fin (m + 1), j.val < i.val → 0 ≤ rhoLocal i j)
    (hRhoLocal_le : ∀ i j : Fin (m + 1), j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin (m + 1), j.val < i.val →
      kappaLocal i j ≤
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
            (Nat.mul_pos (Nat.succ_pos m) hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
            (Nat.mul_pos (Nat.succ_pos m) hr) Ainv))
    (hRho_le_two :
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos ≤ 2) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
                (Nat.mul_pos (Nat.succ_pos m) hr)
                (blockMatrixFlatFin Ablk) *
              maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
                (Nat.mul_pos (Nat.succ_pos m) hr) Ainv) *
            maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
              (Nat.mul_pos (Nat.succ_pos m) hr)
              (blockMatrixFlatFin Ablk) := by
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTailDet hTailPivotInv
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv Ainv hPivotRight hApos hRight n hNn
      rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
      hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    non-determinant point-row source-lower-block witness from matrix-`∞` BDD
    first-Schur-tail data and source product/update data.

    This is the explicit-full-inverse companion to the raw BDD source-lower-
    block Eq.13.23 wrapper above: the ambient right-inverse certificate remains
    an input, but the global `rho <= 2` side condition is discharged by the
    product-bound/diagonal-update route. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_product_bound_diag_update
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ)
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
    (hApos : 0 < maxEntryNorm
      (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse ((m + 1) * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (rhoLocal kappaLocal : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hLocal : ∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j)
    (hRhoLocal_nonneg : ∀ i j : Fin (m + 1), j.val < i.val → 0 ≤ rhoLocal i j)
    (hRhoLocal_le : ∀ i j : Fin (m + 1), j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin (m + 1), j.val < i.val →
      kappaLocal i j ≤
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
            (Nat.mul_pos (Nat.succ_pos m) hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
            (Nat.mul_pos (Nat.succ_pos m) hr) Ainv))
    (entryInvDiagBound : Fin (m + 1) → ℝ)
    (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ)
    (hEntryDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => maxEntryNorm hr (Ablk i j)) entryInvDiagBound)
    (hEntryDiagBound :
      ∀ j : Fin (m + 1), entryInvDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hEntryInit : ∀ j : Fin (m + 1), stageInvDiagBound 0 j = entryInvDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m + 1,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
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
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
                (Nat.mul_pos (Nat.succ_pos m) hr)
                (blockMatrixFlatFin Ablk) *
              maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
                (Nat.mul_pos (Nat.succ_pos m) hr) Ainv) *
            maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
              (Nat.mul_pos (Nat.succ_pos m) hr)
              (blockMatrixFlatFin Ablk) := by
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTail
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv Ainv hPivotRight hApos hRight n hNn
      rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
      entryInvDiagBound stageInvDiagBound hEntryDom hEntryDiagBound hEntryInit
      hPivotInvBound hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    canonical-tail version of the non-determinant BDD first-Schur-tail
    source-lower-block product/update witness.

    The tail stores each recursive active pivot as `nonsingInv`; the BDD
    prefix data and first pivot identity build the all-active right-inverse
    table before invoking the explicit-full-inverse product/update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_product_bound_diag_update
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ)
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
    (hApos : 0 < maxEntryNorm
      (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse ((m + 1) * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (rhoLocal kappaLocal : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hLocal : ∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j)
    (hRhoLocal_nonneg : ∀ i j : Fin (m + 1), j.val < i.val → 0 ≤ rhoLocal i j)
    (hRhoLocal_le : ∀ i j : Fin (m + 1), j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin (m + 1), j.val < i.val →
      kappaLocal i j ≤
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
            (Nat.mul_pos (Nat.succ_pos m) hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
            (Nat.mul_pos (Nat.succ_pos m) hr) Ainv))
    (entryInvDiagBound : Fin (m + 1) → ℝ)
    (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ)
    (hEntryDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => maxEntryNorm hr (Ablk i j)) entryInvDiagBound)
    (hEntryDiagBound :
      ∀ j : Fin (m + 1), entryInvDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hEntryInit : ∀ j : Fin (m + 1), stageInvDiagBound 0 j = entryInvDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m + 1,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
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
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
                (Nat.mul_pos (Nat.succ_pos m) hr)
                (blockMatrixFlatFin Ablk) *
              maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
                (Nat.mul_pos (Nat.succ_pos m) hr) Ainv) *
            maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
              (Nat.mul_pos (Nat.succ_pos m) hr)
              (blockMatrixFlatFin Ablk) := by
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTailDet
      hTailPivotInv
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv Ainv hPivotRight hApos hRight n hNn
      rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
      entryInvDiagBound stageInvDiagBound hEntryDom hEntryDiagBound hEntryInit
      hPivotInvBound hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    determinant-nonzero point-row source-lower-block witness from matrix-`∞`
    BDD first-Schur-tail data and source product/update data.

    This is the shifted-tail counterpart of the BDD source-lower-block
    Eq.13.23 wrapper above, but the global `rho <= 2` side condition is
    discharged by the product-bound/diagonal-update route. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update
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
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    ∀ rhoLocal kappaLocal : Fin (m + 1) → Fin (m + 1) → ℝ,
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j) →
    (∀ i j : Fin (m + 1), j.val < i.val → 0 ≤ rhoLocal i j) →
    (∀ i j : Fin (m + 1), j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) →
    (∀ i j : Fin (m + 1), j.val < i.val →
      kappaLocal i j ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
    (entryInvDiagBound : Fin (m + 1) → ℝ) →
    (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
    IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => maxEntryNorm hr (Ablk i j)) entryInvDiagBound →
    (∀ j : Fin (m + 1), entryInvDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin (m + 1), stageInvDiagBound 0 j = entryInvDiagBound j) →
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
  intro rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le
    hKappaLocal_le entryInvDiagBound stageInvDiagBound hEntryDom hEntryDiagBound
    hEntryInit hPivotInvBound hProduct hDiagUpdate
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTail
  let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv
      (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)) hPivotRight hApos
      ((isInverse_nonsingInv_of_det_ne_zero ((m + 1) * r)
        (blockMatrixFlatFin Ablk) hdet).2)
      n hNn
      rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
      (higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        (Nat.succ_pos m) hr Ablk pivotInv hApos entryInvDiagBound stageInvDiagBound
        hEntryDom hEntryDiagBound hEntryInit hPivotInvBound hProduct hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    canonical-tail version of the BDD first-Schur-tail source-lower-block
    product/update witness.

    The tail stores each recursive active pivot as `nonsingInv`; the BDD
    prefix data and first pivot identity build the all-active right-inverse
    table before invoking the determinant/product-update Eq.13.23 witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update
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
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    ∀ rhoLocal kappaLocal : Fin (m + 1) → Fin (m + 1) → ℝ,
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j) →
    (∀ i j : Fin (m + 1), j.val < i.val → 0 ≤ rhoLocal i j) →
    (∀ i j : Fin (m + 1), j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) →
    (∀ i j : Fin (m + 1), j.val < i.val →
      kappaLocal i j ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
    (entryInvDiagBound : Fin (m + 1) → ℝ) →
    (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
    IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => maxEntryNorm hr (Ablk i j)) entryInvDiagBound →
    (∀ j : Fin (m + 1), entryInvDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin (m + 1), stageInvDiagBound 0 j = entryInvDiagBound j) →
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
  intro rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le
    hKappaLocal_le entryInvDiagBound stageInvDiagBound hEntryDom hEntryDiagBound
    hEntryInit hPivotInvBound hProduct hDiagUpdate
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTailDet
      hTailPivotInv
  let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv
      (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)) hPivotRight hApos
      ((isInverse_nonsingInv_of_det_ne_zero ((m + 1) * r)
        (blockMatrixFlatFin Ablk) hdet).2)
      n hNn
      rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
      (higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        (Nat.succ_pos m) hr Ablk pivotInv hApos entryInvDiagBound stageInvDiagBound
        hEntryDom hEntryDiagBound hEntryInit hPivotInvBound hProduct hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    reciprocal-table companion to the non-determinant BDD first-Schur-tail
    source-lower-block product/update witness.

    The shifted-tail BDD data still supply the all-active pivot right-inverse
    table; the active reciprocal table replaces the scalar pivot-product
    proof artifact. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_product_bound_diag_update_reciprocal
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ)
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
    (hApos : 0 < maxEntryNorm
      (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse ((m + 1) * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (rhoLocal kappaLocal : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hLocal : ∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j)
    (hRhoLocal_nonneg : ∀ i j : Fin (m + 1), j.val < i.val → 0 ≤ rhoLocal i j)
    (hRhoLocal_le : ∀ i j : Fin (m + 1), j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin (m + 1), j.val < i.val →
      kappaLocal i j ≤
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
            (Nat.mul_pos (Nat.succ_pos m) hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
            (Nat.mul_pos (Nat.succ_pos m) hr) Ainv))
    (entryInvDiagBound : Fin (m + 1) → ℝ)
    (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ)
    (hEntryDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => maxEntryNorm hr (Ablk i j)) entryInvDiagBound)
    (hEntryDiagBound :
      ∀ j : Fin (m + 1), entryInvDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hEntryInit : ∀ j : Fin (m + 1), stageInvDiagBound 0 j = entryInvDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
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
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
                (Nat.mul_pos (Nat.succ_pos m) hr)
                (blockMatrixFlatFin Ablk) *
              maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
                (Nat.mul_pos (Nat.succ_pos m) hr) Ainv) *
            maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
              (Nat.mul_pos (Nat.succ_pos m) hr)
              (blockMatrixFlatFin Ablk) := by
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTail
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update_reciprocal_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv Ainv hPivotRight hApos hRight n hNn
      rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
      entryInvDiagBound stageInvDiagBound hEntryDom hEntryDiagBound hEntryInit
      hReciprocal hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    canonical-tail reciprocal-table companion to the non-determinant BDD
    first-Schur-tail source-lower-block product/update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_product_bound_diag_update_reciprocal
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ)
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
    (hApos : 0 < maxEntryNorm
      (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse ((m + 1) * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (rhoLocal kappaLocal : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hLocal : ∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j)
    (hRhoLocal_nonneg : ∀ i j : Fin (m + 1), j.val < i.val → 0 ≤ rhoLocal i j)
    (hRhoLocal_le : ∀ i j : Fin (m + 1), j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos)
    (hKappaLocal_le : ∀ i j : Fin (m + 1), j.val < i.val →
      kappaLocal i j ≤
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
            (Nat.mul_pos (Nat.succ_pos m) hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
            (Nat.mul_pos (Nat.succ_pos m) hr) Ainv))
    (entryInvDiagBound : Fin (m + 1) → ℝ)
    (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ)
    (hEntryDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => maxEntryNorm hr (Ablk i j)) entryInvDiagBound)
    (hEntryDiagBound :
      ∀ j : Fin (m + 1), entryInvDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hEntryInit : ∀ j : Fin (m + 1), stageInvDiagBound 0 j = entryInvDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
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
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
                (Nat.mul_pos (Nat.succ_pos m) hr)
                (blockMatrixFlatFin Ablk) *
              maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
                (Nat.mul_pos (Nat.succ_pos m) hr) Ainv) *
            maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
              (Nat.mul_pos (Nat.succ_pos m) hr)
              (blockMatrixFlatFin Ablk) := by
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTailDet
      hTailPivotInv
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update_reciprocal_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv Ainv hPivotRight hApos hRight n hNn
      rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
      entryInvDiagBound stageInvDiagBound hEntryDom hEntryDiagBound hEntryInit
      hReciprocal hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    determinant-nonzero reciprocal-table companion to the shifted-tail BDD
    first-Schur-tail source-lower-block product/update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update_reciprocal
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
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    ∀ rhoLocal kappaLocal : Fin (m + 1) → Fin (m + 1) → ℝ,
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j) →
    (∀ i j : Fin (m + 1), j.val < i.val → 0 ≤ rhoLocal i j) →
    (∀ i j : Fin (m + 1), j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) →
    (∀ i j : Fin (m + 1), j.val < i.val →
      kappaLocal i j ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
    (entryInvDiagBound : Fin (m + 1) → ℝ) →
    (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
    IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => maxEntryNorm hr (Ablk i j)) entryInvDiagBound →
    (∀ j : Fin (m + 1), entryInvDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin (m + 1), stageInvDiagBound 0 j = entryInvDiagBound j) →
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
  intro rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le
    hKappaLocal_le entryInvDiagBound stageInvDiagBound hEntryDom hEntryDiagBound
    hEntryInit hReciprocal hProduct hDiagUpdate
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTail hdet n hNn
      rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
      entryInvDiagBound stageInvDiagBound hEntryDom hEntryDiagBound hEntryInit
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    determinant-nonzero reciprocal-table companion to the canonical-tail BDD
    first-Schur-tail source-lower-block product/update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update_reciprocal
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
    (n : ℕ) (hNn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    ∀ rhoLocal kappaLocal : Fin (m + 1) → Fin (m + 1) → ℝ,
    (∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j) →
    (∀ i j : Fin (m + 1), j.val < i.val → 0 ≤ rhoLocal i j) →
    (∀ i j : Fin (m + 1), j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) →
    (∀ i j : Fin (m + 1), j.val < i.val →
      kappaLocal i j ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
    (entryInvDiagBound : Fin (m + 1) → ℝ) →
    (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
    IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => maxEntryNorm hr (Ablk i j)) entryInvDiagBound →
    (∀ j : Fin (m + 1), entryInvDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin (m + 1), stageInvDiagBound 0 j = entryInvDiagBound j) →
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
  intro rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le
    hKappaLocal_le entryInvDiagBound stageInvDiagBound hEntryDom hEntryDiagBound
    hEntryInit hReciprocal hProduct hDiagUpdate
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTailDet
      hTailPivotInv hdet n hNn
      rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
      entryInvDiagBound stageInvDiagBound hEntryDom hEntryDiagBound hEntryInit
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

end NumStability
