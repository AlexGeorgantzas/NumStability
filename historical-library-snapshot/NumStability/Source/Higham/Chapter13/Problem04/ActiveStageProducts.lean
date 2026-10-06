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
import NumStability.Algorithms.LinearSystems.LU.BlockLU.GrowthBounds
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Problem04.ActiveStageBounds
import NumStability.Source.Higham.Chapter13.Problem04.LocalGrowth
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStages
import NumStability.Source.Higham.Chapter13.Problem04.ProductBounds
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis

/-!
# Source.Higham.Chapter13.Problem04.ActiveStageProducts

This module formalizes the source-facing Chapter 13 statements for
`Problem04.ActiveStageProducts`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    exact-κ matrix-stage-history product bound with `ρ_n <= 2` discharged
    from active-stage max-entry bounds for the matrix-product Schur table. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_active_stage_bound
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j) ≤
          2 * blockMaxNorm hm hr Ablk) :
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hLower
      (higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_active_stage_bound
        hm hr Ablk pivotInv hApos hActive)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    source-strength conditional exact-κ matrix-stage-history product bound from
    a dimension-free triple-product max-entry estimate and the diagonal
    lower-update layer. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_product_bound_diag_update
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hLower
      (higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hm hr Ablk pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
        hInitInv hPivotInvBound hProduct hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    dimension-aware exact-κ matrix-stage-history product bound.

    This composes the per-stage multiplier-bound product wrapper with the
    proved matrix-product active-stage bridge carrying the explicit
    `(r : ℝ)^2` max-entry matrix-multiplication factor.  The source-strength
    dimension-free active-stage proof remains a separate obligation. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_with_dim_factor
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hActiveDom : SchurStageActiveColumnDom13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
      stageInvDiagBound)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      ((r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k)) *
          stageInvDiagBound k ⟨k, hk⟩ ≤
        1) :
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_active_stage_bound
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hLower
      (higham13_algorithm13_3_matrix_active_stage_bound_with_dim_factor
        hm hr Ablk pivotInv invDiagBound stageInvDiagBound hDom hDiagBound
        hActiveDom hPivotInvBound)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    dimension-aware exact-κ matrix-stage-history product bound from the
    diagonal lower-update layer.

    This replaces the raw active-column-dominance hypothesis in
    `higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_with_dim_factor`
    by the source Theorem 13.7-style diagonal update certificate, while still
    carrying the explicit `(r : ℝ)^2` matrix-product pivot budget. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_with_dim_factor_of_diag_update
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_with_dim_factor
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hLower
      invDiagBound stageInvDiagBound hDom hDiagBound
      (higham13_algorithm13_3_matrix_active_column_dominance_with_dim_factor
        hr Ablk pivotInv invDiagBound stageInvDiagBound hDom hInitInv
        hPivotInvBound hDiagUpdate)
      hPivotInvBound

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    exact-κ matrix-stage-history product bound from local Problem 13.4
    multiplier budgets at every active stage.

    This composes `higham13_algorithm13_3_stage_multiplier_bound_from_local_growth_budget`
    with
    `higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_active_stage_bound`.
    The theorem does not prove the local budget comparison; it isolates it in
    the `hBudget` hypothesis for each active pair. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_active_stage_bound
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (Uloc : Fin m → Fin m → Fin (r + r) → Fin (r + r) → ℝ)
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
    (hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hA_le_U : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) ≤
        maxEntryNorm (Nat.add_pos_left hr r) (Uloc i j))
    (hS_le_U : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      maxEntryNormRect hr hr
          (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
            (hInvPivot i j hji)) ≤
        maxEntryNorm (Nat.add_pos_left hr r) (Uloc i j))
    (hBudget : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      (growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (Uloc i j) (hLocalApos i j hji)) ^ 2 *
        (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
          maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (nonsingInv (r + r)
              (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
              (blockMatrixFlatFin Ablk) *
            maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv))
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j) ≤
          2 * blockMaxNorm hm hr Ablk) :
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let G : Fin (m * r) → Fin (m * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv
  let kappaA : ℝ :=
    maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
      maxEntryNormRect hN hN Ainv
  exact
    higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_active_stage_bound
      hm hr Ablk pivotInv Ainv hApos hRight n hNn
      (by
        intro i j hji
        letI : Invertible
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j) :=
          hInvPivot i j hji
        have hpivot :
            pivotInv j.val =
              ⅟(higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j) :=
          matrix_invOf_eq_of_isRightInverse
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
            (pivotInv j.val) (hPivotRight i j hji)
        letI : Invertible
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i i -
              higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
                ⅟(higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j) *
                higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j i) := by
          simpa [higham13_algorithm13_3_stageLocalSchurOfInv] using hInvSchur i j hji
        letI : Invertible
            (Matrix.fromBlocks
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j i)
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j)
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i i)) := by
          simpa [higham13_algorithm13_3_stageLocalBlockMatrix] using hInvFull i j hji
        have hStageLower :
            maxEntryNorm hr
                (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
                  pivotInv j.val) ≤
              (n : ℝ) *
                ((growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
                  (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                    (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
                  (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
                      (blockMatrixFlatFin Ablk) *
                    maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)) := by
          exact
            higham13_algorithm13_3_stage_multiplier_bound_from_local_growth_budget
              hr Ablk pivotInv i j hji (Uloc i j)
              hpivot
              (by
                simpa [higham13_algorithm13_3_stageLocalFlatMatrix,
                  higham13_algorithm13_3_stageLocalBlockMatrix] using
                  hLocalApos i j hji)
              n hrn
              (by
                simpa [higham13_algorithm13_3_stageLocalFlatMatrix,
                  higham13_algorithm13_3_stageLocalBlockMatrix] using
                  hA_le_U i j hji)
              (by
                simpa [higham13_algorithm13_3_stageLocalSchurOfInv] using
                  hS_le_U i j hji)
              (hBudget i j hji)
        calc
          maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
                pivotInv j.val)
              ≤ (n : ℝ) *
                  ((growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
                    (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                      (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
                    (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
                        (blockMatrixFlatFin Ablk) *
                      maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)) :=
                hStageLower
          _ = (n : ℝ) *
                  (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
                    (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                      (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
                (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
                    (blockMatrixFlatFin Ablk) *
                  maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) := by ring)
      hActive

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ matrix-stage-history product bound from local Problem 13.4
    multiplier budgets at every active stage.

    This is the Eq.13.22 companion to
    `higham13_eq13_23_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_active_stage_bound`;
    it has no `rho <= 2` side condition. -/
theorem
    higham13_eq13_22_matrix_stage_history_product_from_stage_local_budgets_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (Uloc : Fin m → Fin m → Fin (r + r) → Fin (r + r) → ℝ)
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
    (hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hA_le_U : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) ≤
        maxEntryNorm (Nat.add_pos_left hr r) (Uloc i j))
    (hS_le_U : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      maxEntryNormRect hr hr
          (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
            (hInvPivot i j hji)) ≤
        maxEntryNorm (Nat.add_pos_left hr r) (Uloc i j))
    (hBudget : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      (growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (Uloc i j) (hLocalApos i j hji)) ^ 2 *
        (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
          maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (nonsingInv (r + r)
              (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
              (blockMatrixFlatFin Ablk) *
            maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      (n : ℝ) *
        (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 3 *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  let hN : 0 < m * r := Nat.mul_pos hm hr
  exact
    higham13_eq13_22_matrix_stage_history_product_from_multiplier_bounds_exact_kappa
      hm hr Ablk pivotInv Ainv hApos hRight n hNn
      (by
        intro i j hji
        letI : Invertible
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j) :=
          hInvPivot i j hji
        have hpivot :
            pivotInv j.val =
              ⅟(higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j) :=
          matrix_invOf_eq_of_isRightInverse
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
            (pivotInv j.val) (hPivotRight i j hji)
        letI : Invertible
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i i -
              higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
                ⅟(higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j) *
                higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j i) := by
          simpa [higham13_algorithm13_3_stageLocalSchurOfInv] using hInvSchur i j hji
        letI : Invertible
            (Matrix.fromBlocks
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j i)
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j)
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i i)) := by
          simpa [higham13_algorithm13_3_stageLocalBlockMatrix] using hInvFull i j hji
        have hStageLower :
            maxEntryNorm hr
                (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
                  pivotInv j.val) ≤
              (n : ℝ) *
                ((growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
                  (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                    (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
                  (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
                      (blockMatrixFlatFin Ablk) *
                    maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)) := by
          exact
            higham13_algorithm13_3_stage_multiplier_bound_from_local_growth_budget
              hr Ablk pivotInv i j hji (Uloc i j)
              hpivot
              (by
                simpa [higham13_algorithm13_3_stageLocalFlatMatrix,
                  higham13_algorithm13_3_stageLocalBlockMatrix] using
                  hLocalApos i j hji)
              n hrn
              (by
                simpa [higham13_algorithm13_3_stageLocalFlatMatrix,
                  higham13_algorithm13_3_stageLocalBlockMatrix] using
                  hA_le_U i j hji)
              (by
                simpa [higham13_algorithm13_3_stageLocalSchurOfInv] using
                  hS_le_U i j hji)
              (hBudget i j hji)
        calc
          maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
                pivotInv j.val)
              ≤ (n : ℝ) *
                  ((growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
                    (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                      (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
                    (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
                        (blockMatrixFlatFin Ablk) *
                      maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)) :=
                hStageLower
          _ = (n : ℝ) *
                  (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
                    (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                      (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
                (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
                    (blockMatrixFlatFin Ablk) *
                  maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) := by ring)

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ matrix-stage-history `BlockLUFactSpec` witness from local
    Problem 13.4 multiplier budgets and exact pivot right-inverse data.

    This packages
    `higham13_eq13_22_matrix_stage_history_product_from_stage_local_budgets_exact_kappa`
    with the concrete Algorithm 13.3 matrix-stage reconstruction theorem.  The
    local budget table remains the visible source obligation. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_pivot_right_inverse
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
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (Uloc : Fin m → Fin m → Fin (r + r) → Fin (r + r) → ℝ)
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
    (hA_le_U : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) ≤
        maxEntryNorm (Nat.add_pos_left hr r) (Uloc i j))
    (hS_le_U : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      maxEntryNormRect hr hr
          (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
            (hInvPivot i j hji)) ≤
        maxEntryNorm (Nat.add_pos_left hr r) (Uloc i j))
    (hBudget : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      (growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (Uloc i j) (hLocalApos i j hji)) ^ 2 *
        (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
          maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (nonsingInv (r + r)
              (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
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
      higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_right_inverse
        Ablk pivotInv hPivotRightAll
  · simpa [L, U] using
      higham13_eq13_22_matrix_stage_history_product_from_stage_local_budgets_exact_kappa
        hm hr Ablk pivotInv Ainv hApos hRight n hNn hrn Uloc
        hInvPivot hInvSchur hInvFull
        (fun i j _hji => hPivotRightAll j.val j.isLt)
        hLocalApos hA_le_U hS_le_U hBudget

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    exact-κ point-row matrix-stage-history `BlockLUFactSpec` witness from
    local Problem 13.4 multiplier budgets, active-stage `rho <= 2` data, and
    exact pivot right-inverse certificates. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_active_stage_bound_of_pivot_right_inverse
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
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (Uloc : Fin m → Fin m → Fin (r + r) → Fin (r + r) → ℝ)
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
    (hA_le_U : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) ≤
        maxEntryNorm (Nat.add_pos_left hr r) (Uloc i j))
    (hS_le_U : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      maxEntryNormRect hr hr
          (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
            (hInvPivot i j hji)) ≤
        maxEntryNorm (Nat.add_pos_left hr r) (Uloc i j))
    (hBudget : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      (growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (Uloc i j) (hLocalApos i j hji)) ^ 2 *
        (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
          maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (nonsingInv (r + r)
              (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
              (blockMatrixFlatFin Ablk) *
            maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv))
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j) ≤
          2 * blockMaxNorm hm hr Ablk) :
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
      higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_right_inverse
        Ablk pivotInv hPivotRightAll
  · simpa [L, U] using
      higham13_eq13_23_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_active_stage_bound
        hm hr Ablk pivotInv Ainv hApos hRight n hNn hrn Uloc
        hInvPivot hInvSchur hInvFull
        (fun i j _hji => hPivotRightAll j.val j.isLt)
        hLocalApos hA_le_U hS_le_U hBudget hActive

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    same local-budget witness package as
    `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_pivot_right_inverse`,
    but the local `growthFactorEntry` positivity denominator is derived from
    the local full-stage invertibility hypothesis. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_pivot_right_inverse_of_local_invertible
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
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (Uloc : Fin m → Fin m → Fin (r + r) → Fin (r + r) → ℝ)
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hA_le_U : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) ≤
        maxEntryNorm (Nat.add_pos_left hr r) (Uloc i j))
    (hS_le_U : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      maxEntryNormRect hr hr
          (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
            (hInvPivot i j hji)) ≤
        maxEntryNorm (Nat.add_pos_left hr r) (Uloc i j))
    (hBudget : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      (growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (Uloc i j)
          ((higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
            hr Ablk pivotInv hInvFull) i j hji)) ^ 2 *
        (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
          maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (nonsingInv (r + r)
              (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
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
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn hrn Uloc
      hInvPivot hInvSchur hInvFull
      (higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull)
      hA_le_U hS_le_U hBudget

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row local-budget witness package deriving the local
    `growthFactorEntry` positivity denominator from local full-stage
    invertibility. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_active_stage_bound_of_pivot_right_inverse_of_local_invertible
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
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (Uloc : Fin m → Fin m → Fin (r + r) → Fin (r + r) → ℝ)
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hA_le_U : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) ≤
        maxEntryNorm (Nat.add_pos_left hr r) (Uloc i j))
    (hS_le_U : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      maxEntryNormRect hr hr
          (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
            (hInvPivot i j hji)) ≤
        maxEntryNorm (Nat.add_pos_left hr r) (Uloc i j))
    (hBudget : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      (growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (Uloc i j)
          ((higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
            hr Ablk pivotInv hInvFull) i j hji)) ^ 2 *
        (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
          maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (nonsingInv (r + r)
              (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
              (blockMatrixFlatFin Ablk) *
            maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv))
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j) ≤
          2 * blockMaxNorm hm hr Ablk) :
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_active_stage_bound_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn hrn Uloc
      hInvPivot hInvSchur hInvFull
      (higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull)
      hA_le_U hS_le_U hBudget hActive

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ matrix-stage-history product bound from canonical stage-local
    growth budgets.

    Compared with
    `higham13_eq13_22_matrix_stage_history_product_from_stage_local_budgets_exact_kappa`,
    this wrapper chooses the local growth matrix to be the canonical local
    Problem 13.4 envelope and discharges the local initial/Schur containment
    hypotheses.  The remaining budget comparison is the real source
    obligation: local `ρ²κ` must be bounded by the ambient matrix-stage
    `ρ²κ`. -/
theorem
    higham13_eq13_22_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
    (hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hBudget : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      (growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji)) ^ 2 *
        (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
          maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (nonsingInv (r + r)
              (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
              (blockMatrixFlatFin Ablk) *
            maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
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
    higham13_eq13_22_matrix_stage_history_product_from_stage_local_budgets_exact_kappa
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hrn
      (fun i j => higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
      hInvPivot hInvSchur hInvFull hPivotRight hLocalApos
      (by
        intro i j _hji
        exact higham13_algorithm13_3_stageLocalGrowthMatrix_contains_initial
          hr Ablk pivotInv i j)
      (by
        intro i j hji
        letI : Invertible
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j) :=
          hInvPivot i j hji
        have hpivot :
            pivotInv j.val =
              ⅟(higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j) :=
          matrix_invOf_eq_of_isRightInverse
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
            (pivotInv j.val) (hPivotRight i j hji)
        exact higham13_algorithm13_3_stageLocalGrowthMatrix_contains_schurOfInv
          hr Ablk pivotInv i j hpivot)
      hBudget

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    exact-κ matrix-stage-history product bound from canonical stage-local
    growth budgets plus active-stage `ρ <= 2` data.

    This is the Eq.13.23 companion to
    `higham13_eq13_22_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa`. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_active_stage_bound
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
    (hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hBudget : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      (growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji)) ^ 2 *
        (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
          maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (nonsingInv (r + r)
              (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
              (blockMatrixFlatFin Ablk) *
            maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv))
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j) ≤
          2 * blockMaxNorm hm hr Ablk) :
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_active_stage_bound
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hrn
      (fun i j => higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
      hInvPivot hInvSchur hInvFull hPivotRight hLocalApos
      (by
        intro i j _hji
        exact higham13_algorithm13_3_stageLocalGrowthMatrix_contains_initial
          hr Ablk pivotInv i j)
      (by
        intro i j hji
        letI : Invertible
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j) :=
          hInvPivot i j hji
        have hpivot :
            pivotInv j.val =
              ⅟(higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j) :=
          matrix_invOf_eq_of_isRightInverse
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
            (pivotInv j.val) (hPivotRight i j hji)
        exact higham13_algorithm13_3_stageLocalGrowthMatrix_contains_schurOfInv
          hr Ablk pivotInv i j hpivot)
      hBudget hActive

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ matrix-stage-history product bound from canonical stage-local
    growth and an explicit inverse-ratio comparison.

    This refines
    `higham13_eq13_22_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa`:
    the per-stage `rho^2 kappa` budget is no longer a black-box premise.  It is derived
    from the proved max-entry domination of the canonical local growth matrix
    by the matrix-stage history and the displayed inverse-ratio hypothesis,
    which is the remaining condition-number comparison. -/
theorem
    higham13_eq13_22_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
    (hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hInverseRatio : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) ≤
      maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
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
    higham13_eq13_22_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hrn
      hInvPivot hInvSchur hInvFull hPivotRight hLocalApos
      (by
        intro i j hji
        exact
          growthFactorEntry_sq_kappa_budget_le_of_growth_le_inv_ratio
            (Nat.add_pos_left hr r) (Nat.mul_pos hm hr)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
            (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
            (nonsingInv (r + r)
              (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
            (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos hm hr) hm hr Ablk pivotInv)
            Ainv
            (hLocalApos i j hji) hApos
            (higham13_algorithm13_3_stageLocalGrowthMatrix_le_matrixStageHistoryGrowthMatrix
              hm hr Ablk pivotInv i j hji)
            (hInverseRatio i j hji))

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    exact-κ matrix-stage-history product bound from canonical stage-local
    growth, active-stage `rho <= 2` data, and an explicit inverse-ratio
    comparison.

    This is the Eq.13.23 companion to
    `higham13_eq13_22_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa`.
    The active-stage max-entry theorem and the inverse-ratio comparison remain
    visible source obligations. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_active_stage_bound
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
    (hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hInverseRatio : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) ≤
      maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j) ≤
          2 * blockMaxNorm hm hr Ablk) :
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_active_stage_bound
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hrn
      hInvPivot hInvSchur hInvFull hPivotRight hLocalApos
      (by
        intro i j hji
        exact
          growthFactorEntry_sq_kappa_budget_le_of_growth_le_inv_ratio
            (Nat.add_pos_left hr r) (Nat.mul_pos hm hr)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
            (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
            (nonsingInv (r + r)
              (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
            (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos hm hr) hm hr Ablk pivotInv)
            Ainv
            (hLocalApos i j hji) hApos
            (higham13_algorithm13_3_stageLocalGrowthMatrix_le_matrixStageHistoryGrowthMatrix
              hm hr Ablk pivotInv i j hji)
            (hInverseRatio i j hji))
      hActive

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    exact-κ matrix-stage-history product bound from the stage-local
    inverse-ratio route and the source-strength conditional active-stage
    product-bound/diagonal-update layer.

    The inverse-ratio comparison and the dimension-free triple-product
    max-entry estimate remain explicit source obligations. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_product_bound_diag_update
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
    (hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hInverseRatio : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) ≤
      maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_active_stage_bound
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hrn
      hInvPivot hInvSchur hInvFull hPivotRight hLocalApos hInverseRatio
      (higham13_algorithm13_3_matrix_active_stage_bound_of_product_bound_diag_update
        hm hr Ablk pivotInv invDiagBound stageInvDiagBound hDom hDiagBound
        hInitInv hPivotInvBound hProduct hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table companion to
    `higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_product_bound_diag_update`.

    The source-style reciprocal active-pivot table supplies the scalar pivot
    product premise through `higham13_theorem13_7_pivot_inverse_bound_of_reciprocal`. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_product_bound_diag_update_reciprocal
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
    (hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hInverseRatio : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) ≤
      maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_product_bound_diag_update
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hrn
      hInvPivot hInvSchur hInvFull hPivotRight hLocalApos hInverseRatio
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    dimension-aware exact-κ matrix-stage-history product bound from the
    stage-local inverse-ratio route and the diagonal lower-update layer.

    This composes the explicit inverse-ratio comparison with the proved
    `(r : ℝ)^2` matrix-product active-stage route; it is not the source's
    dimension-free structured product proof. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_with_dim_factor_of_diag_update
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (m * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
    (hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hInverseRatio : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) ≤
      maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_active_stage_bound
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hrn
      hInvPivot hInvSchur hInvFull hPivotRight hLocalApos hInverseRatio
      (higham13_algorithm13_3_matrix_active_stage_bound_with_dim_factor_of_diag_update
        hm hr Ablk pivotInv invDiagBound stageInvDiagBound hDom hDiagBound
        hInitInv hPivotInvBound hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-kappa matrix-stage-history `BlockLUFactSpec` witness from canonical
    stage-local growth, exact pivot right-inverse reconstruction data, and
    direct local-to-global `rho^2 kappa` budget comparisons. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_pivot_right_inverse
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
    (hrn : (r : ℝ) ≤ (n : ℝ))
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
    (hBudget : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      (growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji)) ^ 2 *
        (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
          maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (nonsingInv (r + r)
              (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
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
      higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_right_inverse
        Ablk pivotInv hPivotRightAll
  · simpa [L, U] using
      higham13_eq13_22_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa
        hm hr Ablk pivotInv Ainv hApos hRight n hNn hrn
        hInvPivot hInvSchur hInvFull
        (fun i j _hji => hPivotRightAll j.val j.isLt)
        hLocalApos hBudget

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    exact-kappa point-row matrix-stage-history `BlockLUFactSpec` witness from
    canonical stage-local growth, exact pivot right-inverse reconstruction
    data, direct budget comparisons, and active-stage bounds. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_active_stage_bound_of_pivot_right_inverse
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
    (hrn : (r : ℝ) ≤ (n : ℝ))
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
    (hBudget : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      (growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji)) ^ 2 *
        (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
          maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (nonsingInv (r + r)
              (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
              (blockMatrixFlatFin Ablk) *
            maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv))
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j) ≤
          2 * blockMaxNorm hm hr Ablk) :
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
      higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_right_inverse
        Ablk pivotInv hPivotRightAll
  · simpa [L, U] using
      higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_active_stage_bound
        hm hr Ablk pivotInv Ainv hApos hRight n hNn hrn
        hInvPivot hInvSchur hInvFull
        (fun i j _hji => hPivotRightAll j.val j.isLt)
        hLocalApos hBudget hActive

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    same direct-budget canonical-growth witness package as
    `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_pivot_right_inverse`,
    but the local `growthFactorEntry` positivity denominator is derived from
    the local full-stage invertibility hypothesis. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_pivot_right_inverse_of_local_invertible
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
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hBudget : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      (growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
            hr Ablk pivotInv hInvFull i j hji)) ^ 2 *
        (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
          maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (nonsingInv (r + r)
              (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
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
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn hrn
      hInvPivot hInvSchur hInvFull
      (higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull)
      hBudget

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row direct-budget canonical-growth witness package deriving the local
    `growthFactorEntry` positivity denominator from local full-stage
    invertibility. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_active_stage_bound_of_pivot_right_inverse_of_local_invertible
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
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hBudget : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      (growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
            hr Ablk pivotInv hInvFull i j hji)) ^ 2 *
        (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
          maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (nonsingInv (r + r)
              (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
              (blockMatrixFlatFin Ablk) *
            maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv))
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j) ≤
          2 * blockMaxNorm hm hr Ablk) :
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_active_stage_bound_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn hrn
      hInvPivot hInvSchur hInvFull
      (higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull)
      hBudget hActive

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero canonical-growth witness package for the stage-local
    direct-budget route.

    This specializes the exact-κ stage-local surface to the repository's
    canonical inverse `nonsingInv` and derives the global positive denominator
    and right-inverse certificate from `det(blockMatrixFlatFin A) != 0`.  The
    per-stage local-to-global budget comparisons remain explicit. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
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
    (hrn : (r : ℝ) ≤ (n : ℝ))
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
    (∀ i j : Fin m, ∀ hji : j.val < i.val,
      (growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
            hr Ablk pivotInv hInvFull i j hji)) ^ 2 *
        (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
          maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (nonsingInv (r + r)
              (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        (growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos) ^ 2 *
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
  intro hBudget
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  have hRight :
      IsRightInverse (m * r) (blockMatrixFlatFin Ablk)
        (nonsingInv (m * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      (m * r) (blockMatrixFlatFin Ablk) hdet).2
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_pivot_right_inverse_of_local_invertible
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hPivotRightAll hApos hRight n hNn hrn
      hInvPivot hInvSchur hInvFull hBudget

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero point-row witness package for the canonical-growth
    stage-local direct-budget route.

    This is the Eq.13.23 companion to
    `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_pivot_right_inverse_of_det_ne_zero`;
    the active-stage `rho <= 2` surface remains an explicit source obligation. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_active_stage_bound_of_pivot_right_inverse_of_det_ne_zero
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
    (hrn : (r : ℝ) ≤ (n : ℝ))
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
    (∀ i j : Fin m, ∀ hji : j.val < i.val,
      (growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
            hr Ablk pivotInv hInvFull i j hji)) ^ 2 *
        (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
          maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (nonsingInv (r + r)
              (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        (growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
            maxEntryNormRect hN hN
              (nonsingInv (m * r) (blockMatrixFlatFin Ablk)))) →
    (∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j) ≤
          2 * blockMaxNorm hm hr Ablk) →
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hBudget hActive
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  have hRight :
      IsRightInverse (m * r) (blockMatrixFlatFin Ablk)
        (nonsingInv (m * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      (m * r) (blockMatrixFlatFin Ablk) hdet).2
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_active_stage_bound_of_pivot_right_inverse_of_local_invertible
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hPivotRightAll hApos hRight n hNn hrn
      hInvPivot hInvSchur hInvFull hBudget hActive

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ matrix-stage-history `BlockLUFactSpec` witness from canonical
    stage-local growth, exact pivot right-inverse reconstruction data, and an
    explicit inverse-ratio comparison. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_pivot_right_inverse
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
    (hrn : (r : ℝ) ≤ (n : ℝ))
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
    (hInverseRatio : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) ≤
      maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) :
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
      higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_right_inverse
        Ablk pivotInv hPivotRightAll
  · simpa [L, U] using
      higham13_eq13_22_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa
        hm hr Ablk pivotInv Ainv hApos hRight n hNn hrn
        hInvPivot hInvSchur hInvFull
        (fun i j _hji => hPivotRightAll j.val j.isLt)
        hLocalApos hInverseRatio

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    exact-κ point-row matrix-stage-history `BlockLUFactSpec` witness from
    canonical stage-local growth, exact pivot right-inverse reconstruction
    data, active-stage bounds, and an explicit inverse-ratio comparison. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_active_stage_bound_of_pivot_right_inverse
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
    (hrn : (r : ℝ) ≤ (n : ℝ))
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
    (hInverseRatio : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) ≤
      maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j) ≤
          2 * blockMaxNorm hm hr Ablk) :
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
      higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_right_inverse
        Ablk pivotInv hPivotRightAll
  · simpa [L, U] using
      higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_active_stage_bound
        hm hr Ablk pivotInv Ainv hApos hRight n hNn hrn
        hInvPivot hInvSchur hInvFull
        (fun i j _hji => hPivotRightAll j.val j.isLt)
        hLocalApos hInverseRatio hActive

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    `BlockLUFactSpec` witness from the stage-local inverse-ratio route and the
    source-strength conditional active-stage product-bound/diagonal-update
    layer. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
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
    (hrn : (r : ℝ) ≤ (n : ℝ))
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
    (hInverseRatio : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) ≤
      maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_active_stage_bound_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn hrn
      hInvPivot hInvSchur hInvFull hLocalApos hInverseRatio
      (higham13_algorithm13_3_matrix_active_stage_bound_of_product_bound_diag_update
        hm hr Ablk pivotInv invDiagBound stageInvDiagBound hDom hDiagBound
        hInitInv hPivotInvBound hProduct hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table `BlockLUFactSpec` witness companion to
    `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_product_bound_diag_update_reciprocal_of_pivot_right_inverse
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
    (hrn : (r : ℝ) ≤ (n : ℝ))
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
    (hInverseRatio : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) ≤
      maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn hrn
      hInvPivot hInvSchur hInvFull hLocalApos hInverseRatio
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    dimension-aware `BlockLUFactSpec` witness from the stage-local
    inverse-ratio route and the diagonal lower-update layer. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_with_dim_factor_of_diag_update_of_pivot_right_inverse
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
    (hrn : (r : ℝ) ≤ (n : ℝ))
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
    (hInverseRatio : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) ≤
      maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_active_stage_bound_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn hrn
      hInvPivot hInvSchur hInvFull hLocalApos hInverseRatio
      (higham13_algorithm13_3_matrix_active_stage_bound_with_dim_factor_of_diag_update
        hm hr Ablk pivotInv invDiagBound stageInvDiagBound hDom hDiagBound
        hInitInv hPivotInvBound hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    same witness package as
    `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_pivot_right_inverse`,
    but the local `growthFactorEntry` positivity denominator is derived from
    the local full-stage invertibility hypothesis. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_pivot_right_inverse_of_local_invertible
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
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hInverseRatio : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) ≤
      maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) :
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
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn hrn
      hInvPivot hInvSchur hInvFull
      (higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull)
      hInverseRatio

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row witness package with exact pivot right-inverse data and an
    explicit inverse-ratio comparison, deriving the local `growthFactorEntry`
    positivity denominator from local full-stage invertibility. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_active_stage_bound_of_pivot_right_inverse_of_local_invertible
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
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (hInvPivot : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hInvSchur : ∀ i j : Fin m, ∀ hji : j.val < i.val,
      Invertible
        (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          (hInvPivot i j hji)))
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hInverseRatio : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) ≤
      maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j) ≤
          2 * blockMaxNorm hm hr Ablk) :
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_active_stage_bound_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn hrn
      hInvPivot hInvSchur hInvFull
      (higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull)
      hInverseRatio hActive

end NumStability
