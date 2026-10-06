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
import NumStability.Source.Higham.Chapter13.Problem04.FactorizationProducts.LocalComparisons
import NumStability.Source.Higham.Chapter13.Problem04.InfNormGrowth
import NumStability.Source.Higham.Chapter13.Problem04.LocalGrowth
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStages
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis
import NumStability.Source.Higham.Chapter13.Theorem02.Factorization

/-!
# Source.Higham.Chapter13.Problem04.FactorizationProducts.ComparisonUpdates

This module formalizes the source-facing Chapter 13 statements for
`Problem04.FactorizationProducts.ComparisonUpdates`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero exact-kappa `BlockLUFactSpec` witness from the
    canonical stage-local-growth source comparison route.

    This is the canonical-inverse variant of
    `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse`:
    it uses `nonsingInv (m*r) (blockMatrixFlatFin Ablk)` and derives the full
    positive denominator and right-inverse certificate from
    `det(blockMatrixFlatFin Ablk) != 0`. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
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
    let hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
      higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull
    let hN : 0 < m * r := Nat.mul_pos hm hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin m, ∀ hji : j.val < i.val,
      growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos) →
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
  intro hRhoLocal_le hKappaLocal_le
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
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hLocalApos hRhoLocal_le hKappaLocal_le

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero point-row exact-kappa `BlockLUFactSpec` witness from
    the canonical stage-local-growth source comparison route and the source
    `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
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
    let hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
      higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull
    let hN : 0 < m * r := Nat.mul_pos hm hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin m, ∀ hji : j.val < i.val,
      growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos) →
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
  intro hRhoLocal_le hKappaLocal_le hRho_le_two
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hLocalApos hRhoLocal_le hKappaLocal_le
      hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero exact-κ `BlockLUFactSpec` witness from the canonical
    stage-local-growth source comparison route and canonical active pivots
    `pivotInv k = nonsingInv pivot_k`.

    This combines the source-facing full inverse
    `nonsingInv (m*r) (blockMatrixFlatFin Ablk)` with the canonical active
    pivot inverse table. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv_of_det_ne_zero
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
    let hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
      higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull
    let hN : 0 < m * r := Nat.mul_pos hm hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin m, ∀ hji : j.val < i.val,
      growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos) →
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
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
      hm hr Ablk pivotInv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hdet n hNn hInvPivot hInvSchur hInvFull

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero point-row exact-κ `BlockLUFactSpec` witness from the
    canonical stage-local-growth source comparison route, canonical active
    pivots, and the source `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv_of_det_ne_zero
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
    let hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
      higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull
    let hN : 0 < m * r := Nat.mul_pos hm hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin m, ∀ hji : j.val < i.val,
      growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos) →
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
      hm hr Ablk pivotInv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hdet n hNn hInvPivot hInvSchur hInvFull

/-- Higham, 2nd ed., Chapter 13, equations (13.22) and Problem 13.4:
    BDD first-Schur-tail determinant-nonzero stage-local-growth
    source-comparison witness.

    The BDD prefix data and shifted recursive tail right-inverse table build
    the all-active pivot right-inverse certificate internally.  The ambient
    exact-kappa object is the canonical full `nonsingInv`, derived from
    `det(blockMatrixFlatFin Ablk) != 0`. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero
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
    let hLocalApos : ∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
      higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) →
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
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
  intro hRhoLocal_le hKappaLocal_le
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTail
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
      (Nat.succ_pos m) hr Ablk pivotInv hPivotRight hdet n hNn
      hInvPivot hInvSchur hInvFull hRhoLocal_le hKappaLocal_le

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    BDD first-Schur-tail determinant-nonzero stage-local-growth
    source-comparison witness with a raw `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero
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
    let hLocalApos : ∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
      higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) →
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
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
  intro hRhoLocal_le hKappaLocal_le hRho_le_two
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTail
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
      (Nat.succ_pos m) hr Ablk pivotInv hPivotRight hdet n hNn
      hInvPivot hInvSchur hInvFull hRhoLocal_le hKappaLocal_le hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equations (13.22) and Problem 13.4:
    canonical-tail version of the BDD first-Schur-tail determinant-nonzero
    stage-local-growth source-comparison witness. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero
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
    let hLocalApos : ∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
      higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) →
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
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
  intro hRhoLocal_le hKappaLocal_le
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTailDet
      hTailPivotInv
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
      (Nat.succ_pos m) hr Ablk pivotInv hPivotRight hdet n hNn
      hInvPivot hInvSchur hInvFull hRhoLocal_le hKappaLocal_le

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    canonical-tail version of the BDD first-Schur-tail determinant-nonzero
    stage-local-growth source-comparison witness with raw `rho <= 2`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero
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
    let hLocalApos : ∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
      higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) →
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
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
  intro hRhoLocal_le hKappaLocal_le hRho_le_two
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTailDet
      hTailPivotInv
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
      (Nat.succ_pos m) hr Ablk pivotInv hPivotRight hdet n hNn
      hInvPivot hInvSchur hInvFull hRhoLocal_le hKappaLocal_le hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ `BlockLUFactSpec` witness from the canonical
    stage-local-growth source comparison route and the matrix-stage BDD
    `rho <= 2` proof layer.

    This is the concrete witness counterpart of
    `higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_product_bound_diag_update`.
    It removes the raw `rho <= 2` premise from the witness surface while
    keeping the local-to-full scalar comparison table and active
    product/update data explicit. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hLocalApos hRhoLocal_le hKappaLocal_le
      (higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hm hr Ablk pivotInv hApos invDiagBound stageInvDiagBound
        hDom hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    concrete reciprocal-table companion to the source-comparison
    product/update `BlockLUFactSpec` witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_product_bound_diag_update_reciprocal_of_pivot_right_inverse
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hLocalApos hRhoLocal_le hKappaLocal_le
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ `BlockLUFactSpec` witness from the canonical
    stage-local-growth source comparison route, the matrix-stage BDD
    `rho <= 2` proof layer, and canonical active pivots
    `pivotInv k = nonsingInv pivot_k`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_product_bound_diag_update_of_pivotInv_eq_nonsingInv
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hLocalApos hRhoLocal_le hKappaLocal_le
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv hPivotInvBound
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ `BlockLUFactSpec` witness from the base-comparison
    stage-local-growth route and the matrix-stage BDD `rho <= 2` proof layer.

    This is the concrete witness counterpart of
    `higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_product_bound_diag_update`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hLocalApos hBaseLocal hKappaLocal_le
      (higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hm hr Ablk pivotInv hApos invDiagBound stageInvDiagBound
        hDom hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    concrete reciprocal-table companion to the base-comparison
    product/update `BlockLUFactSpec` witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_product_bound_diag_update_reciprocal_of_pivot_right_inverse
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv hPivotRightAll hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hLocalApos hBaseLocal hKappaLocal_le
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ `BlockLUFactSpec` witness from the base-comparison
    stage-local-growth route, canonical active pivots, and the matrix-stage
    BDD `rho <= 2` proof layer. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_product_bound_diag_update_of_pivotInv_eq_nonsingInv
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
      hm hr Ablk pivotInv Ainv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hApos hRight n hNn hInvPivot hInvSchur hInvFull hLocalApos
      hBaseLocal hKappaLocal_le invDiagBound stageInvDiagBound hDom hDiagBound
      hInitInv hPivotInvBound hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ `BlockLUFactSpec` witness from the base-comparison
    stage-local-growth route, canonical active pivots, and reciprocal-table
    product/update data. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_product_bound_diag_update_reciprocal_of_pivotInv_eq_nonsingInv
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_product_bound_diag_update_of_pivotInv_eq_nonsingInv
      hm hr Ablk pivotInv Ainv hPivotDet hPivotInv hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hLocalApos hBaseLocal hKappaLocal_le
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero point-row exact-κ `BlockLUFactSpec` witness from the
    stage-local-growth base-comparison route, canonical active pivots, and the
    matrix-stage BDD product-bound/diagonal-update proof layer.

    This is the full-`nonsingInv` variant of the base-comparison
    product-bound surface.  It removes the explicit ambient inverse/right-inverse
    object while keeping the base comparison, condition comparison, and BDD
    product/update data as visible source obligations. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv_of_det_ne_zero_of_product_bound_diag_update
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
  intro hBaseLocal hKappaLocal_le invDiagBound stageInvDiagBound
    hDom hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_product_bound_diag_update_of_pivotInv_eq_nonsingInv
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hPivotDet hPivotInv hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hLocalApos hBaseLocal hKappaLocal_le
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv hPivotInvBound
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero point-row exact-κ `BlockLUFactSpec` witness from the
    stage-local-growth base-comparison route, canonical active pivots,
    reciprocal-table product/update data, and the canonical full `nonsingInv`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv_of_det_ne_zero_of_product_bound_diag_update_reciprocal
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
  intro hBaseLocal hKappaLocal_le invDiagBound stageInvDiagBound
    hDom hDiagBound hInitInv hReciprocal hProduct hDiagUpdate
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv_of_det_ne_zero_of_product_bound_diag_update
      hm hr Ablk pivotInv hPivotDet hPivotInv hdet n hNn
      hInvPivot hInvSchur hInvFull hBaseLocal hKappaLocal_le invDiagBound
      stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equations (13.22) and Problem 13.4:
    BDD first-Schur-tail determinant-nonzero stage-local-growth
    base-comparison witness.

    The BDD prefix data and shifted recursive tail right-inverse table build
    the all-active pivot right-inverse certificate internally.  The ambient
    exact-kappa object is the canonical full `nonsingInv`, derived from
    `det(blockMatrixFlatFin Ablk) != 0`; the explicit base and condition
    comparisons remain visible source obligations. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero
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
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      maxEntryNorm hN (blockMatrixFlatFin Ablk) ≤
        maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) →
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
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
  intro hBaseLocal hKappaLocal_le
  let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  let hLocalApos : ∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
    higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
      hr Ablk pivotInv hInvFull
  have hRight :
      IsRightInverse ((m + 1) * r) (blockMatrixFlatFin Ablk)
        (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      ((m + 1) * r) (blockMatrixFlatFin Ablk) hdet).2
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTail
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv
      (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))
      hPivotRight hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hLocalApos hBaseLocal hKappaLocal_le

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    BDD first-Schur-tail determinant-nonzero stage-local-growth
    base-comparison witness with a raw `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero
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
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      maxEntryNorm hN (blockMatrixFlatFin Ablk) ≤
        maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) →
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
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
  intro hBaseLocal hKappaLocal_le hRho_le_two
  let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  let hLocalApos : ∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
    higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
      hr Ablk pivotInv hInvFull
  have hRight :
      IsRightInverse ((m + 1) * r) (blockMatrixFlatFin Ablk)
        (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      ((m + 1) * r) (blockMatrixFlatFin Ablk) hdet).2
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTail
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv
      (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))
      hPivotRight hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hLocalApos hBaseLocal hKappaLocal_le
      hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equations (13.22) and Problem 13.4:
    canonical-tail version of the BDD first-Schur-tail determinant-nonzero
    stage-local-growth base-comparison witness. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero
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
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      maxEntryNorm hN (blockMatrixFlatFin Ablk) ≤
        maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) →
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
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
  intro hBaseLocal hKappaLocal_le
  let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  let hLocalApos : ∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
    higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
      hr Ablk pivotInv hInvFull
  have hRight :
      IsRightInverse ((m + 1) * r) (blockMatrixFlatFin Ablk)
        (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      ((m + 1) * r) (blockMatrixFlatFin Ablk) hdet).2
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTailDet
      hTailPivotInv
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv
      (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))
      hPivotRight hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hLocalApos hBaseLocal hKappaLocal_le

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    canonical-tail version of the BDD first-Schur-tail determinant-nonzero
    stage-local-growth base-comparison witness with raw `rho <= 2`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero
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
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      maxEntryNorm hN (blockMatrixFlatFin Ablk) ≤
        maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) →
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
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
  intro hBaseLocal hKappaLocal_le hRho_le_two
  let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  let hLocalApos : ∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
    higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
      hr Ablk pivotInv hInvFull
  have hRight :
      IsRightInverse ((m + 1) * r) (blockMatrixFlatFin Ablk)
        (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      ((m + 1) * r) (blockMatrixFlatFin Ablk) hdet).2
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTailDet
      hTailPivotInv
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv
      (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))
      hPivotRight hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hLocalApos hBaseLocal hKappaLocal_le
      hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    BDD first-Schur-tail determinant-nonzero stage-local-growth
    base-comparison witness with product/update data.

    This removes the explicit all-active pivot right-inverse table, the full
    inverse/right-inverse object, and the raw `rho <= 2` premise from callers;
    the base comparison, condition comparison, and active product/update data
    remain the visible source obligations. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update
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
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      maxEntryNorm hN (blockMatrixFlatFin Ablk) ≤
        maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) →
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
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
  intro hBaseLocal hKappaLocal_le invDiagBound stageInvDiagBound
    hDom hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate
  let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  let hLocalApos : ∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
    higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
      hr Ablk pivotInv hInvFull
  have hRight :
      IsRightInverse ((m + 1) * r) (blockMatrixFlatFin Ablk)
        (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      ((m + 1) * r) (blockMatrixFlatFin Ablk) hdet).2
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTail
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv
      (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))
      hPivotRight hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hLocalApos hBaseLocal hKappaLocal_le
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv hPivotInvBound
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    canonical-tail version of the BDD first-Schur-tail stage-local-growth
    base-comparison product/update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update
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
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      maxEntryNorm hN (blockMatrixFlatFin Ablk) ≤
        maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) →
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
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
  intro hBaseLocal hKappaLocal_le invDiagBound stageInvDiagBound
    hDom hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate
  let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  let hLocalApos : ∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
    higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
      hr Ablk pivotInv hInvFull
  have hRight :
      IsRightInverse ((m + 1) * r) (blockMatrixFlatFin Ablk)
        (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      ((m + 1) * r) (blockMatrixFlatFin Ablk) hdet).2
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTailDet
      hTailPivotInv
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv
      (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))
      hPivotRight hApos hRight n hNn
      hInvPivot hInvSchur hInvFull hLocalApos hBaseLocal hKappaLocal_le
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv hPivotInvBound
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero point-row exact-κ `BlockLUFactSpec` witness from the
    canonical stage-local-growth source comparison route and the matrix-stage
    BDD `rho <= 2` proof layer.

    This combines the determinant-nonzero canonical-inverse cleanup with the
    product-bound/diagonal-update `rho <= 2` bridge at the concrete factor
    witness surface.  The scalar comparison table and active product/update
    data remain the visible source obligations. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse_of_det_ne_zero_of_product_bound_diag_update
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
    let hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
      higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull
    let hN : 0 < m * r := Nat.mul_pos hm hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin m, ∀ hji : j.val < i.val,
      growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos) →
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
  intro hRhoLocal_le hKappaLocal_le invDiagBound stageInvDiagBound
    hDom hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  let hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
    higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
      hr Ablk pivotInv hInvFull
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
      hm hr Ablk pivotInv hPivotRightAll hdet n hNn
      hInvPivot hInvSchur hInvFull hRhoLocal_le hKappaLocal_le
      (higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hm hr Ablk pivotInv hApos invDiagBound stageInvDiagBound
        hDom hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero point-row exact-κ `BlockLUFactSpec` witness from the
    canonical stage-local-growth source comparison route, canonical active
    pivots, the source-facing full inverse, and the matrix-stage BDD
    `rho <= 2` proof layer. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv_of_det_ne_zero_of_product_bound_diag_update
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
    let hLocalApos : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
      higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull
    let hN : 0 < m * r := Nat.mul_pos hm hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin m, ∀ hji : j.val < i.val,
      growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos) →
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
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse_of_det_ne_zero_of_product_bound_diag_update
      hm hr Ablk pivotInv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hdet n hNn hInvPivot hInvSchur hInvFull

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    BDD first-Schur-tail, determinant-nonzero, stage-local-growth
    source-comparison witness with product/update data.

    The BDD prefix data and shifted recursive tail right-inverse table build
    the all-active pivot right-inverse certificate internally.  The local
    lower-block estimates are supplied by the canonical stage-local-growth
    source-comparison route, and `rho <= 2` is supplied by the
    product-bound/diagonal-update route. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update
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
    let hLocalApos : ∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
      higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) →
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
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
  intro hRhoLocal_le hKappaLocal_le invDiagBound stageInvDiagBound
    hDom hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTail
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse_of_det_ne_zero_of_product_bound_diag_update
      (Nat.succ_pos m) hr Ablk pivotInv hPivotRight hdet n hNn
      hInvPivot hInvSchur hInvFull hRhoLocal_le hKappaLocal_le
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv hPivotInvBound
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    canonical-tail version of the BDD first-Schur-tail stage-local-growth
    source-comparison product/update witness.

    The tail stores each recursive active pivot as `nonsingInv`; the BDD prefix
    data and first pivot identity build the all-active right-inverse table
    before invoking the determinant/product-update source-comparison witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update
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
    let hLocalApos : ∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
      higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) →
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
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
  intro hRhoLocal_le hKappaLocal_le invDiagBound stageInvDiagBound
    hDom hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTailDet
      hTailPivotInv
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse_of_det_ne_zero_of_product_bound_diag_update
      (Nat.succ_pos m) hr Ablk pivotInv hPivotRight hdet n hNn
      hInvPivot hInvSchur hInvFull hRhoLocal_le hKappaLocal_le
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv hPivotInvBound
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    reciprocal-table companion to the shifted-tail BDD first-Schur-tail
    stage-local-growth base-comparison product/update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update_reciprocal
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
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      maxEntryNorm hN (blockMatrixFlatFin Ablk) ≤
        maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) →
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
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
  fun hBaseLocal hKappaLocal_le invDiagBound stageInvDiagBound hDom hDiagBound
      hInitInv (hReciprocal : SchurStageActivePivotInvReciprocal13_7
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))) hProduct
      hDiagUpdate =>
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTail hdet
      n hNn hInvPivot hInvSchur hInvFull hBaseLocal hKappaLocal_le
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    reciprocal-table companion to the canonical-tail BDD first-Schur-tail
    stage-local-growth base-comparison product/update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update_reciprocal
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
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      maxEntryNorm hN (blockMatrixFlatFin Ablk) ≤
        maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) →
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
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
  fun hBaseLocal hKappaLocal_le invDiagBound stageInvDiagBound hDom hDiagBound
      hInitInv (hReciprocal : SchurStageActivePivotInvReciprocal13_7
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))) hProduct
      hDiagUpdate =>
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0
      hTailDet hTailPivotInv hdet n hNn hInvPivot hInvSchur hInvFull
      hBaseLocal hKappaLocal_le invDiagBound stageInvDiagBound hDom hDiagBound
      hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    reciprocal-table companion to the shifted-tail BDD first-Schur-tail
    stage-local-growth source-comparison product/update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update_reciprocal
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
    let hLocalApos : ∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
      higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) →
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
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
  fun hRhoLocal_le hKappaLocal_le invDiagBound stageInvDiagBound hDom hDiagBound
      hInitInv (hReciprocal : SchurStageActivePivotInvReciprocal13_7
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))) hProduct
      hDiagUpdate =>
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0 hTail hdet
      n hNn hInvPivot hInvSchur hInvFull hRhoLocal_le hKappaLocal_le
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equations (13.23) and Problem 13.4:
    reciprocal-table companion to the canonical-tail BDD first-Schur-tail
    stage-local-growth source-comparison product/update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update_reciprocal
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
    let hLocalApos : ∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) :=
      higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
        hr Ablk pivotInv hInvFull
    let hN : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin (m + 1), ∀ hji : j.val < i.val,
      growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          (hLocalApos i j hji) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) →
    (∀ i j : Fin (m + 1), ∀ _hji : j.val < i.val,
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk)))) →
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
  fun hRhoLocal_le hKappaLocal_le invDiagBound stageInvDiagBound hDom hDiagBound
      hInitInv (hReciprocal : SchurStageActivePivotInvReciprocal13_7
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))) hProduct
      hDiagUpdate =>
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_product_bound_diag_update
      hr Ablk pivotInv bddInvDiagBound hPrefix hBDDDom hBDDBound hPivot0
      hTailDet hTailPivotInv hdet n hNn hInvPivot hInvSchur hInvFull
      hRhoLocal_le hKappaLocal_le invDiagBound stageInvDiagBound hDom hDiagBound
      hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

end NumStability
