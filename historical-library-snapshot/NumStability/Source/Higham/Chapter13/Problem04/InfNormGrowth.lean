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
import NumStability.Source.Higham.Chapter13.Equation21
import NumStability.Source.Higham.Chapter13.Problem04.ActiveStageBounds
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStages
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis
import NumStability.Source.Higham.Chapter13.Theorem02.Factorization
import NumStability.Source.Higham.Chapter13.Theorem07.PivotExistence

/-!
# Source.Higham.Chapter13.Problem04.InfNormGrowth

This module formalizes the source-facing Chapter 13 statements for
`Problem04.InfNormGrowth`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, equation (13.21):
    matrix-`∞` active-stage bounds control the assembled matrix-stage upper
    factor in the blockwise matrix-`∞` maximum.

    This is the source-norm endpoint for the matrix-`∞` branch: unlike the
    max-entry transfer below, no factor depending on the block size `r` is
    introduced.  It is still a block-matrix-`∞` endpoint, not the entrywise
    max-norm growth-factor conclusion. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_active_stage_bound
    {m r : ℕ} (hm : 0 < m)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (normMax : ℝ)
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ i.val → k ≤ j.val →
      infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
        2 * normMax) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      2 * normMax := by
  have hRhsNonneg : 0 ≤ 2 * normMax :=
    le_trans
      (infNorm_nonneg
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 ⟨0, hm⟩ ⟨0, hm⟩))
      (hActive 0 ⟨0, hm⟩ ⟨0, hm⟩ (Nat.zero_le _) (Nat.zero_le _))
  apply blockInfNorm_le_of_block_le
  intro i j
  by_cases hij : i.val ≤ j.val
  · have hstage := hActive i.val i j le_rfl hij
    rw [higham13_algorithm13_3_upperFromMatrixStages_eq_of_le A pivotInv hij]
    exact hstage
  · have hji : j.val < i.val := Nat.lt_of_not_ge hij
    exact le_trans
      (infNorm_le_zero_of_eq_zeroBlock
        (higham13_algorithm13_3_upperFromMatrixStages_lower_zero A pivotInv hji))
      hRhsNonneg

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    source-table matrix-`∞` endpoint for the assembled matrix-stage upper
    factor in the blockwise matrix-`∞` maximum.

    This composes the continuous-linear source-table active-stage proof with
    `blockInfNorm` on the input blocks, so the endpoint has right side
    `2 * blockInfNorm A` and no max-entry comparison loss. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_continuousLinearMap_source_table
    {m r : ℕ} (hm : 0 < m)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : Fin r → ℝ,
      matrixMulVecCLM (pivotInv k)
        (matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : Fin r → ℝ,
      matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (matrixMulVecCLM (pivotInv k) y) = y) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_active_stage_bound
      hm A pivotInv (blockInfNorm hm A)
      (fun k i j hik hjk =>
        higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_continuousLinearMap_source_table
          hunit A pivotInv invDiagBound hDom hDiagBound hInit hLeft hRight
          (blockInfNorm hm A) (block_le_blockInfNorm hm A) k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    source-table matrix-`∞` upper-factor endpoint with certified active pivot
    right inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_continuousLinearMap_source_table_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_active_stage_bound
      hm A pivotInv (blockInfNorm hm A)
      (fun k i j hik hjk =>
        higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_continuousLinearMap_source_table_of_pivot_right_inverse
          hunit A pivotInv invDiagBound hDom hDiagBound hInit hPivotRight
          (blockInfNorm hm A) (block_le_blockInfNorm hm A) k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    matrix-`∞` upper-factor endpoint from initial diagonal reciprocal data and
    certified active pivot right inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_initial_diag_right_inverse_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_active_stage_bound
      hm A pivotInv (blockInfNorm hm A)
      (fun k i j hik hjk =>
        higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_initial_diag_right_inverse_of_pivot_right_inverse
          hunit A pivotInv invDiagBound diagInv hDom hInvBound hDiagRight hPivotRight
          (blockInfNorm hm A) (block_le_blockInfNorm hm A) k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, equation (13.21):
    a matrix-`∞` active-stage bound also controls the assembled upper factor in
    the chapter entrywise block max norm, with the input measured in the same
    blockwise matrix-`∞` maximum.

    This keeps the useful output norm from the existing max-entry APIs while
    avoiding the factor `r` that appears when the input is measured by the
    scalar-entry `blockMaxNorm`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_by_blockInfNorm_of_active_stage_bound
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (normMax : ℝ)
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ i.val → k ≤ j.val →
      infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
        2 * normMax) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      2 * normMax :=
  le_trans
    (blockMaxNorm_le_blockInfNorm hm hr
      (higham13_algorithm13_3_upperFromMatrixStages A pivotInv))
    (higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_active_stage_bound
      hm A pivotInv normMax hActive)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    source-table matrix-`∞` upper-factor endpoint in the chapter entrywise
    block max norm, with the input measured by `blockInfNorm`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_by_blockInfNorm_of_continuousLinearMap_source_table
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : Fin r → ℝ,
      matrixMulVecCLM (pivotInv k)
        (matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : Fin r → ℝ,
      matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (matrixMulVecCLM (pivotInv k) y) = y) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_by_blockInfNorm_of_active_stage_bound
      hm hr A pivotInv (blockInfNorm hm A)
      (fun k i j hik hjk =>
        higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_continuousLinearMap_source_table
          hunit A pivotInv invDiagBound hDom hDiagBound hInit hLeft hRight
          (blockInfNorm hm A) (block_le_blockInfNorm hm A) k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    source-table matrix-`∞` upper-factor max-entry endpoint with certified
    active pivot right inverses, with the input measured by `blockInfNorm`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_by_blockInfNorm_of_continuousLinearMap_source_table_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_by_blockInfNorm_of_active_stage_bound
      hm hr A pivotInv (blockInfNorm hm A)
      (fun k i j hik hjk =>
        higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_continuousLinearMap_source_table_of_pivot_right_inverse
          hunit A pivotInv invDiagBound hDom hDiagBound hInit hPivotRight
          (blockInfNorm hm A) (block_le_blockInfNorm hm A) k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    matrix-`∞` upper-factor max-entry endpoint from initial diagonal
    reciprocal data and certified active pivot right inverses, with the input
    measured by `blockInfNorm`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_by_blockInfNorm_of_initial_diag_right_inverse_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_by_blockInfNorm_of_active_stage_bound
      hm hr A pivotInv (blockInfNorm hm A)
      (fun k i j hik hjk =>
        higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_initial_diag_right_inverse_of_pivot_right_inverse
          hunit A pivotInv invDiagBound diagInv hDom hInvBound hDiagRight hPivotRight
          (blockInfNorm hm A) (block_le_blockInfNorm hm A) k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.23):
    source-table matrix-`∞` endpoint for the finite matrix-stage history
    scalar, with the input measured by `blockInfNorm`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryInfBound_le_of_continuousLinearMap_source_table
    {m r : ℕ} (hm : 0 < m)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : Fin r → ℝ,
      matrixMulVecCLM (pivotInv k)
        (matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : Fin r → ℝ,
      matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (matrixMulVecCLM (pivotInv k) y) = y) :
    higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
      2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrixStageHistoryInfBound_le_two_of_active_stage_bound
      hm A pivotInv (blockInfNorm hm A)
      (fun k i j _hk hik hjk =>
        higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_continuousLinearMap_source_table
          hunit A pivotInv invDiagBound hDom hDiagBound hInit hLeft hRight
          (blockInfNorm hm A) (block_le_blockInfNorm hm A) k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.23):
    pivot-right-inverse source-table matrix-`∞` endpoint for the finite
    matrix-stage history scalar, with the input measured by `blockInfNorm`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryInfBound_le_of_continuousLinearMap_source_table_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
      2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrixStageHistoryInfBound_le_two_of_active_stage_bound
      hm A pivotInv (blockInfNorm hm A)
      (fun k i j _hk hik hjk =>
        higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_continuousLinearMap_source_table_of_pivot_right_inverse
          hunit A pivotInv invDiagBound hDom hDiagBound hInit hPivotRight
          (blockInfNorm hm A) (block_le_blockInfNorm hm A) k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.23):
    initial-diagonal/right-inverse matrix-`∞` endpoint for the finite
    matrix-stage history scalar, with the input measured by `blockInfNorm`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryInfBound_le_of_initial_diag_right_inverse_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
      2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrixStageHistoryInfBound_le_two_of_active_stage_bound
      hm A pivotInv (blockInfNorm hm A)
      (fun k i j _hk hik hjk =>
        higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_initial_diag_right_inverse_of_pivot_right_inverse
          hunit A pivotInv invDiagBound diagInv hDom hInvBound hDiagRight hPivotRight
          (blockInfNorm hm A) (block_le_blockInfNorm hm A) k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    paired matrix-`∞` source-table endpoint.

    The first component bounds the assembled matrix-stage upper factor in
    `blockInfNorm`; the second component bounds the finite matrix-stage history
    scalar in the same source norm.  This is a source-norm dependency package,
    not the max-entry `rho <= 2` theorem. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_continuousLinearMap_source_table
    {m r : ℕ} (hm : 0 < m)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : Fin r → ℝ,
      matrixMulVecCLM (pivotInv k)
        (matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : Fin r → ℝ,
      matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (matrixMulVecCLM (pivotInv k) y) = y) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockInfNorm hm A ∧
      higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
        2 * blockInfNorm hm A :=
  ⟨higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_continuousLinearMap_source_table
      hm hunit A pivotInv invDiagBound hDom hDiagBound hInit hLeft hRight,
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryInfBound_le_of_continuousLinearMap_source_table
      hm hunit A pivotInv invDiagBound hDom hDiagBound hInit hLeft hRight⟩

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    paired matrix-`∞` source-table endpoint with certified active pivot right
    inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_continuousLinearMap_source_table_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockInfNorm hm A ∧
      higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
        2 * blockInfNorm hm A :=
  ⟨higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_continuousLinearMap_source_table_of_pivot_right_inverse
      hm hunit A pivotInv invDiagBound hDom hDiagBound hInit hPivotRight,
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryInfBound_le_of_continuousLinearMap_source_table_of_pivot_right_inverse
      hm hunit A pivotInv invDiagBound hDom hDiagBound hInit hPivotRight⟩

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    paired matrix-`∞` endpoint from initial diagonal reciprocal data and
    certified active pivot right inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_initial_diag_right_inverse_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockInfNorm hm A ∧
      higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
        2 * blockInfNorm hm A :=
  ⟨higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_initial_diag_right_inverse_of_pivot_right_inverse
      hm hunit A pivotInv invDiagBound diagInv hDom hInvBound hDiagRight
      hPivotRight,
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryInfBound_le_of_initial_diag_right_inverse_of_pivot_right_inverse
      hm hunit A pivotInv invDiagBound diagInv hDom hInvBound hDiagRight
      hPivotRight⟩

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    matrix-`∞` active-stage bounds control the existing max-entry finite
    matrix-stage history growth object, with the input measured by
    `blockInfNorm`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthMatrix_bound_by_blockInfNorm_of_active_stage_bound
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
        2 * blockInfNorm hm A) :
    maxEntryNorm hN
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr A pivotInv) ≤
      2 * blockInfNorm hm A :=
  higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_le_of_active_bound
    hN hm hr A pivotInv
    (fun k i j hk hik hjk =>
      higham13_algorithm13_3_matrix_infNorm_active_stage_maxEntry_bound
        hr A pivotInv (blockInfNorm hm A) hActive k i j hk hik hjk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.23):
    source-table matrix-`∞` endpoint for the existing max-entry finite
    matrix-stage history growth object, with the input measured by
    `blockInfNorm`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthMatrix_bound_by_blockInfNorm_of_continuousLinearMap_source_table
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : Fin r → ℝ,
      matrixMulVecCLM (pivotInv k)
        (matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : Fin r → ℝ,
      matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (matrixMulVecCLM (pivotInv k) y) = y) :
    maxEntryNorm hN
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr A pivotInv) ≤
      2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthMatrix_bound_by_blockInfNorm_of_active_stage_bound
      hN hm hr A pivotInv
      (fun k i j _hk hik hjk =>
        higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_continuousLinearMap_source_table
          hunit A pivotInv invDiagBound hDom hDiagBound hInit hLeft hRight
          (blockInfNorm hm A) (block_le_blockInfNorm hm A) k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.23):
    pivot-right-inverse source-table matrix-`∞` endpoint for the existing
    max-entry finite matrix-stage history growth object, with the input
    measured by `blockInfNorm`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthMatrix_bound_by_blockInfNorm_of_continuousLinearMap_source_table_of_pivot_right_inverse
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    maxEntryNorm hN
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr A pivotInv) ≤
      2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthMatrix_bound_by_blockInfNorm_of_active_stage_bound
      hN hm hr A pivotInv
      (fun k i j _hk hik hjk =>
        higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_continuousLinearMap_source_table_of_pivot_right_inverse
          hunit A pivotInv invDiagBound hDom hDiagBound hInit hPivotRight
          (blockInfNorm hm A) (block_le_blockInfNorm hm A) k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.23):
    initial-diagonal/right-inverse matrix-`∞` endpoint for the existing
    max-entry finite matrix-stage history growth object, with the input
    measured by `blockInfNorm`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthMatrix_bound_by_blockInfNorm_of_initial_diag_right_inverse_of_pivot_right_inverse
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    maxEntryNorm hN
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr A pivotInv) ≤
      2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthMatrix_bound_by_blockInfNorm_of_active_stage_bound
      hN hm hr A pivotInv
      (fun k i j _hk hik hjk =>
        higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_initial_diag_right_inverse_of_pivot_right_inverse
          hunit A pivotInv invDiagBound diagInv hDom hInvBound hDiagRight hPivotRight
          (blockInfNorm hm A) (block_le_blockInfNorm hm A) k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, equation (13.21):
    matrix-`∞` active-stage bounds control the assembled matrix-stage upper
    factor in the chapter max-entry block norm.

    This is the max-entry transfer layer for the matrix-`∞` route.  The final
    source-strength conclusion still requires proving the active-stage bound
    with `normMax = ‖A‖` in the chapter norm; the corollaries below record the
    currently available dimension-aware `r‖A‖` specialization. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_of_active_stage_bound
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (normMax : ℝ)
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
        2 * normMax) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      2 * normMax := by
  exact le_trans
    (higham13_algorithm13_3_matrixStageHistoryBound_contains_upperFromMatrixStages
      hm hr A pivotInv)
    (higham13_algorithm13_3_matrixStageHistoryBound_le_of_stage_bound
      hm hr A pivotInv
      (fun k hk =>
        higham13_algorithm13_3_matrixStage_blockMaxNorm_bound_of_active_bound
          hm hr A pivotInv
          (fun k i j hk hik hjk =>
            higham13_algorithm13_3_matrix_infNorm_active_stage_maxEntry_bound
              hr A pivotInv normMax hActive k i j hk hik hjk)
          k hk))

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    matrix-`∞` active-stage bounds control the finite matrix-stage history
    growth object in max-entry norm. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthMatrix_le_of_active_stage_bound
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (normMax : ℝ)
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
        2 * normMax) :
    maxEntryNorm hN
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr A pivotInv) ≤
      2 * normMax := by
  exact
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_le_of_active_bound
      hN hm hr A pivotInv
      (fun k i j hk hik hjk =>
        higham13_algorithm13_3_matrix_infNorm_active_stage_maxEntry_bound
          hr A pivotInv normMax hActive k i j hk hik hjk)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    a dimension-aware growth-factor consequence of the matrix-`∞` active-stage
    route.

    The conclusion is `ρ <= 2*r`, not the printed `ρ <= 2`; it records the
    exact loss incurred when the current matrix-`∞` proof is transferred to the
    chapter max-entry denominator by `infNorm <= r * maxEntryNorm`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthFactor_le_card_of_active_stage_bound
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A)) :
    growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
      2 * (r : ℝ) := by
  exact
    growthFactorEntry_le_of_maxEntryNorm_le_mul
      (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        (Nat.mul_pos hm hr) hm hr A pivotInv)
      hApos
      (by
        rw [maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm hm hr A]
        simpa [mul_assoc] using
          higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthMatrix_le_of_active_stage_bound
            (Nat.mul_pos hm hr) hm hr A pivotInv
            ((r : ℝ) * blockMaxNorm hm hr A) hActive)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    dimension-aware max-entry upper-factor bound from the matrix-`∞`
    continuous-linear source-table route.

    This composes the source-table active-stage theorem with the max-entry
    transfer layer.  It keeps the initial lower table and active two-sided
    inverse identities explicit, and its right side is `2*r*‖A‖`, not the
    source-strength `2*‖A‖`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_with_card_of_continuousLinearMap_source_table
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : Fin r → ℝ,
      matrixMulVecCLM (pivotInv k)
        (matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : Fin r → ℝ,
      matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (matrixMulVecCLM (pivotInv k) y) = y) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      2 * ((r : ℝ) * blockMaxNorm hm hr A) := by
  have hMax : ∀ i j : Fin m,
      infNorm (A i j) ≤ (r : ℝ) * blockMaxNorm hm hr A := by
    intro i j
    exact
      higham13_algorithm13_3_matrix_infNorm_block_le_card_mul_blockMaxNorm
        hm hr A i j
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_of_active_stage_bound
      hm hr A pivotInv ((r : ℝ) * blockMaxNorm hm hr A)
      (fun k i j _hk hik hjk =>
        higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_continuousLinearMap_source_table
          hunit A pivotInv invDiagBound hDom hDiagBound hInit hLeft hRight
          ((r : ℝ) * blockMaxNorm hm hr A) hMax k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.23):
    dimension-aware finite-history growth-factor bound from the matrix-`∞`
    continuous-linear source-table route.

    The conclusion is the current transferred endpoint `ρ <= 2*r`; the printed
    `ρ <= 2` source row remains open. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthFactor_le_card_of_continuousLinearMap_source_table
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : Fin r → ℝ,
      matrixMulVecCLM (pivotInv k)
        (matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : Fin r → ℝ,
      matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (matrixMulVecCLM (pivotInv k) y) = y) :
    growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
      2 * (r : ℝ) := by
  have hMax : ∀ i j : Fin m,
      infNorm (A i j) ≤ (r : ℝ) * blockMaxNorm hm hr A := by
    intro i j
    exact
      higham13_algorithm13_3_matrix_infNorm_block_le_card_mul_blockMaxNorm
        hm hr A i j
  exact
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthFactor_le_card_of_active_stage_bound
      hm hr A pivotInv hApos
      (fun k i j _hk hik hjk =>
        higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_continuousLinearMap_source_table
          hunit A pivotInv invDiagBound hDom hDiagBound hInit hLeft hRight
          ((r : ℝ) * blockMaxNorm hm hr A) hMax k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    package of the dimension-aware max-entry consequences obtained from the
    matrix-`∞` continuous-linear source-table route. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_continuousLinearMap_source_table
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : Fin r → ℝ,
      matrixMulVecCLM (pivotInv k)
        (matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : Fin r → ℝ,
      matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (matrixMulVecCLM (pivotInv k) y) = y) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 * (r : ℝ) :=
  ⟨higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_with_card_of_continuousLinearMap_source_table
      hm hr hunit A pivotInv invDiagBound hDom hDiagBound hInit hLeft hRight,
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthFactor_le_card_of_continuousLinearMap_source_table
      hm hr hunit A pivotInv hApos invDiagBound hDom hDiagBound hInit hLeft hRight⟩

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    determinant-nonzero form of the dimension-aware matrix-`∞` source-table
    max-entry package.

    This removes the separate positive growth-denominator premise from the
    source-table surface by deriving it from
    `det (blockMatrixFlatFin A) != 0`.  The endpoint remains the
    dimension-aware `2*r` transfer, not the printed `rho <= 2`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_continuousLinearMap_source_table_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : Fin r → ℝ,
      matrixMulVecCLM (pivotInv k)
        (matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : Fin r → ℝ,
      matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (matrixMulVecCLM (pivotInv k) y) = y) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet) ≤
        2 * (r : ℝ) := by
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin A) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin A) hdet
  simpa [hN, hApos] using
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_continuousLinearMap_source_table
      hm hr hunit A pivotInv hApos invDiagBound hDom hDiagBound hInit hLeft hRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    positive-block-size form of the matrix-`∞` source-table max-entry package.

    This removes the artificial finite unit-sphere witness from the raw
    continuous-linear source-table endpoint.  The result is still the
    dimension-aware `2*r` transfer, not the printed dimension-free
    Eq.13.21/`rho <= 2` theorem. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_continuousLinearMap_source_table_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          (higham13_fin_fun_unit_sphere_nonempty hr))
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : Fin r → ℝ,
      matrixMulVecCLM (pivotInv k)
        (matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : Fin r → ℝ,
      matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (matrixMulVecCLM (pivotInv k) y) = y) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_continuousLinearMap_source_table
      hm hr (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv hApos
      invDiagBound hDom hDiagBound hInit hLeft hRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    dimension-aware max-entry upper-factor bound from matrix-`∞` source-table
    data and certified active pivot right inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_with_card_of_continuousLinearMap_source_table_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      2 * ((r : ℝ) * blockMaxNorm hm hr A) := by
  have hMax : ∀ i j : Fin m,
      infNorm (A i j) ≤ (r : ℝ) * blockMaxNorm hm hr A := by
    intro i j
    exact
      higham13_algorithm13_3_matrix_infNorm_block_le_card_mul_blockMaxNorm
        hm hr A i j
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_of_active_stage_bound
      hm hr A pivotInv ((r : ℝ) * blockMaxNorm hm hr A)
      (fun k i j _hk hik hjk =>
        higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_continuousLinearMap_source_table_of_pivot_right_inverse
          hunit A pivotInv invDiagBound hDom hDiagBound hInit hPivotRight
          ((r : ℝ) * blockMaxNorm hm hr A) hMax k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.23):
    dimension-aware finite-history growth-factor bound from matrix-`∞`
    source-table data and certified active pivot right inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthFactor_le_card_of_continuousLinearMap_source_table_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
      2 * (r : ℝ) := by
  have hMax : ∀ i j : Fin m,
      infNorm (A i j) ≤ (r : ℝ) * blockMaxNorm hm hr A := by
    intro i j
    exact
      higham13_algorithm13_3_matrix_infNorm_block_le_card_mul_blockMaxNorm
        hm hr A i j
  exact
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthFactor_le_card_of_active_stage_bound
      hm hr A pivotInv hApos
      (fun k i j _hk hik hjk =>
        higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_continuousLinearMap_source_table_of_pivot_right_inverse
          hunit A pivotInv invDiagBound hDom hDiagBound hInit hPivotRight
          ((r : ℝ) * blockMaxNorm hm hr A) hMax k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    package of the dimension-aware max-entry consequences obtained from
    matrix-`∞` source-table data plus active pivot right inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_continuousLinearMap_source_table_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 * (r : ℝ) :=
  ⟨higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_with_card_of_continuousLinearMap_source_table_of_pivot_right_inverse
      hm hr hunit A pivotInv invDiagBound hDom hDiagBound hInit hPivotRight,
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthFactor_le_card_of_continuousLinearMap_source_table_of_pivot_right_inverse
      hm hr hunit A pivotInv hApos invDiagBound hDom hDiagBound hInit hPivotRight⟩

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    determinant-nonzero form of the pivot-right-inverse matrix-`∞`
    source-table max-entry package.

    The determinant hypothesis is used only to derive the positive
    growth-factor denominator; the source-table and active pivot right-inverse
    certificates remain explicit. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_continuousLinearMap_source_table_of_pivot_right_inverse_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet) ≤
        2 * (r : ℝ) := by
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin A) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin A) hdet
  simpa [hN, hApos] using
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_continuousLinearMap_source_table_of_pivot_right_inverse
      hm hr hunit A pivotInv hApos invDiagBound hDom hDiagBound hInit hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    determinant-nonzero positive-block-size form of the matrix-`∞`
    source-table max-entry package. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_continuousLinearMap_source_table_of_det_ne_zero_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          (higham13_fin_fun_unit_sphere_nonempty hr))
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : Fin r → ℝ,
      matrixMulVecCLM (pivotInv k)
        (matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : Fin r → ℝ,
      matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (matrixMulVecCLM (pivotInv k) y) = y) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet) ≤
        2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_continuousLinearMap_source_table_of_det_ne_zero
      hm hr (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv
      invDiagBound hdet hDom hDiagBound hInit hLeft hRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    positive-block-size form of the pivot-right-inverse matrix-`∞`
    source-table max-entry package. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_continuousLinearMap_source_table_of_pivot_right_inverse_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          (higham13_fin_fun_unit_sphere_nonempty hr))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_continuousLinearMap_source_table_of_pivot_right_inverse
      hm hr (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv hApos
      invDiagBound hDom hDiagBound hInit hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    determinant-nonzero positive-block-size form of the pivot-right-inverse
    matrix-`∞` source-table max-entry package. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_continuousLinearMap_source_table_of_pivot_right_inverse_of_det_ne_zero_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          (higham13_fin_fun_unit_sphere_nonempty hr))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet) ≤
        2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_continuousLinearMap_source_table_of_pivot_right_inverse_of_det_ne_zero
      hm hr (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv
      invDiagBound hdet hDom hDiagBound hInit hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    dimension-aware max-entry upper-factor bound from initial diagonal
    reciprocal data and certified active pivot right inverses in the
    matrix-`∞` route. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_with_card_of_initial_diag_right_inverse_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      2 * ((r : ℝ) * blockMaxNorm hm hr A) := by
  have hMax : ∀ i j : Fin m,
      infNorm (A i j) ≤ (r : ℝ) * blockMaxNorm hm hr A := by
    intro i j
    exact
      higham13_algorithm13_3_matrix_infNorm_block_le_card_mul_blockMaxNorm
        hm hr A i j
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_of_active_stage_bound
      hm hr A pivotInv ((r : ℝ) * blockMaxNorm hm hr A)
      (fun k i j hk hik hjk =>
        higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_initial_diag_right_inverse_of_pivot_right_inverse
          hunit A pivotInv invDiagBound diagInv hDom hInvBound hDiagRight
          hPivotRight ((r : ℝ) * blockMaxNorm hm hr A) hMax
          k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.23):
    dimension-aware finite-history growth-factor bound from initial diagonal
    reciprocal data and certified active pivot right inverses in the
    matrix-`∞` route.

    This is a proved max-entry consequence of the matrix-`∞` source-table
    branch, but it remains weaker than the printed `ρ <= 2` endpoint by the
    explicit factor `r`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthFactor_le_card_of_initial_diag_right_inverse_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
      2 * (r : ℝ) := by
  have hMax : ∀ i j : Fin m,
      infNorm (A i j) ≤ (r : ℝ) * blockMaxNorm hm hr A := by
    intro i j
    exact
      higham13_algorithm13_3_matrix_infNorm_block_le_card_mul_blockMaxNorm
        hm hr A i j
  exact
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthFactor_le_card_of_active_stage_bound
      hm hr A pivotInv hApos
      (fun k i j hk hik hjk =>
        higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_initial_diag_right_inverse_of_pivot_right_inverse
          hunit A pivotInv invDiagBound diagInv hDom hInvBound hDiagRight
          hPivotRight ((r : ℝ) * blockMaxNorm hm hr A) hMax
          k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    package of the dimension-aware max-entry consequences currently obtained
    from the matrix-`∞` initial-diagonal/right-inverse route.

    The first component is the Eq.13.21-style upper-factor max-entry bound with
    right side `2*r*‖A‖`; the second component is the matching finite-history
    growth-factor bound `ρ <= 2*r`.  The source-strength `2*‖A‖` and `ρ <= 2`
    rows remain open. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_initial_diag_right_inverse_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 * (r : ℝ) :=
  ⟨higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_with_card_of_initial_diag_right_inverse_of_pivot_right_inverse
      hm hr hunit A pivotInv invDiagBound diagInv hDom hInvBound hDiagRight
      hPivotRight,
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthFactor_le_card_of_initial_diag_right_inverse_of_pivot_right_inverse
      hm hr hunit A pivotInv hApos invDiagBound diagInv hDom hInvBound
      hDiagRight hPivotRight⟩

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    determinant-nonzero form of the matrix-`∞`
    initial-diagonal/right-inverse max-entry package.

    This is the reciprocal-initial-table specialization of the source-table
    determinant wrappers above.  The determinant hypothesis supplies only the
    positive growth-factor denominator; the diagonal reciprocal and active
    pivot right-inverse data remain explicit. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_initial_diag_right_inverse_of_pivot_right_inverse_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet) ≤
        2 * (r : ℝ) := by
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin A) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin A) hdet
  simpa [hN, hApos] using
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_initial_diag_right_inverse_of_pivot_right_inverse
      hm hr hunit A pivotInv hApos invDiagBound diagInv hDom hInvBound
      hDiagRight hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    positive-block-size form of the initial-diagonal/right-inverse
    dimension-aware max-entry upper-factor route.

    This has the same conclusion as
    `higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_with_card_of_initial_diag_right_inverse_of_pivot_right_inverse`;
    the finite unit-sphere witness is constructed from `0 < r`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_with_card_of_initial_diag_right_inverse_of_pivot_right_inverse_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      2 * ((r : ℝ) * blockMaxNorm hm hr A) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_with_card_of_initial_diag_right_inverse_of_pivot_right_inverse
      hm hr (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv
      invDiagBound diagInv hDom hInvBound hDiagRight hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.23):
    positive-block-size form of the initial-diagonal/right-inverse
    dimension-aware finite-history growth-factor route.

    This discharges the finite unit-sphere witness from `0 < r`; the endpoint
    remains the currently proved `growthFactorEntry <= 2*r` max-entry transfer,
    not the printed dimension-free `rho <= 2` theorem. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthFactor_le_card_of_initial_diag_right_inverse_of_pivot_right_inverse_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
      2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthFactor_le_card_of_initial_diag_right_inverse_of_pivot_right_inverse
      hm hr (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv hApos
      invDiagBound diagInv hDom hInvBound hDiagRight hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    positive-block-size package for the initial-diagonal/right-inverse
    dimension-aware max-entry transfer.

    The two conclusions are unchanged from the witness-taking package: the
    assembled upper factor is bounded by `2*r*‖A‖`, and the matching finite
    history growth factor is bounded by `2*r`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_initial_diag_right_inverse_of_pivot_right_inverse_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_initial_diag_right_inverse_of_pivot_right_inverse
      hm hr (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv hApos
      invDiagBound diagInv hDom hInvBound hDiagRight hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    determinant-nonzero positive-block-size form of the
    initial-diagonal/right-inverse max-entry transfer package.

    The determinant hypothesis supplies the positive growth-factor denominator;
    `0 < r` supplies the finite unit-sphere witness. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_initial_diag_right_inverse_of_pivot_right_inverse_of_det_ne_zero_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet) ≤
        2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_initial_diag_right_inverse_of_pivot_right_inverse_of_det_ne_zero
      hm hr (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv
      invDiagBound diagInv hdet hDom hInvBound hDiagRight hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    matrix-`∞` active-stage bound from the source-shaped reciprocal initial
    diagonal table.

    This specializes
    `higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_initial_diag_right_inverse_of_pivot_right_inverse`
    to the natural table
    `invDiagBound j = ‖diagInv j‖∞⁻¹`, removing the separate
    `invDiagBound j <= ‖diagInv j‖∞⁻¹` proof artifact.  The endpoint remains
    the matrix-`∞`/dimension-aware dependency route, not the printed
    max-entry `ρ <= 2` theorem. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_reciprocal_diag_right_inverse_of_pivot_right_inverse
    {m r : ℕ}
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (diagInv j))⁻¹))
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, infNorm (A i j) ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
      2 * normMax := by
  exact
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_initial_diag_right_inverse_of_pivot_right_inverse
      hunit A pivotInv (fun j : Fin m => (infNorm (diagInv j))⁻¹)
      diagInv hDom (fun _j => le_rfl) hDiagRight hPivotRight
      normMax hMax k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    matrix-`∞` upper-factor endpoint from the source-shaped reciprocal initial
    diagonal table and certified active pivot right inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_reciprocal_diag_right_inverse_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (diagInv j))⁻¹))
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_initial_diag_right_inverse_of_pivot_right_inverse
      hm hunit A pivotInv (fun j : Fin m => (infNorm (diagInv j))⁻¹)
      diagInv hDom (fun _j => le_rfl) hDiagRight hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.23):
    finite matrix-stage-history matrix-`∞` endpoint from the source-shaped
    reciprocal initial diagonal table and certified active pivot right
    inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryInfBound_le_of_reciprocal_diag_right_inverse_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (diagInv j))⁻¹))
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
      2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryInfBound_le_of_initial_diag_right_inverse_of_pivot_right_inverse
      hm hunit A pivotInv (fun j : Fin m => (infNorm (diagInv j))⁻¹)
      diagInv hDom (fun _j => le_rfl) hDiagRight hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    paired matrix-`∞` endpoint from the source-shaped reciprocal initial
    diagonal table and certified active pivot right inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_reciprocal_diag_right_inverse_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (diagInv j))⁻¹))
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockInfNorm hm A ∧
      higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
        2 * blockInfNorm hm A :=
  ⟨higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_reciprocal_diag_right_inverse_of_pivot_right_inverse
      hm hunit A pivotInv diagInv hDom hDiagRight hPivotRight,
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryInfBound_le_of_reciprocal_diag_right_inverse_of_pivot_right_inverse
      hm hunit A pivotInv diagInv hDom hDiagRight hPivotRight⟩

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    dimension-aware max-entry package from the source-shaped reciprocal
    initial diagonal table.

    The result removes the separate reciprocal-bound hypothesis from the
    strongest currently proved matrix-`∞` route.  It still concludes
    `growthFactorEntry <= 2*r`, not the printed dimension-free `ρ <= 2`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_reciprocal_diag_right_inverse_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (diagInv j))⁻¹))
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_initial_diag_right_inverse_of_pivot_right_inverse
      hm hr hunit A pivotInv hApos
      (fun j : Fin m => (infNorm (diagInv j))⁻¹) diagInv hDom
      (fun _j => le_rfl) hDiagRight hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    positive-block-size form of the reciprocal diagonal right-inverse
    active-stage matrix-`∞` route.

    This is the same theorem as
    `higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_reciprocal_diag_right_inverse_of_pivot_right_inverse`,
    with the finite-dimensional unit-sphere witness supplied from `0 < r`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_reciprocal_diag_right_inverse_of_pivot_right_inverse_of_pos_dim
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (diagInv j))⁻¹))
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, infNorm (A i j) ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
      2 * normMax := by
  exact
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_reciprocal_diag_right_inverse_of_pivot_right_inverse
      (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv diagInv hDom
      hDiagRight hPivotRight normMax hMax k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    positive-block-size form of the reciprocal diagonal right-inverse
    matrix-`∞` package.

    The conclusion and constants are unchanged from
    `higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_reciprocal_diag_right_inverse_of_pivot_right_inverse`;
    only the artificial unit-sphere witness is discharged from `0 < r`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_reciprocal_diag_right_inverse_of_pivot_right_inverse_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (diagInv j))⁻¹))
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_reciprocal_diag_right_inverse_of_pivot_right_inverse
      hm hr (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv hApos
      diagInv hDom hDiagRight hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    determinant-nonzero form of the reciprocal initial diagonal table package.

    The determinant hypothesis supplies only the positive growth-factor
    denominator; diagonal reciprocal data and active pivot right inverses remain
    explicit. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_reciprocal_diag_right_inverse_of_pivot_right_inverse_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (diagInv j))⁻¹))
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet) ≤
        2 * (r : ℝ) := by
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin A) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin A) hdet
  simpa [hN, hApos] using
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_reciprocal_diag_right_inverse_of_pivot_right_inverse
      hm hr hunit A pivotInv hApos diagInv hDom hDiagRight hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    determinant-nonzero positive-block-size form of the reciprocal initial
    diagonal table package.

    This removes the finite unit-sphere witness from the determinant-denominator
    endpoint by constructing it from `0 < r`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_reciprocal_diag_right_inverse_of_pivot_right_inverse_of_det_ne_zero_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (diagInv j))⁻¹))
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet) ≤
        2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_reciprocal_diag_right_inverse_of_pivot_right_inverse_of_det_ne_zero
      hm hr (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv diagInv
      hdet hDom hDiagRight hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    matrix-`∞` active-stage bound using the canonical `nonsingInv` of each
    initial diagonal block.

    This is the determinant-nonzero diagonal-block specialization of
    `higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_reciprocal_diag_right_inverse_of_pivot_right_inverse`.
    It removes the explicit diagonal inverse object from the reciprocal-table
    route, but still leaves the active pivot right-inverse data explicit. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_nonsingInv_diag_of_pivot_right_inverse
    {m r : ℕ}
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hDiagDet : ∀ j : Fin m, Matrix.det (A j j) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (nonsingInv r (A j j)))⁻¹))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, infNorm (A i j) ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
      2 * normMax := by
  have hDiagRight :
      ∀ j : Fin m, IsRightInverse r (A j j) (nonsingInv r (A j j)) := by
    intro j
    exact (isInverse_nonsingInv_of_det_ne_zero r (A j j) (hDiagDet j)).2
  exact
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_reciprocal_diag_right_inverse_of_pivot_right_inverse
      hunit A pivotInv (fun j : Fin m => nonsingInv r (A j j))
      hDom hDiagRight hPivotRight normMax hMax k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    matrix-`∞` upper-factor endpoint using canonical initial diagonal
    `nonsingInv` blocks. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_nonsingInv_diag_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hDiagDet : ∀ j : Fin m, Matrix.det (A j j) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (nonsingInv r (A j j)))⁻¹))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      2 * blockInfNorm hm A := by
  have hDiagRight :
      ∀ j : Fin m, IsRightInverse r (A j j) (nonsingInv r (A j j)) := by
    intro j
    exact (isInverse_nonsingInv_of_det_ne_zero r (A j j) (hDiagDet j)).2
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_reciprocal_diag_right_inverse_of_pivot_right_inverse
      hm hunit A pivotInv (fun j : Fin m => nonsingInv r (A j j))
      hDom hDiagRight hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.23):
    finite matrix-stage-history matrix-`∞` endpoint using canonical initial
    diagonal `nonsingInv` blocks. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryInfBound_le_of_nonsingInv_diag_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hDiagDet : ∀ j : Fin m, Matrix.det (A j j) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (nonsingInv r (A j j)))⁻¹))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
      2 * blockInfNorm hm A := by
  have hDiagRight :
      ∀ j : Fin m, IsRightInverse r (A j j) (nonsingInv r (A j j)) := by
    intro j
    exact (isInverse_nonsingInv_of_det_ne_zero r (A j j) (hDiagDet j)).2
  exact
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryInfBound_le_of_reciprocal_diag_right_inverse_of_pivot_right_inverse
      hm hunit A pivotInv (fun j : Fin m => nonsingInv r (A j j))
      hDom hDiagRight hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    paired matrix-`∞` endpoint using canonical initial diagonal `nonsingInv`
    blocks and certified active pivot right inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_nonsingInv_diag_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hDiagDet : ∀ j : Fin m, Matrix.det (A j j) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (nonsingInv r (A j j)))⁻¹))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockInfNorm hm A ∧
      higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
        2 * blockInfNorm hm A :=
  ⟨higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_nonsingInv_diag_of_pivot_right_inverse
      hm hunit A pivotInv hDiagDet hDom hPivotRight,
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryInfBound_le_of_nonsingInv_diag_of_pivot_right_inverse
      hm hunit A pivotInv hDiagDet hDom hPivotRight⟩

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    dimension-aware max-entry package using canonical initial diagonal
    `nonsingInv` blocks.

    This removes explicit diagonal inverse witnesses from the matrix-`∞`
    reciprocal-table package, while retaining the dimension-aware
    `growthFactorEntry <= 2*r` conclusion. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_nonsingInv_diag_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (hDiagDet : ∀ j : Fin m, Matrix.det (A j j) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (nonsingInv r (A j j)))⁻¹))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 * (r : ℝ) := by
  have hDiagRight :
      ∀ j : Fin m, IsRightInverse r (A j j) (nonsingInv r (A j j)) := by
    intro j
    exact (isInverse_nonsingInv_of_det_ne_zero r (A j j) (hDiagDet j)).2
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_reciprocal_diag_right_inverse_of_pivot_right_inverse
      hm hr hunit A pivotInv hApos (fun j : Fin m => nonsingInv r (A j j))
      hDom hDiagRight hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    determinant-nonzero growth-denominator form of the canonical diagonal
    `nonsingInv` matrix-`∞` package. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_nonsingInv_diag_of_pivot_right_inverse_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hDiagDet : ∀ j : Fin m, Matrix.det (A j j) ≠ 0)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (nonsingInv r (A j j)))⁻¹))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet) ≤
        2 * (r : ℝ) := by
  have hDiagRight :
      ∀ j : Fin m, IsRightInverse r (A j j) (nonsingInv r (A j j)) := by
    intro j
    exact (isInverse_nonsingInv_of_det_ne_zero r (A j j) (hDiagDet j)).2
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_reciprocal_diag_right_inverse_of_pivot_right_inverse_of_det_ne_zero
      hm hr hunit A pivotInv (fun j : Fin m => nonsingInv r (A j j))
      hdet hDom hDiagRight hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    matrix-`∞` active-stage bound with canonical initial diagonal inverses and
    canonical active pivot inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_nonsingInv_diag_of_pivotInv_eq_nonsingInv
    {m r : ℕ}
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hDiagDet : ∀ j : Fin m, Matrix.det (A j j) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (nonsingInv r (A j j)))⁻¹))
    (hPivotDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv k =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩))
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, infNorm (A i j) ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
      2 * normMax := by
  exact
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_nonsingInv_diag_of_pivot_right_inverse
      hunit A pivotInv hDiagDet hDom
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        A pivotInv hPivotDet hPivotInv)
      normMax hMax k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    matrix-`∞` upper-factor endpoint with canonical initial diagonal inverses
    and canonical active pivot inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_nonsingInv_diag_of_pivotInv_eq_nonsingInv
    {m r : ℕ} (hm : 0 < m)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hDiagDet : ∀ j : Fin m, Matrix.det (A j j) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (nonsingInv r (A j j)))⁻¹))
    (hPivotDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv k =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_nonsingInv_diag_of_pivot_right_inverse
      hm hunit A pivotInv hDiagDet hDom
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        A pivotInv hPivotDet hPivotInv)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.23):
    finite matrix-stage-history matrix-`∞` endpoint with canonical initial
    diagonal inverses and canonical active pivot inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryInfBound_le_of_nonsingInv_diag_of_pivotInv_eq_nonsingInv
    {m r : ℕ} (hm : 0 < m)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hDiagDet : ∀ j : Fin m, Matrix.det (A j j) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (nonsingInv r (A j j)))⁻¹))
    (hPivotDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv k =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)) :
    higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
      2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryInfBound_le_of_nonsingInv_diag_of_pivot_right_inverse
      hm hunit A pivotInv hDiagDet hDom
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        A pivotInv hPivotDet hPivotInv)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    paired matrix-`∞` endpoint with canonical initial diagonal inverses and
    canonical active pivot inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_nonsingInv_diag_of_pivotInv_eq_nonsingInv
    {m r : ℕ} (hm : 0 < m)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hDiagDet : ∀ j : Fin m, Matrix.det (A j j) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (nonsingInv r (A j j)))⁻¹))
    (hPivotDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv k =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockInfNorm hm A ∧
      higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
        2 * blockInfNorm hm A :=
  ⟨higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_nonsingInv_diag_of_pivotInv_eq_nonsingInv
      hm hunit A pivotInv hDiagDet hDom hPivotDet hPivotInv,
    higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryInfBound_le_of_nonsingInv_diag_of_pivotInv_eq_nonsingInv
      hm hunit A pivotInv hDiagDet hDom hPivotDet hPivotInv⟩

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    positive-block-size form of the paired raw continuous-linear source-table
    matrix-`∞` endpoint.

    This removes the artificial finite unit-sphere witness from the source-norm
    dependency route.  The theorem remains a matrix-`∞` source-norm endpoint; it
    is not the printed dimension-free max-entry growth theorem. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_continuousLinearMap_source_table_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          (higham13_fin_fun_unit_sphere_nonempty hr))
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : Fin r → ℝ,
      matrixMulVecCLM (pivotInv k)
        (matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : Fin r → ℝ,
      matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (matrixMulVecCLM (pivotInv k) y) = y) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockInfNorm hm A ∧
      higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
        2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_continuousLinearMap_source_table
      hm (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv
      invDiagBound hDom hDiagBound hInit hLeft hRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    positive-block-size form of the paired matrix-`∞` source-table endpoint with
    certified active pivot right inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_continuousLinearMap_source_table_of_pivot_right_inverse_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          (higham13_fin_fun_unit_sphere_nonempty hr))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockInfNorm hm A ∧
      higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
        2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_continuousLinearMap_source_table_of_pivot_right_inverse
      hm (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv
      invDiagBound hDom hDiagBound hInit hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    paired matrix-`∞` upper-factor and stage-history bounds from BDD
    all-leading-prefix data plus certified active pivot right inverses.

    This is the endpoint form of the matrix-`∞` BDD bridge: callers supply the
    source BDD/nonsingularity hypotheses and the active pivot right-inverse
    table, while the initial lower table and diagonal comparison are derived
    internally. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockInfNorm hm A ∧
      higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
        2 * blockInfNorm hm A := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hDomPi :
      IsBlockDiagDomCol m
        (fun i j => ‖(fun a b => A i j a b : Fin r → Fin r → ℝ)‖)
        invDiagBound :=
    higham13_blockDiagDomCol_piNorm_of_infNorm hr A invDiagBound hDom
  have hInit :
      ∀ j : Fin m,
        invDiagBound j ≤
          continuousLinearMapLowerNorm
            (matrixMulVecCLM
              (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
            (higham13_fin_fun_unit_sphere_nonempty hr) := by
    let Afn : Fin m → Fin m → Fin r → Fin r → ℝ :=
      fun i j a b => A i j a b
    let pivotFn : ℕ → Fin r → Fin r → ℝ :=
      fun k a b => pivotInv k a b
    have hInitFn :=
      higham13_algorithm13_3_matrix_infNorm_initial_lower_table_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos_of_pos_dim
        hr invDiagBound Afn pivotFn hPrefix hDomPi hBound
    simpa [Afn, pivotFn] using hInitFn
  have hDiagBound :
      ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j) :=
    higham13_algorithm13_3_matrix_infNorm_initial_diag_bound_of_diagBound_nonpos
      A invDiagBound hBound
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_continuousLinearMap_source_table_of_pivot_right_inverse_of_pos_dim
      hm hr A pivotInv invDiagBound hDom hDiagBound hInit hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    paired matrix-`∞` upper-factor and stage-history bounds from BDD data and
    canonical first-Schur-tail pivot inverse data.

    This removes the explicit all-active pivot right-inverse table from the
    paired BDD matrix-`∞` endpoint by deriving it from the initial canonical
    pivot equality and first-tail canonical `nonsingInv` data. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pos_dim
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩)) :
    blockInfNorm (Nat.succ_pos m)
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockInfNorm (Nat.succ_pos m) A ∧
      higham13_algorithm13_3_matrixStageHistoryInfBound
          (Nat.succ_pos m) A pivotInv ≤
        2 * blockInfNorm (Nat.succ_pos m) A := by
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr A pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTailDet
      hTailPivotInv
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
      (Nat.succ_pos m) hr A pivotInv invDiagBound hPrefix hDom hBound
      hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    dimension-aware max-entry/growth-factor package from BDD all-leading-prefix
    data plus certified active pivot right inverses.

    This is the max-entry transfer of the matrix-`∞` BDD source endpoint.  Its
    growth conclusion is the current dependency-strength `ρ <= 2*r`, recording
    the matrix-`∞` to max-entry norm-comparison loss, not the printed
    dimension-free `ρ <= 2` theorem. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 * (r : ℝ) := by
  have hMax : ∀ i j : Fin m,
      infNorm (A i j) ≤ (r : ℝ) * blockMaxNorm hm hr A := by
    intro i j
    exact
      higham13_algorithm13_3_matrix_infNorm_block_le_card_mul_blockMaxNorm
        hm hr A i j
  have hActive :
      ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
        infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
          2 * ((r : ℝ) * blockMaxNorm hm hr A) := by
    intro k i j _hk hik hjk
    exact
      higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
        hr A pivotInv invDiagBound hPrefix hDom hBound hPivotRight
        ((r : ℝ) * blockMaxNorm hm hr A) hMax k i j hik hjk
  exact
    ⟨higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_of_active_stage_bound
        hm hr A pivotInv ((r : ℝ) * blockMaxNorm hm hr A) hActive,
      higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthFactor_le_card_of_active_stage_bound
        hm hr A pivotInv hApos hActive⟩

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    dimension-aware max-entry/growth-factor package from BDD data and canonical
    first-Schur-tail pivot inverse data.

    The conclusion remains the matrix-`∞` transfer endpoint
    `ρ <= 2 * r`; the new content is discharging the all-active pivot
    right-inverse table through the recursive canonical-tail bridge. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pos_dim
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm
      (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩)) :
    blockMaxNorm (Nat.succ_pos m) hr
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm (Nat.succ_pos m) hr A) ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr)
          (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr A pivotInv)
          hApos ≤
        2 * (r : ℝ) := by
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr A pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTailDet
      hTailPivotInv
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
      (Nat.succ_pos m) hr A pivotInv hApos invDiagBound hPrefix hDom hBound
      hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    determinant-nonzero form of the BDD matrix-`∞` max-entry/growth-factor
    package.

    The determinant hypothesis is used only to supply the positive denominator
    for `growthFactorEntry`; the BDD and active pivot right-inverse hypotheses
    remain the source-facing inputs. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_det_ne_zero_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet) ≤
        2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
      hm hr A pivotInv
      (maxEntryNorm_pos_of_det_ne_zero
        (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet)
      invDiagBound hPrefix hDom hBound hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    determinant-nonzero form of the BDD matrix-`∞` canonical-tail
    max-entry/growth-factor package. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_pos_dim
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩)) :
    blockMaxNorm (Nat.succ_pos m) hr
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm (Nat.succ_pos m) hr A) ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr)
          (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A) hdet) ≤
        2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pos_dim
      hr A pivotInv
      (maxEntryNorm_pos_of_det_ne_zero
        (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A) hdet)
      invDiagBound hPrefix hDom hBound hPivot0 hTailDet hTailPivotInv

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    source-facing BDD matrix-`∞` max-entry/growth-factor package from
    all-leading-prefix nonsingularity data and certified active pivot right
    inverses.

    The all-leading-prefix table supplies the full-matrix determinant
    certificate needed only for the positive denominator of `growthFactorEntry`.
    The active-stage bounds still come from the BDD matrix-`∞` source data, so
    the conclusion remains the current dimension-aware `ρ <= 2*r` endpoint. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              hm (fun i j a b => A i j a b) hPrefix)) ≤
        2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_det_ne_zero_of_pos_dim
      hm hr A pivotInv invDiagBound
      (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
        hm (fun i j a b => A i j a b) hPrefix)
      hPrefix hDom hBound hPivotRight

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    matrix-`∞` BDD specialization of the first-Schur-tail recursive
    active pivot-table lift.

    This wrapper transports the source-facing matrix-`∞` BDD hypothesis to the
    finite-function norm expected by the scalar BDD pivot bridge. It discharges
    the stage-zero pivot certificate from `pivotInv 0 = nonsingInv r (A 0 0)`,
    leaving exactly the shifted all-active right-inverse table for the first
    Schur tail as the recursive obligation. -/
theorem
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1))) :
    ∀ k : ℕ, ∀ hk : k < m + 1,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k) := by
  let Afn : Fin (m + 1) → Fin (m + 1) → Fin r → Fin r → ℝ :=
    fun i j a b => A i j a b
  let pivotFn : ℕ → Fin r → Fin r → ℝ :=
    fun k a b => pivotInv k a b
  have hPrefixFn : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 Afn p hp) := by
    intro p hp
    simpa [Afn] using hPrefix p hp
  have hDomPi : IsBlockDiagDomCol (m + 1)
      (fun i j => ‖Afn i j‖) invDiagBound := by
    simpa [Afn] using
      (higham13_blockDiagDomCol_piNorm_of_infNorm hr A invDiagBound hDom)
  have hPivot0Fn :
      pivotFn 0 =
        nonsingInv r (Afn (0 : Fin (m + 1)) (0 : Fin (m + 1))) := by
    simpa [Afn, pivotFn] using hPivot0
  have hTailFn : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur Afn (pivotFn 0)) (fun q => pivotFn (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotFn (k + 1)) := by
    intro k hk
    simpa [Afn, pivotFn] using hTail k hk
  have hPivotRightFn :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
      Afn pivotFn invDiagBound hPrefixFn hDomPi hBound hPivot0Fn hTailFn
  intro k hk
  simpa [Afn, pivotFn] using hPivotRightFn k hk

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    determinant projection of the matrix-`∞` first-Schur-tail recursive
    pivot-table lift. -/
theorem
    higham13_algorithm13_3_pivot_det_ne_zero_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1))) :
    ∀ k : ℕ, ∀ hk : k < m + 1,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0 := by
  exact
    higham13_algorithm13_3_pivot_det_ne_zero_of_pivot_right_inverse A pivotInv
      (higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
        hr A pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTail)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7:
    source-facing matrix-`∞` active column dominance from BDD data and the
    shifted right-inverse table for the first Schur tail.

    Compared with the all-active-pivot endpoint, this derives the original
    stage-zero certificate internally and asks only for the recursive tail
    table. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_active_column_dominance_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pos_dim
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1))) :
    letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
    SchurStageActiveColumnDom13_7
      (fun k i j => infNorm
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv) := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr A pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTail
  exact
    higham13_algorithm13_3_matrix_infNorm_active_column_dominance_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
      hr A pivotInv invDiagBound hPrefix hDom hBound hPivotRight

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    source-facing matrix-`∞` active-stage `2 * max` bound from BDD data and the
    shifted right-inverse table for the first Schur tail. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pos_dim
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1)))
    (normMax : ℝ)
    (hMax : ∀ i j : Fin (m + 1), infNorm (A i j) ≤ normMax)
    (k : ℕ) (i j : Fin (m + 1)) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
      2 * normMax := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr A pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTail
  exact
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
      hr A pivotInv invDiagBound hPrefix hDom hBound hPivotRight
      normMax hMax k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    paired matrix-`∞` upper-factor and stage-history bounds from BDD data and
    the shifted right-inverse table for the first Schur tail. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pos_dim
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1))) :
    blockInfNorm (Nat.succ_pos m)
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockInfNorm (Nat.succ_pos m) A ∧
      higham13_algorithm13_3_matrixStageHistoryInfBound
          (Nat.succ_pos m) A pivotInv ≤
        2 * blockInfNorm (Nat.succ_pos m) A := by
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr A pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTail
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
      (Nat.succ_pos m) hr A pivotInv invDiagBound hPrefix hDom hBound
      hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    dimension-aware max-entry/growth-factor package from BDD data and the
    shifted right-inverse table for the first Schur tail. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pos_dim
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm
      (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1))) :
    blockMaxNorm (Nat.succ_pos m) hr
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm (Nat.succ_pos m) hr A) ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr)
          (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr A pivotInv)
          hApos ≤
        2 * (r : ℝ) := by
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr A pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTail
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
      (Nat.succ_pos m) hr A pivotInv hApos invDiagBound hPrefix hDom hBound
      hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    determinant-nonzero form of the BDD matrix-`∞` first-tail-right-inverse
    max-entry/growth-factor package. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_pos_dim
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1))) :
    blockMaxNorm (Nat.succ_pos m) hr
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm (Nat.succ_pos m) hr A) ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr)
          (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A) hdet) ≤
        2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pos_dim
      hr A pivotInv
      (maxEntryNorm_pos_of_det_ne_zero
        (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A) hdet)
      invDiagBound hPrefix hDom hBound hPivot0 hTail

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    source-facing BDD matrix-`∞` max-entry/growth-factor package from
    all-leading-prefix nonsingularity data and the shifted first-Schur-tail
    right-inverse table. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1))) :
    blockMaxNorm (Nat.succ_pos m) hr
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm (Nat.succ_pos m) hr A) ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr)
          (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos m) (fun i j a b => A i j a b) hPrefix)) ≤
        2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_pos_dim
      hr A pivotInv invDiagBound
      (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
        (Nat.succ_pos m) (fun i j a b => A i j a b) hPrefix)
      hPrefix hDom hBound hPivot0 hTail

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    source-facing BDD matrix-`∞` max-entry/growth-factor package from
    all-leading-prefix nonsingularity data and canonical first-Schur-tail pivot
    inverse data.

    The all-leading-prefix table supplies the full-matrix determinant
    certificate, and the first-tail canonical data supplies the active pivot
    right-inverse table.  The result remains the current dimension-aware
    `ρ <= 2*r` endpoint. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩)) :
    blockMaxNorm (Nat.succ_pos m) hr
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm (Nat.succ_pos m) hr A) ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr)
          (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos m) (fun i j a b => A i j a b) hPrefix)) ≤
        2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_pos_dim
      hr A pivotInv invDiagBound
      (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
        (Nat.succ_pos m) (fun i j a b => A i j a b) hPrefix)
      hPrefix hDom hBound hPivot0 hTailDet hTailPivotInv

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    exact matrix-stage block-LU specification from source-facing matrix-`∞`
    BDD data and the shifted right-inverse table for the first Schur tail.

    This composes the BDD first-tail pivot-table lift with the generic exact
    matrix-stage reconstruction theorem.  It is an exact-arithmetic correctness
    package for Algorithm 13.3 under the same recursive tail obligation used by
    the BDD matrix-`∞` growth endpoints. -/
theorem
    higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1))) :
    BlockLUFactSpec (m + 1) r A
      (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
      (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) := by
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr A pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTail
  exact
    higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_right_inverse
      A pivotInv hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    product-entry reconstruction form of the BDD first-tail right-inverse
    exact matrix-stage block-LU specification. -/
theorem
    higham13_algorithm13_3_matrixStages_product_eq_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1))) :
    ∀ (i j : Fin (m + 1)) (s t : Fin r),
      ∑ k : Fin (m + 1), ∑ l : Fin r,
        higham13_algorithm13_3_lowerFromMatrixStages A pivotInv i k s l *
          higham13_algorithm13_3_upperFromMatrixStages A pivotInv k j l t =
        A i j s t := by
  exact
    (higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr A pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTail).product_eq

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    shifted first-Schur-tail right-inverse data supplies the mixed
    matrix-`∞`/max-entry upper-factor and finite-history growth-factor bounds.

    This is the right-inverse-table analogue of the canonical first-tail
    endpoint: the recursive obligation is the shifted right-inverse table for
    the first Schur tail, not determinant/equality data for canonical
    `nonsingInv` tail pivots. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_mixed_column_mass
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1))) :
    blockMaxNorm (Nat.succ_pos m) hr
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos m) hr A ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr A pivotInv)
          hApos ≤
        2 := by
  have hPivotRight :
      ∀ k : ℕ, ∀ hk : k < m + 1,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k) :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr A pivotInv invDiagBound hPrefix hDomInf hBound hPivot0 hTail
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_mixed_column_mass
      (Nat.succ_pos m) hr A pivotInv hApos invDiagBound hPrefix hDomInf
      hBound hPivotRight

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    determinant-nonzero form of the BDD mixed endpoint with shifted
    first-Schur-tail right-inverse data. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_mixed_column_mass
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1))) :
    blockMaxNorm (Nat.succ_pos m) hr
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos m) hr A ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A) hdet) ≤
        2 := by
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_mixed_column_mass
      hr A pivotInv
      (maxEntryNorm_pos_of_det_ne_zero
        (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A) hdet)
      invDiagBound hPrefix hDomInf hBound hPivot0 hTail

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    source-facing BDD mixed matrix-`∞`/max-entry endpoint with shifted
    first-Schur-tail right-inverse data.

    The all-leading-prefix table supplies the full determinant certificate
    needed for the `growthFactorEntry` denominator; the shifted first-tail table
    remains the recursive pivot obligation. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1))) :
    blockMaxNorm (Nat.succ_pos m) hr
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockMaxNorm (Nat.succ_pos m) hr A ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              (Nat.succ_pos m) (fun i j a b => A i j a b) hPrefix)) ≤
        2 := by
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_mixed_column_mass
      hr A pivotInv invDiagBound
      (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
        (Nat.succ_pos m) (fun i j a b => A i j a b) hPrefix)
      hPrefix hDomInf hBound hPivot0 hTail

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    exact matrix-stage block-LU specification from source-facing matrix-`∞`
    BDD data and canonical first-Schur-tail pivot inverse data.

    This is the canonical-tail companion to the shifted-right-inverse wrapper:
    first-tail determinant nonzero facts plus the `nonsingInv` equality table
    supply the recursive tail right-inverse table before exact reconstruction
    is invoked. -/
theorem
    higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩)) :
    BlockLUFactSpec (m + 1) r A
      (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
      (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) := by
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr A pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTailDet
      hTailPivotInv
  exact
    higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_right_inverse
      A pivotInv hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    product-entry reconstruction form of the BDD canonical-tail exact
    matrix-stage block-LU specification. -/
theorem
    higham13_algorithm13_3_matrixStages_product_eq_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩)) :
    ∀ (i j : Fin (m + 1)) (s t : Fin r),
      ∑ k : Fin (m + 1), ∑ l : Fin r,
        higham13_algorithm13_3_lowerFromMatrixStages A pivotInv i k s l *
          higham13_algorithm13_3_upperFromMatrixStages A pivotInv k j l t =
        A i j s t := by
  exact
    (higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr A pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTailDet
      hTailPivotInv).product_eq

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    product-bound witness form of the BDD first-tail right-inverse exact
    matrix-stage reconstruction.

    This packages the assembled `L,U` factors and product bound under the same
    source-facing first-Schur-tail obligation as the BDD matrix-`∞` endpoint. -/
theorem
    higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {C_L C_U : ℝ}
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTail : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv (k + 1)))
    (hId : 1 ≤ C_L)
    (hLower : ∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv j.val i j *
            pivotInv j.val) ≤ C_L)
    (hUpper :
      blockMaxNorm (Nat.succ_pos m) hr
          (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        C_U) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r A L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          C_L * C_U := by
  exact
    higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound
      (Nat.succ_pos m) hr A pivotInv
      (higham13_algorithm13_3_matrixStages_product_eq_of_first_schur_tail_pivot_right_inverse_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
        hr A pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTail)
      hId hLower hUpper

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    product-bound witness form of the BDD canonical-tail exact matrix-stage
    reconstruction.

    First-tail determinant nonzero facts plus the canonical `nonsingInv` table
    supply the recursive active pivot certificates before the generic product
    witness theorem is invoked. -/
theorem
    higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {C_L C_U : ℝ}
    (invDiagBound : Fin (m + 1) → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j : Fin (m + 1) => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin (m + 1), invDiagBound j ≤ 0)
    (hPivot0 : pivotInv 0 =
      nonsingInv r (A (0 : Fin (m + 1)) (0 : Fin (m + 1))))
    (hTailDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
          ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hTailPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv (k + 1) =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k
            ⟨k, hk⟩ ⟨k, hk⟩))
    (hId : 1 ≤ C_L)
    (hLower : ∀ i j : Fin (m + 1), j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv j.val i j *
            pivotInv j.val) ≤ C_L)
    (hUpper :
      blockMaxNorm (Nat.succ_pos m) hr
          (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        C_U) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r A L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L * blockMaxNorm (Nat.succ_pos m) hr U ≤
          C_L * C_U := by
  exact
    higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound
      (Nat.succ_pos m) hr A pivotInv
      (higham13_algorithm13_3_matrixStages_product_eq_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
        hr A pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTailDet
        hTailPivotInv)
      hId hLower hUpper

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    positive-block-size form of the paired matrix-`∞` endpoint from initial
    diagonal reciprocal data and certified active pivot right inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_initial_diag_right_inverse_of_pivot_right_inverse_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockInfNorm hm A ∧
      higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
        2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_initial_diag_right_inverse_of_pivot_right_inverse
      hm (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv
      invDiagBound diagInv hDom hInvBound hDiagRight hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    positive-block-size form of the paired matrix-`∞` endpoint from the
    source-shaped reciprocal initial diagonal table. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_reciprocal_diag_right_inverse_of_pivot_right_inverse_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (diagInv j))⁻¹))
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockInfNorm hm A ∧
      higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
        2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_reciprocal_diag_right_inverse_of_pivot_right_inverse
      hm (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv diagInv
      hDom hDiagRight hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    positive-block-size form of the paired matrix-`∞` endpoint using canonical
    initial diagonal `nonsingInv` blocks and certified active pivot right
    inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_nonsingInv_diag_of_pivot_right_inverse_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hDiagDet : ∀ j : Fin m, Matrix.det (A j j) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (nonsingInv r (A j j)))⁻¹))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockInfNorm hm A ∧
      higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
        2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_nonsingInv_diag_of_pivot_right_inverse
      hm (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv
      hDiagDet hDom hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations (13.21),(13.23):
    positive-block-size form of the paired matrix-`∞` endpoint with canonical
    initial diagonal inverses and canonical active pivot inverses.

    This removes the artificial finite unit-sphere witness from the source-norm
    dependency route.  The theorem remains a matrix-`∞` endpoint; it is not the
    printed dimension-free max-entry growth theorem. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_nonsingInv_diag_of_pivotInv_eq_nonsingInv_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hDiagDet : ∀ j : Fin m, Matrix.det (A j j) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (nonsingInv r (A j j)))⁻¹))
    (hPivotDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv k =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)) :
    blockInfNorm hm (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockInfNorm hm A ∧
      higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
        2 * blockInfNorm hm A := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_nonsingInv_diag_of_pivotInv_eq_nonsingInv
      hm (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv hDiagDet hDom
      hPivotDet hPivotInv

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    dimension-aware max-entry package with canonical initial diagonal inverses
    and canonical active pivot inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_nonsingInv_diag_of_pivotInv_eq_nonsingInv
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (hDiagDet : ∀ j : Fin m, Matrix.det (A j j) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (nonsingInv r (A j j)))⁻¹))
    (hPivotDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv k =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_nonsingInv_diag_of_pivot_right_inverse
      hm hr hunit A pivotInv hApos hDiagDet hDom
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        A pivotInv hPivotDet hPivotInv)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    determinant-nonzero growth-denominator form of the canonical diagonal and
    active-pivot `nonsingInv` matrix-`∞` package. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_nonsingInv_diag_of_pivotInv_eq_nonsingInv_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hDiagDet : ∀ j : Fin m, Matrix.det (A j j) ≠ 0)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (nonsingInv r (A j j)))⁻¹))
    (hPivotDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv k =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet) ≤
        2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_nonsingInv_diag_of_pivot_right_inverse_of_det_ne_zero
      hm hr hunit A pivotInv hDiagDet hdet hDom
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        A pivotInv hPivotDet hPivotInv)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    positive-block-size form of the canonical diagonal and active-pivot
    `nonsingInv` matrix-`∞` package.

    This is the strongest current canonical matrix-`∞` package with the
    artificial finite unit-sphere witness discharged from `0 < r`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_nonsingInv_diag_of_pivotInv_eq_nonsingInv_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (hDiagDet : ∀ j : Fin m, Matrix.det (A j j) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (nonsingInv r (A j j)))⁻¹))
    (hPivotDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv k =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_nonsingInv_diag_of_pivotInv_eq_nonsingInv
      hm hr (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv hApos
      hDiagDet hDom hPivotDet hPivotInv

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    determinant-nonzero positive-block-size form of the canonical diagonal and
    active-pivot `nonsingInv` matrix-`∞` package. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_nonsingInv_diag_of_pivotInv_eq_nonsingInv_of_det_ne_zero_of_pos_dim
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hDiagDet : ∀ j : Fin m, Matrix.det (A j j) ≠ 0)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (nonsingInv r (A j j)))⁻¹))
    (hPivotDet : ∀ k : ℕ, ∀ hk : k < m,
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0)
    (hPivotInv : ∀ k : ℕ, ∀ hk : k < m,
      pivotInv k =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * ((r : ℝ) * blockMaxNorm hm hr A) ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet) ≤
        2 * (r : ℝ) := by
  exact
    higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_nonsingInv_diag_of_pivotInv_eq_nonsingInv_of_det_ne_zero
      hm hr (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv
      hDiagDet hdet hDom hPivotDet hPivotInv

end NumStability
