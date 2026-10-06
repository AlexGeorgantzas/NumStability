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
import NumStability.Algorithms.LinearSystems.LU.BlockLU.RecursiveFactorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Algorithm03
import NumStability.Source.Higham.Chapter13.Problem04.ActiveStageBounds
import NumStability.Source.Higham.Chapter13.Problem04.BlockInverseBounds
import NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauProducts.DiagonalUpdate
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.RecursiveBudgetChains
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis

/-!
# Source.Higham.Chapter13.Problem04.OneStepProducts

This module formalizes the source-facing Chapter 13 statements for
`Problem04.OneStepProducts`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    one-block base case for the recursive full-factor norm lift.

    For a `1 × 1` block matrix, the block LU factors are `L = I` and `U = A`.
    The lower-factor budget follows from the existing right-inverse
    nonvacuity lemma for the exact max-entry condition product, and the
    upper-factor budget follows from the finite matrix-stage growth object
    containing the initial matrix. -/
theorem higham13_eq13_22_exists_blockLUFact_one_norms_from_matrix_stage_history_exact_kappa
    {r : ℕ} (hr : 0 < r)
    (Ablk : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (1 * r) → Fin (1 * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (1 * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : (((1 * r : ℕ) : ℝ) ≤ (n : ℝ))) :
    ∃ L U : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec 1 r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos 0) hr L ≤
          (n : ℝ) *
            (growthFactorEntry (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                (Nat.mul_pos (Nat.succ_pos 0) hr) (Nat.succ_pos 0) hr Ablk pivotInv) hApos) ^ 2 *
            (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
                (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk) *
              maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
                (Nat.mul_pos (Nat.succ_pos 0) hr) Ainv) ∧
        blockMaxNorm (Nat.succ_pos 0) hr U ≤
          growthFactorEntry (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos (Nat.succ_pos 0) hr) (Nat.succ_pos 0) hr Ablk pivotInv) hApos *
          maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
            (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk) := by
  let hm : 0 < 1 := Nat.succ_pos 0
  let hN : 0 < 1 * r := Nat.mul_pos hm hr
  let A0 : Fin (1 * r) → Fin (1 * r) → ℝ := blockMatrixFlatFin Ablk
  let G : Fin (1 * r) → Fin (1 * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv
  let Ainv0 : Fin (1 * r) → Fin (1 * r) → ℝ := Ainv
  let L0 : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ := fun _ _ => idBlock r
  let U0 : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ := Ablk
  have hA_le_G : maxEntryNorm hN A0 ≤ maxEntryNorm hN G := by
    simpa [hN, hm, A0, G] using
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_flat_initial
        hm hr Ablk pivotInv
  have hBudget :
      1 ≤ (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 *
        (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv0) := by
    exact
      higham13_eq13_22_lower_diagonal_budget_from_right_inverse_growth
        hN A0 G Ainv0 hApos (by simpa [A0, Ainv0] using hRight)
        n hNn hA_le_G
  have hLnorm_one : blockMaxNorm hm hr L0 ≤ 1 := by
    apply blockMaxNorm_le_of_entry_abs_le
    intro i j s t
    fin_cases i
    fin_cases j
    by_cases hst : s = t
    · simp [L0, idBlock, hst]
    · simp [L0, idBlock, hst]
  have hLnorm :
      blockMaxNorm hm hr L0 ≤
        (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 *
          (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv0) :=
    le_trans hLnorm_one hBudget
  have hU_le_G : blockMaxNorm hm hr U0 ≤ maxEntryNorm hN G := by
    rw [← maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm hm hr U0]
    simpa [A0, G, U0] using hA_le_G
  have hUnorm :
      blockMaxNorm hm hr U0 ≤
        growthFactorEntry hN A0 G hApos * maxEntryNormRect hN hN A0 :=
    blockMaxNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm
      hN hm hr A0 G U0 hApos hU_le_G
  have hLU : BlockLUFactSpec 1 r Ablk L0 U0 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      simp [L0]
    · intro i j hij
      fin_cases i
      fin_cases j
      omega
    · intro i j hij
      fin_cases i
      fin_cases j
      omega
    · intro i j s t
      fin_cases i
      fin_cases j
      simp [L0, U0, idBlock]
  refine ⟨L0, U0, hLU, ?_, ?_⟩
  · simpa [hN, hm, A0, G, Ainv0, L0] using hLnorm
  · simpa [hN, hm, A0, G, U0] using hUnorm

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    one-block base case for the recursive full-factor product lift. -/
theorem higham13_eq13_22_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa
    {r : ℕ} (hr : 0 < r)
    (Ablk : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (1 * r) → Fin (1 * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (1 * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : (((1 * r : ℕ) : ℝ) ≤ (n : ℝ))) :
    ∃ L U : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec 1 r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos 0) hr L *
          blockMaxNorm (Nat.succ_pos 0) hr U ≤
            (n : ℝ) *
              (growthFactorEntry (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk)
                (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                  (Nat.mul_pos (Nat.succ_pos 0) hr) (Nat.succ_pos 0) hr Ablk pivotInv) hApos) ^ 3 *
              (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
                  (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk) *
                maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
                  (Nat.mul_pos (Nat.succ_pos 0) hr) Ainv) *
              maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
                (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk) := by
  let hm : 0 < 1 := Nat.succ_pos 0
  let hN : 0 < 1 * r := Nat.mul_pos hm hr
  let A0 : Fin (1 * r) → Fin (1 * r) → ℝ := blockMatrixFlatFin Ablk
  let G : Fin (1 * r) → Fin (1 * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv
  let Ainv0 : Fin (1 * r) → Fin (1 * r) → ℝ := Ainv
  let CL : ℝ :=
    (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 *
      (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv0)
  let CU : ℝ := growthFactorEntry hN A0 G hApos * maxEntryNormRect hN hN A0
  rcases
    higham13_eq13_22_exists_blockLUFact_one_norms_from_matrix_stage_history_exact_kappa
      hr Ablk pivotInv Ainv hApos hRight n hNn with
    ⟨L, U, hLU, hL, hU⟩
  have hCL_nonneg : 0 ≤ CL := by
    exact le_trans (blockMaxNorm_nonneg hm hr L)
      (by simpa [CL, hN, hm, A0, G, Ainv0] using hL)
  have hProd :
      blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤ CL * CU := by
    exact mul_le_mul
      (by simpa [CL, hN, hm, A0, G, Ainv0] using hL)
      (by simpa [CU, hN, hm, A0, G] using hU)
      (blockMaxNorm_nonneg hm hr U)
      hCL_nonneg
  refine ⟨L, U, hLU, ?_⟩
  simpa [CL, CU, hN, hm, A0, G, Ainv0, pow_succ, pow_two,
    mul_assoc, mul_comm, mul_left_comm] using hProd

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    one-block base case for the point-row full-factor product lift. -/
theorem higham13_eq13_23_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa
    {r : ℕ} (hr : 0 < r)
    (Ablk : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (1 * r) → Fin (1 * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (1 * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : (((1 * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hRho_le_two :
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos 0) hr) (Nat.succ_pos 0) hr Ablk pivotInv) hApos ≤ 2) :
    ∃ L U : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec 1 r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos 0) hr L *
          blockMaxNorm (Nat.succ_pos 0) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
                  (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk) *
                maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
                  (Nat.mul_pos (Nat.succ_pos 0) hr) Ainv) *
              maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
                (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk) := by
  let hm : 0 < 1 := Nat.succ_pos 0
  let hN : 0 < 1 * r := Nat.mul_pos hm hr
  let A0 : Fin (1 * r) → Fin (1 * r) → ℝ := blockMatrixFlatFin Ablk
  let G : Fin (1 * r) → Fin (1 * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv
  let Ainv0 : Fin (1 * r) → Fin (1 * r) → ℝ := Ainv
  let rho : ℝ := growthFactorEntry hN A0 G hApos
  let kappaA : ℝ := maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv0
  let Anorm : ℝ := maxEntryNormRect hN hN A0
  rcases
    higham13_eq13_22_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa
      hr Ablk pivotInv Ainv hApos hRight n hNn with
    ⟨L, U, hLU, hProd22⟩
  have hrho_nonneg : 0 ≤ rho := by
    simpa [rho, hN, hm, A0, G] using growthFactorEntry_nonneg hN A0 G hApos
  have hkappa_nonneg : 0 ≤ kappaA := by
    exact mul_nonneg (maxEntryNormRect_nonneg hN hN A0)
      (maxEntryNormRect_nonneg hN hN Ainv0)
  have hAnorm_nonneg : 0 ≤ Anorm := by
    exact maxEntryNormRect_nonneg hN hN A0
  have hrho3 : rho ^ 3 ≤ 8 := by
    have hpow : rho ^ 3 ≤ (2 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hrho_nonneg (by simpa [rho, hN, hm, A0, G] using hRho_le_two) 3
    norm_num at hpow
    exact hpow
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcoef_left : (n : ℝ) * rho ^ 3 ≤ (n : ℝ) * 8 :=
    mul_le_mul_of_nonneg_left hrho3 hn
  have hcoef : (n : ℝ) * rho ^ 3 * kappaA ≤ (n : ℝ) * 8 * kappaA :=
    mul_le_mul_of_nonneg_right hcoef_left hkappa_nonneg
  have hbound :
      (n : ℝ) * rho ^ 3 * kappaA * Anorm ≤
        (n : ℝ) * 8 * kappaA * Anorm :=
    mul_le_mul_of_nonneg_right hcoef hAnorm_nonneg
  refine ⟨L, U, hLU, ?_⟩
  calc
    blockMaxNorm hm hr L * blockMaxNorm hm hr U
        ≤ (n : ℝ) * rho ^ 3 * kappaA * Anorm := by
          simpa [rho, kappaA, Anorm, hN, hm, A0, G, Ainv0] using hProd22
    _ ≤ (n : ℝ) * 8 * kappaA * Anorm := hbound
    _ = 8 * (n : ℝ) * kappaA * Anorm := by ring

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    one-block point-row product witness with `rho <= 2` supplied by the
    matrix-stage product-bound/diagonal-update BDD route. -/
theorem
    higham13_eq13_23_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa_of_product_bound_diag_update
    {r : ℕ} (hr : 0 < r)
    (Ablk : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (1 * r) → Fin (1 * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (1 * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : (((1 * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (invDiagBound : Fin 1 → ℝ)
    (stageInvDiagBound : ℕ → Fin 1 → ℝ)
    (hDom : IsBlockDiagDomCol 1
      (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin 1, invDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hInitInv : ∀ j : Fin 1, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < 1,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < 1, ∀ i j : Fin 1,
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
    ∃ L U : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec 1 r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos 0) hr L *
          blockMaxNorm (Nat.succ_pos 0) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
                  (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk) *
                maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
                  (Nat.mul_pos (Nat.succ_pos 0) hr) Ainv) *
              maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
                (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk) := by
  let hm : 0 < 1 := Nat.succ_pos 0
  let hN : 0 < 1 * r := Nat.mul_pos hm hr
  let A0 : Fin (1 * r) → Fin (1 * r) → ℝ := blockMatrixFlatFin Ablk
  let G : Fin (1 * r) → Fin (1 * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv
  have hRho_le_two :
      growthFactorEntry hN A0 G hApos ≤ 2 := by
    simpa [hm, hN, A0, G] using
      higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hm hr Ablk pivotInv hApos invDiagBound stageInvDiagBound
        hDom hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate
  simpa [hm, hN, A0, G] using
    higham13_eq13_23_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa
      hr Ablk pivotInv Ainv hApos hRight n hNn hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table form of the one-block product/update point-row witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal
    {r : ℕ} (hr : 0 < r)
    (Ablk : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (1 * r) → Fin (1 * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (1 * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : (((1 * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (invDiagBound : Fin 1 → ℝ)
    (stageInvDiagBound : ℕ → Fin 1 → ℝ)
    (hDom : IsBlockDiagDomCol 1
      (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin 1, invDiagBound j ≤ maxEntryNorm hr (Ablk j j))
    (hInitInv : ∀ j : Fin 1, stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < 1, ∀ i j : Fin 1,
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
    ∃ L U : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec 1 r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos 0) hr L *
          blockMaxNorm (Nat.succ_pos 0) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
                  (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk) *
                maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
                  (Nat.mul_pos (Nat.succ_pos 0) hr) Ainv) *
              maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
                (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa_of_product_bound_diag_update
      hr Ablk pivotInv Ainv hApos hRight n hNn invDiagBound stageInvDiagBound
      hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero one-block separate-budget witness.

    This is the source-facing canonical-inverse variant of
    `higham13_eq13_22_exists_blockLUFact_one_norms_from_matrix_stage_history_exact_kappa`:
    the positive growth denominator and `nonsingInv` right-inverse certificate
    are both derived from `det(blockMatrixFlatFin Ablk) != 0`. -/
theorem
    higham13_eq13_22_exists_blockLUFact_one_norms_from_matrix_stage_history_exact_kappa_of_det_ne_zero
    {r : ℕ} (hr : 0 < r)
    (Ablk : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (1 * r)) (Fin (1 * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((1 * r : ℕ) : ℝ) ≤ (n : ℝ))) :
    let hN : 0 < 1 * r := Nat.mul_pos (Nat.succ_pos 0) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    ∃ L U : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec 1 r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos 0) hr L ≤
          (n : ℝ) *
            (growthFactorEntry hN (blockMatrixFlatFin Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN (Nat.succ_pos 0) hr Ablk pivotInv) hApos) ^ 2 *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (1 * r) (blockMatrixFlatFin Ablk))) ∧
        blockMaxNorm (Nat.succ_pos 0) hr U ≤
          growthFactorEntry hN (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos 0) hr Ablk pivotInv) hApos *
          maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  let hN : 0 < 1 * r := Nat.mul_pos (Nat.succ_pos 0) hr
  let A0 : Fin (1 * r) → Fin (1 * r) → ℝ := blockMatrixFlatFin Ablk
  let hApos : 0 < maxEntryNorm hN A0 :=
    maxEntryNorm_pos_of_det_ne_zero hN A0 hdet
  have hRight : IsRightInverse (1 * r) A0 (nonsingInv (1 * r) A0) :=
    (isInverse_nonsingInv_of_det_ne_zero (1 * r) A0 hdet).2
  simpa [hN, A0, hApos] using
    higham13_eq13_22_exists_blockLUFact_one_norms_from_matrix_stage_history_exact_kappa
      hr Ablk pivotInv (nonsingInv (1 * r) A0) hApos hRight n hNn

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero one-block product witness. -/
theorem
    higham13_eq13_22_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa_of_det_ne_zero
    {r : ℕ} (hr : 0 < r)
    (Ablk : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (1 * r)) (Fin (1 * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((1 * r : ℕ) : ℝ) ≤ (n : ℝ))) :
    let hN : 0 < 1 * r := Nat.mul_pos (Nat.succ_pos 0) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    ∃ L U : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec 1 r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos 0) hr L *
          blockMaxNorm (Nat.succ_pos 0) hr U ≤
            (n : ℝ) *
              (growthFactorEntry hN (blockMatrixFlatFin Ablk)
                (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                  hN (Nat.succ_pos 0) hr Ablk pivotInv) hApos) ^ 3 *
              (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
                maxEntryNormRect hN hN
                  (nonsingInv (1 * r) (blockMatrixFlatFin Ablk))) *
              maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  let hN : 0 < 1 * r := Nat.mul_pos (Nat.succ_pos 0) hr
  let A0 : Fin (1 * r) → Fin (1 * r) → ℝ := blockMatrixFlatFin Ablk
  let hApos : 0 < maxEntryNorm hN A0 :=
    maxEntryNorm_pos_of_det_ne_zero hN A0 hdet
  have hRight : IsRightInverse (1 * r) A0 (nonsingInv (1 * r) A0) :=
    (isInverse_nonsingInv_of_det_ne_zero (1 * r) A0 hdet).2
  simpa [hN, A0, hApos] using
    higham13_eq13_22_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa
      hr Ablk pivotInv (nonsingInv (1 * r) A0) hApos hRight n hNn

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero one-block point-row product witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa_of_det_ne_zero
    {r : ℕ} (hr : 0 < r)
    (Ablk : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (1 * r)) (Fin (1 * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((1 * r : ℕ) : ℝ) ≤ (n : ℝ))) :
    let hN : 0 < 1 * r := Nat.mul_pos (Nat.succ_pos 0) hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    growthFactorEntry hN (blockMatrixFlatFin Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos 0) hr Ablk pivotInv) hApos ≤ 2 →
      ∃ L U : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec 1 r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos 0) hr L *
            blockMaxNorm (Nat.succ_pos 0) hr U ≤
              8 * (n : ℝ) *
                (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
                  maxEntryNormRect hN hN
                    (nonsingInv (1 * r) (blockMatrixFlatFin Ablk))) *
                maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hRho_le_two
  let hN : 0 < 1 * r := Nat.mul_pos (Nat.succ_pos 0) hr
  let A0 : Fin (1 * r) → Fin (1 * r) → ℝ := blockMatrixFlatFin Ablk
  let hApos : 0 < maxEntryNorm hN A0 :=
    maxEntryNorm_pos_of_det_ne_zero hN A0 hdet
  have hRight : IsRightInverse (1 * r) A0 (nonsingInv (1 * r) A0) :=
    (isInverse_nonsingInv_of_det_ne_zero (1 * r) A0 hdet).2
  simpa [hN, A0, hApos] using
    higham13_eq13_23_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa
      hr Ablk pivotInv (nonsingInv (1 * r) A0) hApos hRight n hNn hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero one-block point-row product witness with `rho <= 2`
    supplied by the matrix-stage product-bound/diagonal-update BDD route. -/
theorem
    higham13_eq13_23_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
    {r : ℕ} (hr : 0 < r)
    (Ablk : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (1 * r)) (Fin (1 * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((1 * r : ℕ) : ℝ) ≤ (n : ℝ))) :
    let hN : 0 < 1 * r := Nat.mul_pos (Nat.succ_pos 0) hr
    (invDiagBound : Fin 1 → ℝ) →
    (stageInvDiagBound : ℕ → Fin 1 → ℝ) →
    IsBlockDiagDomCol 1
      (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin 1, invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin 1, stageInvDiagBound 0 j = invDiagBound j) →
    (∀ k : ℕ, ∀ hk : k < 1,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1) →
    (∀ k : ℕ, ∀ hk : k < 1, ∀ i j : Fin 1,
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
      ∃ L U : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec 1 r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos 0) hr L *
            blockMaxNorm (Nat.succ_pos 0) hr U ≤
              8 * (n : ℝ) *
                (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
                  maxEntryNormRect hN hN
                    (nonsingInv (1 * r) (blockMatrixFlatFin Ablk))) *
                maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hPivotInvBound hProduct hDiagUpdate
  let hN : 0 < 1 * r := Nat.mul_pos (Nat.succ_pos 0) hr
  let A0 : Fin (1 * r) → Fin (1 * r) → ℝ := blockMatrixFlatFin Ablk
  let hApos : 0 < maxEntryNorm hN A0 :=
    maxEntryNorm_pos_of_det_ne_zero hN A0 hdet
  have hRight : IsRightInverse (1 * r) A0 (nonsingInv (1 * r) A0) :=
    (isInverse_nonsingInv_of_det_ne_zero (1 * r) A0 hdet).2
  simpa [hN, A0, hApos] using
    higham13_eq13_23_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa_of_product_bound_diag_update
      hr Ablk pivotInv (nonsingInv (1 * r) A0) hApos hRight n hNn
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hPivotInvBound hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table determinant-nonzero one-block product/update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_ne_zero
    {r : ℕ} (hr : 0 < r)
    (Ablk : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (1 * r)) (Fin (1 * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((1 * r : ℕ) : ℝ) ≤ (n : ℝ))) :
    let hN : 0 < 1 * r := Nat.mul_pos (Nat.succ_pos 0) hr
    (invDiagBound : Fin 1 → ℝ) →
    (stageInvDiagBound : ℕ → Fin 1 → ℝ) →
    IsBlockDiagDomCol 1
      (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound →
    (∀ j : Fin 1, invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
    (∀ j : Fin 1, stageInvDiagBound 0 j = invDiagBound j) →
    SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) →
    (∀ k : ℕ, ∀ hk : k < 1, ∀ i j : Fin 1,
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
      ∃ L U : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec 1 r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos 0) hr L *
            blockMaxNorm (Nat.succ_pos 0) hr U ≤
              8 * (n : ℝ) *
                (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
                  maxEntryNormRect hN hN
                    (nonsingInv (1 * r) (blockMatrixFlatFin Ablk))) *
                maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hReciprocal hProduct hDiagUpdate
  exact
    higham13_eq13_23_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
      hr Ablk pivotInv hdet n hNn invDiagBound stageInvDiagBound
      hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    one-step full-factor product lift from the source-faithful first split.

    If the recursive Schur-tail factors already satisfy the Eq.13.22 lower and
    upper budgets, then the explicit one-step factors
    `blockLUOneStepL` and `blockLUOneStepU` satisfy the displayed
    `n ρ^3 κ(A) ‖A‖` product bound.  This is the structural induction step for
    the still-open recursive/full-factor Eq.13.22 theorem. -/
theorem higham13_eq13_22_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hN : 0 < r + m * r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
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
      IsRightInverse (r + m * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat Ablk)))
    (n : ℕ)
    (hsn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (L_S U_S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hTailL :
      blockMaxNorm hm hr L_S ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + m * r)
              (blockMatrixFirstSplitFlat Ablk))))
    (hTailU :
      blockMaxNorm hm hr U_S ≤
        growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    blockMaxNorm (Nat.succ_pos m) hr
        (blockLUOneStepL Ablk (pivotInv 0) L_S) *
      blockMaxNorm (Nat.succ_pos m) hr (blockLUOneStepU Ablk U_S) ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 3 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + m * r)
              (blockMatrixFirstSplitFlat Ablk))) *
          maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  letI hA11Inv : Invertible (blockMatrixFirstSplitA11 Ablk) := inferInstance
  let A0 : Fin (r + m * r) → Fin (r + m * r) → ℝ :=
    blockMatrixFirstSplitFlat Ablk
  let G : Fin (r + m * r) → Fin (r + m * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      hN (Nat.succ_pos m) hr Ablk pivotInv
  let Ainv : Fin (r + m * r) → Fin (r + m * r) → ℝ :=
    nonsingInv (r + m * r) A0
  let rho : ℝ := growthFactorEntry hN A0 G hApos
  let kappaA : ℝ := maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv
  let Anorm : ℝ := maxEntryNormRect hN hN A0
  let A11_inv : Matrix (Fin r) (Fin r) ℝ := pivotInv 0
  have hA_le_G : maxEntryNorm hN A0 ≤ maxEntryNorm hN G := by
    exact le_trans
      (by
        simpa [A0] using
          maxEntryNorm_blockMatrixFirstSplitFlat_le_blockMaxNorm_of_hN hN hm hr Ablk)
      (by
        simpa [G] using
          higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
            hN (Nat.succ_pos m) hr Ablk pivotInv)
  have hId : 1 ≤ (n : ℝ) * rho ^ 2 * kappaA := by
    simpa [A0, G, Ainv, rho, kappaA] using
      higham13_eq13_22_lower_diagonal_budget_from_right_inverse_growth
        hN A0 G Ainv hApos (by simpa [A0, Ainv] using hRight)
        n hNn hA_le_G
  have hL21 :
      maxEntryNormRect (Nat.mul_pos hm hr) hr
          ((blockMatrixFirstSplitA21 Ablk * A11_inv :
            Matrix (Fin (m * r)) (Fin r) ℝ)) ≤
        (n : ℝ) * rho ^ 2 * kappaA := by
    simpa [A0, G, Ainv, rho, kappaA, A11_inv, hpivot] using
      higham13_problem13_4_L21_eq13_22_premise_from_matrix_stage_history_first_split_exact_kappa
        hm hr hN Ablk pivotInv hpivot hApos n hsn
  have hFirstRow :
      ∀ j : Fin (m + 1), maxEntryNorm hr (Ablk 0 j) ≤ rho * Anorm := by
    have hInput :
        blockMaxNorm (Nat.succ_pos m) hr Ablk ≤ rho * Anorm := by
      simpa [A0, G, rho, Anorm] using
        blockMaxNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm
          hN (Nat.succ_pos m) hr A0 G Ablk hApos
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
            hN (Nat.succ_pos m) hr Ablk pivotInv)
    intro j
    exact le_trans
      (block_le_blockMaxNorm (Nat.succ_pos m) hr Ablk 0 j)
      hInput
  have hProd :=
    blockLUOneStep_blockMaxNorm_product_le_of_firstSplit_tail
      hm hr Ablk A11_inv L_S U_S
      hId hL21
      (by simpa [A0, G, Ainv, rho, kappaA] using hTailL)
      hFirstRow
      (by simpa [A0, G, rho, Anorm] using hTailU)
  simpa [A0, G, Ainv, rho, kappaA, Anorm, A11_inv, pow_succ, pow_two,
    mul_assoc, mul_comm, mul_left_comm] using hProd

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    one-step preservation of the separate lower and upper factor budgets from
    the source-faithful first split.

    This is the induction-strength form of the one-step product lift: if the
    Schur-tail factors already satisfy the recursive lower and upper budgets,
    then the explicit factors `blockLUOneStepL` and `blockLUOneStepU` satisfy
    those same budgets for the full first split. -/
theorem higham13_eq13_22_blockLUOneStep_norms_from_matrix_stage_history_first_split_tail_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hN : 0 < r + m * r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
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
      IsRightInverse (r + m * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat Ablk)))
    (n : ℕ)
    (hsn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (L_S U_S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hTailL :
      blockMaxNorm hm hr L_S ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + m * r)
              (blockMatrixFirstSplitFlat Ablk))))
    (hTailU :
      blockMaxNorm hm hr U_S ≤
        growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    blockMaxNorm (Nat.succ_pos m) hr
        (blockLUOneStepL Ablk (pivotInv 0) L_S) ≤
          (n : ℝ) *
            (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 2 *
            (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
              maxEntryNormRect hN hN (nonsingInv (r + m * r)
                (blockMatrixFirstSplitFlat Ablk))) ∧
      blockMaxNorm (Nat.succ_pos m) hr (blockLUOneStepU Ablk U_S) ≤
        growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  letI hA11Inv : Invertible (blockMatrixFirstSplitA11 Ablk) := inferInstance
  let A0 : Fin (r + m * r) → Fin (r + m * r) → ℝ :=
    blockMatrixFirstSplitFlat Ablk
  let G : Fin (r + m * r) → Fin (r + m * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      hN (Nat.succ_pos m) hr Ablk pivotInv
  let Ainv : Fin (r + m * r) → Fin (r + m * r) → ℝ :=
    nonsingInv (r + m * r) A0
  let rho : ℝ := growthFactorEntry hN A0 G hApos
  let kappaA : ℝ := maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv
  let Anorm : ℝ := maxEntryNormRect hN hN A0
  let A11_inv : Matrix (Fin r) (Fin r) ℝ := pivotInv 0
  have hA_le_G : maxEntryNorm hN A0 ≤ maxEntryNorm hN G := by
    exact le_trans
      (by
        simpa [A0] using
          maxEntryNorm_blockMatrixFirstSplitFlat_le_blockMaxNorm_of_hN hN hm hr Ablk)
      (by
        simpa [G] using
          higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
            hN (Nat.succ_pos m) hr Ablk pivotInv)
  have hId : 1 ≤ (n : ℝ) * rho ^ 2 * kappaA := by
    simpa [A0, G, Ainv, rho, kappaA] using
      higham13_eq13_22_lower_diagonal_budget_from_right_inverse_growth
        hN A0 G Ainv hApos (by simpa [A0, Ainv] using hRight)
        n hNn hA_le_G
  have hL21 :
      maxEntryNormRect (Nat.mul_pos hm hr) hr
          ((blockMatrixFirstSplitA21 Ablk * A11_inv :
            Matrix (Fin (m * r)) (Fin r) ℝ)) ≤
        (n : ℝ) * rho ^ 2 * kappaA := by
    simpa [A0, G, Ainv, rho, kappaA, A11_inv, hpivot] using
      higham13_problem13_4_L21_eq13_22_premise_from_matrix_stage_history_first_split_exact_kappa
        hm hr hN Ablk pivotInv hpivot hApos n hsn
  have hFirstRow :
      ∀ j : Fin (m + 1), maxEntryNorm hr (Ablk 0 j) ≤ rho * Anorm := by
    have hInput :
        blockMaxNorm (Nat.succ_pos m) hr Ablk ≤ rho * Anorm := by
      simpa [A0, G, rho, Anorm] using
        blockMaxNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm
          hN (Nat.succ_pos m) hr A0 G Ablk hApos
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
            hN (Nat.succ_pos m) hr Ablk pivotInv)
    intro j
    exact le_trans
      (block_le_blockMaxNorm (Nat.succ_pos m) hr Ablk 0 j)
      hInput
  constructor
  · have hL :=
      blockLUOneStepL_blockMaxNorm_le_of_firstSplit_tail
        hm hr Ablk A11_inv L_S hId hL21
        (by simpa [A0, G, Ainv, rho, kappaA] using hTailL)
    simpa [A0, G, Ainv, rho, kappaA, A11_inv] using hL
  · have hU :=
      blockLUOneStepU_blockMaxNorm_le_of_firstRow_tail
        hm hr Ablk U_S hFirstRow
        (by simpa [A0, G, rho, Anorm] using hTailU)
    simpa [A0, G, rho, Anorm] using hU

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    one-step full-factor witness theorem with separate recursive budgets.

    This packages
    `higham13_eq13_22_blockLUOneStep_norms_from_matrix_stage_history_first_split_tail_exact_kappa`
    with `block_lu_one_step_explicit`: under a Schur-tail factorization and
    tail lower/upper budgets, the explicit one-step factors factor `A` and
    satisfy the separate lower and upper budgets needed for recursive
    induction. -/
theorem higham13_eq13_22_exists_blockLUOneStep_fact_norms_from_matrix_stage_history_first_split_tail_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hN : 0 < r + m * r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
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
      IsRightInverse (r + m * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat Ablk)))
    (n : ℕ)
    (hsn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (L_S U_S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hTailFact : BlockLUFactSpec m r (blockSchur Ablk (pivotInv 0)) L_S U_S)
    (hTailL :
      blockMaxNorm hm hr L_S ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + m * r)
              (blockMatrixFirstSplitFlat Ablk))))
    (hTailU :
      blockMaxNorm hm hr U_S ≤
        growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L ≤
          (n : ℝ) *
            (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 2 *
            (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
              maxEntryNormRect hN hN (nonsingInv (r + m * r)
                (blockMatrixFirstSplitFlat Ablk))) ∧
        blockMaxNorm (Nat.succ_pos m) hr U ≤
          growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
          maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  letI hA11Inv : Invertible (blockMatrixFirstSplitA11 Ablk) := inferInstance
  let A11_inv : Matrix (Fin r) (Fin r) ℝ := pivotInv 0
  have hInvLeft :
      ∀ s t : Fin r,
        ∑ l : Fin r, A11_inv s l * Ablk 0 0 l t = if s = t then 1 else 0 := by
    intro s t
    have hA11_inv :
        A11_inv = ⅟(blockMatrixFirstSplitA11 Ablk) := by
      simpa [A11_inv] using hpivot
    have hmul :
        ((A11_inv * blockMatrixFirstSplitA11 Ablk) :
          Matrix (Fin r) (Fin r) ℝ) s t =
          (1 : Matrix (Fin r) (Fin r) ℝ) s t := by
      rw [hA11_inv]
      exact congr_fun
        (congr_fun (invOf_mul_self (blockMatrixFirstSplitA11 Ablk)) s) t
    simpa [Matrix.mul_apply, blockMatrixFirstSplitA11] using hmul
  let L := blockLUOneStepL Ablk (pivotInv 0) L_S
  let U := blockLUOneStepU Ablk U_S
  have hBounds :=
    higham13_eq13_22_blockLUOneStep_norms_from_matrix_stage_history_first_split_tail_exact_kappa
      hm hr hN Ablk pivotInv hpivot hApos hRight n hsn hNn L_S U_S hTailL hTailU
  refine ⟨L, U, ?_, ?_, ?_⟩
  · simpa [L, U, A11_inv] using
      block_lu_one_step_explicit Ablk A11_inv hInvLeft L_S U_S
        (by simpa [A11_inv] using hTailFact)
  · simpa [L, U] using hBounds.1
  · simpa [L, U] using hBounds.2

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    existential-tail successor step for the recursive full-factor norm lift.

    This is the induction-step surface paired with the one-block base case:
    if the Schur tail already has a `BlockLUFactSpec` witness satisfying the
    recursive lower and upper budgets, then the successor matrix has a witness
    satisfying the same source-facing budgets. -/
theorem higham13_eq13_22_exists_blockLUFact_succ_norms_from_tail_witness_matrix_stage_history_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hN : 0 < r + m * r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
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
      IsRightInverse (r + m * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat Ablk)))
    (n : ℕ)
    (hsn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hTail :
      ∃ L_S U_S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec m r (blockSchur Ablk (pivotInv 0)) L_S U_S ∧
          blockMaxNorm hm hr L_S ≤
            (n : ℝ) *
              (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
                (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                  hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 2 *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + m * r)
                  (blockMatrixFirstSplitFlat Ablk))) ∧
          blockMaxNorm hm hr U_S ≤
            growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
            maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L ≤
          (n : ℝ) *
            (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 2 *
            (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
              maxEntryNormRect hN hN (nonsingInv (r + m * r)
                (blockMatrixFirstSplitFlat Ablk))) ∧
        blockMaxNorm (Nat.succ_pos m) hr U ≤
          growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
          maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  rcases hTail with ⟨L_S, U_S, hTailFact, hTailL, hTailU⟩
  exact
    higham13_eq13_22_exists_blockLUOneStep_fact_norms_from_matrix_stage_history_first_split_tail_exact_kappa
      hm hr hN Ablk pivotInv hpivot hApos hRight n hsn hNn
      L_S U_S hTailFact hTailL hTailU

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    one-step point-row specialization of the source-faithful first split.

    This composes
    `higham13_eq13_22_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa`
    with the source-side hypothesis `rho <= 2`, yielding the displayed
    `8 n kappa(A) ||A||` product bound for the explicit one-step factors. -/
theorem higham13_eq13_23_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hN : 0 < r + m * r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
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
      IsRightInverse (r + m * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat Ablk)))
    (n : ℕ)
    (hsn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hRho_le_two :
      growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos ≤ 2)
    (L_S U_S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hTailL :
      blockMaxNorm hm hr L_S ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + m * r)
              (blockMatrixFirstSplitFlat Ablk))))
    (hTailU :
      blockMaxNorm hm hr U_S ≤
        growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    blockMaxNorm (Nat.succ_pos m) hr
        (blockLUOneStepL Ablk (pivotInv 0) L_S) *
      blockMaxNorm (Nat.succ_pos m) hr (blockLUOneStepU Ablk U_S) ≤
        8 * (n : ℝ) *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + m * r)
              (blockMatrixFirstSplitFlat Ablk))) *
          maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  let A0 : Fin (r + m * r) → Fin (r + m * r) → ℝ :=
    blockMatrixFirstSplitFlat Ablk
  let G : Fin (r + m * r) → Fin (r + m * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      hN (Nat.succ_pos m) hr Ablk pivotInv
  let Ainv : Fin (r + m * r) → Fin (r + m * r) → ℝ :=
    nonsingInv (r + m * r) A0
  let rho : ℝ := growthFactorEntry hN A0 G hApos
  let kappaA : ℝ := maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv
  let Anorm : ℝ := maxEntryNormRect hN hN A0
  have hProd :
      blockMaxNorm (Nat.succ_pos m) hr
          (blockLUOneStepL Ablk (pivotInv 0) L_S) *
        blockMaxNorm (Nat.succ_pos m) hr (blockLUOneStepU Ablk U_S) ≤
          (n : ℝ) * rho ^ 3 * kappaA * Anorm := by
    simpa [A0, G, Ainv, rho, kappaA, Anorm] using
      higham13_eq13_22_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa
        hm hr hN Ablk pivotInv hpivot hApos hRight n hsn hNn L_S U_S
        hTailL hTailU
  have hrho_nonneg : 0 ≤ rho := by
    simpa [A0, G, rho] using growthFactorEntry_nonneg hN A0 G hApos
  have hkappa_nonneg : 0 ≤ kappaA := by
    exact mul_nonneg (maxEntryNormRect_nonneg hN hN A0)
      (maxEntryNormRect_nonneg hN hN Ainv)
  have hAnorm_nonneg : 0 ≤ Anorm := by
    exact maxEntryNormRect_nonneg hN hN A0
  have hrho3 : rho ^ 3 ≤ 8 := by
    have hpow : rho ^ 3 ≤ (2 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hrho_nonneg (by simpa [A0, G, rho] using hRho_le_two) 3
    norm_num at hpow
    exact hpow
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcoef_left : (n : ℝ) * rho ^ 3 ≤ (n : ℝ) * 8 :=
    mul_le_mul_of_nonneg_left hrho3 hn
  have hcoef : (n : ℝ) * rho ^ 3 * kappaA ≤ (n : ℝ) * 8 * kappaA :=
    mul_le_mul_of_nonneg_right hcoef_left hkappa_nonneg
  have hbound :
      (n : ℝ) * rho ^ 3 * kappaA * Anorm ≤
        (n : ℝ) * 8 * kappaA * Anorm :=
    mul_le_mul_of_nonneg_right hcoef hAnorm_nonneg
  calc
    blockMaxNorm (Nat.succ_pos m) hr
          (blockLUOneStepL Ablk (pivotInv 0) L_S) *
        blockMaxNorm (Nat.succ_pos m) hr (blockLUOneStepU Ablk U_S)
        ≤ (n : ℝ) * rho ^ 3 * kappaA * Anorm := hProd
    _ ≤ (n : ℝ) * 8 * kappaA * Anorm := hbound
    _ = 8 * (n : ℝ) * kappaA * Anorm := by ring

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    successor-shaped one-step product bound with `rho <= 2` supplied by the
    first-split product-bound/diagonal-update BDD route. -/
theorem
    higham13_eq13_23_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa_of_product_bound_diag_update
    {m r : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
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
    (n : ℕ)
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
    (L_S U_S : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (hTailL :
      blockMaxNorm (Nat.succ_pos m) hr L_S ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
              (blockMatrixFirstSplitFlat Ablk))))
    (hTailU :
      blockMaxNorm (Nat.succ_pos m) hr U_S ≤
        growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos *
        maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (blockLUOneStepL Ablk (pivotInv 0) L_S) *
      blockMaxNorm (Nat.succ_pos (m + 1)) hr (blockLUOneStepU Ablk U_S) ≤
        8 * (n : ℝ) *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
              (blockMatrixFirstSplitFlat Ablk))) *
          maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  let hmTail : 0 < m + 1 := Nat.succ_pos m
  have hRho_le_two :
      growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos ≤ 2 := by
    exact
      higham13_algorithm13_3_firstSplitStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hr hN Ablk pivotInv hApos invDiagBound stageInvDiagBound hDom
        hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate
  simpa [hmTail] using
    higham13_eq13_23_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa
      hmTail hr hN Ablk pivotInv hpivot hApos hRight n hsn hNn
      hRho_le_two L_S U_S hTailL hTailU

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table form of the successor-shaped one-step product/update
    bound. -/
theorem
    higham13_eq13_23_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa_of_product_bound_diag_update_reciprocal
    {m r : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
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
    (n : ℕ)
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
    (L_S U_S : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (hTailL :
      blockMaxNorm (Nat.succ_pos m) hr L_S ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
              (blockMatrixFirstSplitFlat Ablk))))
    (hTailU :
      blockMaxNorm (Nat.succ_pos m) hr U_S ≤
        growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos *
        maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (blockLUOneStepL Ablk (pivotInv 0) L_S) *
      blockMaxNorm (Nat.succ_pos (m + 1)) hr (blockLUOneStepU Ablk U_S) ≤
        8 * (n : ℝ) *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
              (blockMatrixFirstSplitFlat Ablk))) *
          maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  exact
    higham13_eq13_23_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa_of_product_bound_diag_update
      hr hN Ablk pivotInv hpivot hApos hRight n hsn hNn
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate L_S U_S hTailL hTailU

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero form of the first-split product/update point-row
    product bound.

    This wrapper keeps the source BDD product/update certificate explicit, but
    derives the positive growth denominator and canonical ambient `nonsingInv`
    right-inverse from `det(blockMatrixFirstSplitFlat Ablk) != 0`. -/
theorem
    higham13_eq13_23_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
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
    (L_S U_S : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (hTailL :
      blockMaxNorm (Nat.succ_pos m) hr L_S ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
            (maxEntryNorm_pos_of_det_ne_zero hN
              (blockMatrixFirstSplitFlat Ablk) hdet)) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
              (blockMatrixFirstSplitFlat Ablk))))
    (hTailU :
      blockMaxNorm (Nat.succ_pos m) hr U_S ≤
        growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero hN
            (blockMatrixFirstSplitFlat Ablk) hdet) *
        maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (blockLUOneStepL Ablk (pivotInv 0) L_S) *
      blockMaxNorm (Nat.succ_pos (m + 1)) hr (blockLUOneStepU Ablk U_S) ≤
        8 * (n : ℝ) *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
              (blockMatrixFirstSplitFlat Ablk))) *
          maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  have hRight :
      IsRightInverse (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero (r + (m + 1) * r)
      (blockMatrixFirstSplitFlat Ablk) hdet).2
  simpa using
    higham13_eq13_23_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa_of_product_bound_diag_update
      hr hN Ablk pivotInv hpivot
      (maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFirstSplitFlat Ablk) hdet)
      hRight n hsn hNn invDiagBound stageInvDiagBound hDom hDiagBound
      hInitInv hPivotInvBound hProduct hDiagUpdate L_S U_S hTailL hTailU

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero reciprocal-table form of the first-split
    product/update point-row product bound. -/
theorem
    higham13_eq13_23_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
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
    (L_S U_S : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (hTailL :
      blockMaxNorm (Nat.succ_pos m) hr L_S ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
            (maxEntryNorm_pos_of_det_ne_zero hN
              (blockMatrixFirstSplitFlat Ablk) hdet)) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
              (blockMatrixFirstSplitFlat Ablk))))
    (hTailU :
      blockMaxNorm (Nat.succ_pos m) hr U_S ≤
        growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero hN
            (blockMatrixFirstSplitFlat Ablk) hdet) *
        maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    blockMaxNorm (Nat.succ_pos (m + 1)) hr
        (blockLUOneStepL Ablk (pivotInv 0) L_S) *
      blockMaxNorm (Nat.succ_pos (m + 1)) hr (blockLUOneStepU Ablk U_S) ≤
        8 * (n : ℝ) *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
              (blockMatrixFirstSplitFlat Ablk))) *
          maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  exact
    higham13_eq13_23_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
      hr hN Ablk pivotInv hpivot hdet n hsn hNn
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate L_S U_S hTailL hTailU

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    one-step full-factor witness theorem from the source-faithful first split.

    This combines the explicit block LU construction with
    `higham13_eq13_22_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa`.
    If the Schur-tail factors satisfy `BlockLUFactSpec` and the recursive
    tail norm budgets, the constructed full one-step factors both factor `A`
    and satisfy the displayed `n rho^3 kappa(A) ||A||` product bound. -/
theorem higham13_eq13_22_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hN : 0 < r + m * r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
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
      IsRightInverse (r + m * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat Ablk)))
    (n : ℕ)
    (hsn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (L_S U_S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hTailFact : BlockLUFactSpec m r (blockSchur Ablk (pivotInv 0)) L_S U_S)
    (hTailL :
      blockMaxNorm hm hr L_S ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + m * r)
              (blockMatrixFirstSplitFlat Ablk))))
    (hTailU :
      blockMaxNorm hm hr U_S ≤
        growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L *
          blockMaxNorm (Nat.succ_pos m) hr U ≤
            (n : ℝ) *
              (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
                (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                  hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 3 *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + m * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
              maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  letI hA11Inv : Invertible (blockMatrixFirstSplitA11 Ablk) := inferInstance
  let A11_inv : Matrix (Fin r) (Fin r) ℝ := pivotInv 0
  have hInvLeft :
      ∀ s t : Fin r,
        ∑ l : Fin r, A11_inv s l * Ablk 0 0 l t = if s = t then 1 else 0 := by
    intro s t
    have hA11_inv :
        A11_inv = ⅟(blockMatrixFirstSplitA11 Ablk) := by
      simpa [A11_inv] using hpivot
    have hmul :
        ((A11_inv * blockMatrixFirstSplitA11 Ablk) :
          Matrix (Fin r) (Fin r) ℝ) s t =
          (1 : Matrix (Fin r) (Fin r) ℝ) s t := by
      rw [hA11_inv]
      exact congr_fun
        (congr_fun (invOf_mul_self (blockMatrixFirstSplitA11 Ablk)) s) t
    simpa [Matrix.mul_apply, blockMatrixFirstSplitA11] using hmul
  let L := blockLUOneStepL Ablk (pivotInv 0) L_S
  let U := blockLUOneStepU Ablk U_S
  refine ⟨L, U, ?_, ?_⟩
  · simpa [L, U, A11_inv] using
      block_lu_one_step_explicit Ablk A11_inv hInvLeft L_S U_S
        (by simpa [A11_inv] using hTailFact)
  · simpa [L, U] using
      higham13_eq13_22_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa
        hm hr hN Ablk pivotInv hpivot hApos hRight n hsn hNn L_S U_S
        hTailL hTailU

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    existential-tail successor step for the full-factor product lift.

    This product-bound companion to
    `higham13_eq13_22_exists_blockLUFact_succ_norms_from_tail_witness_matrix_stage_history_exact_kappa`
    packages the one-step Eq.13.22 witness behind an existential Schur-tail
    witness satisfying the separate lower and upper budgets. -/
theorem higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_witness_matrix_stage_history_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hN : 0 < r + m * r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
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
      IsRightInverse (r + m * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat Ablk)))
    (n : ℕ)
    (hsn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hTail :
      ∃ L_S U_S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec m r (blockSchur Ablk (pivotInv 0)) L_S U_S ∧
          blockMaxNorm hm hr L_S ≤
            (n : ℝ) *
              (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
                (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                  hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 2 *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + m * r)
                  (blockMatrixFirstSplitFlat Ablk))) ∧
          blockMaxNorm hm hr U_S ≤
            growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
            maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L *
          blockMaxNorm (Nat.succ_pos m) hr U ≤
            (n : ℝ) *
              (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
                (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                  hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 3 *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + m * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
              maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  rcases hTail with ⟨L_S, U_S, hTailFact, hTailL, hTailU⟩
  exact
    higham13_eq13_22_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa
      hm hr hN Ablk pivotInv hpivot hApos hRight n hsn hNn
      L_S U_S hTailFact hTailL hTailU

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    one-step full-factor witness theorem from the source-faithful first split
    under the point-row growth hypothesis `rho <= 2`.

    This is the Eq.13.23 analogue of
    `higham13_eq13_22_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa`:
    the same explicit one-step factors satisfy `BlockLUFactSpec`, while the
    product bound is specialized to `8 n kappa(A) ||A||`. -/
theorem higham13_eq13_23_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hN : 0 < r + m * r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
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
      IsRightInverse (r + m * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat Ablk)))
    (n : ℕ)
    (hsn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hRho_le_two :
      growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos ≤ 2)
    (L_S U_S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hTailFact : BlockLUFactSpec m r (blockSchur Ablk (pivotInv 0)) L_S U_S)
    (hTailL :
      blockMaxNorm hm hr L_S ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + m * r)
              (blockMatrixFirstSplitFlat Ablk))))
    (hTailU :
      blockMaxNorm hm hr U_S ≤
        growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
        maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L *
          blockMaxNorm (Nat.succ_pos m) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + m * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
              maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  letI hA11Inv : Invertible (blockMatrixFirstSplitA11 Ablk) := inferInstance
  let A11_inv : Matrix (Fin r) (Fin r) ℝ := pivotInv 0
  have hInvLeft :
      ∀ s t : Fin r,
        ∑ l : Fin r, A11_inv s l * Ablk 0 0 l t = if s = t then 1 else 0 := by
    intro s t
    have hA11_inv :
        A11_inv = ⅟(blockMatrixFirstSplitA11 Ablk) := by
      simpa [A11_inv] using hpivot
    have hmul :
        ((A11_inv * blockMatrixFirstSplitA11 Ablk) :
          Matrix (Fin r) (Fin r) ℝ) s t =
          (1 : Matrix (Fin r) (Fin r) ℝ) s t := by
      rw [hA11_inv]
      exact congr_fun
        (congr_fun (invOf_mul_self (blockMatrixFirstSplitA11 Ablk)) s) t
    simpa [Matrix.mul_apply, blockMatrixFirstSplitA11] using hmul
  let L := blockLUOneStepL Ablk (pivotInv 0) L_S
  let U := blockLUOneStepU Ablk U_S
  refine ⟨L, U, ?_, ?_⟩
  · simpa [L, U, A11_inv] using
      block_lu_one_step_explicit Ablk A11_inv hInvLeft L_S U_S
        (by simpa [A11_inv] using hTailFact)
  · simpa [L, U] using
      higham13_eq13_23_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa
        hm hr hN Ablk pivotInv hpivot hApos hRight n hsn hNn hRho_le_two
        L_S U_S hTailL hTailU

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero one-step product lift for the source-faithful first
    split.

    This is the same one-step Eq.13.22 product bound as
    `higham13_eq13_22_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa`,
    but derives the positive growth denominator and canonical ambient
    `nonsingInv` right-inverse from
    `det(blockMatrixFirstSplitFlat Ablk) != 0`. -/
theorem
    higham13_eq13_22_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hN : 0 < r + m * r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
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
        Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (L_S U_S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hTailL :
      blockMaxNorm hm hr L_S ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos m) hr Ablk pivotInv)
            (maxEntryNorm_pos_of_det_ne_zero hN
              (blockMatrixFirstSplitFlat Ablk) hdet)) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + m * r)
              (blockMatrixFirstSplitFlat Ablk))))
    (hTailU :
      blockMaxNorm hm hr U_S ≤
        growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero hN
            (blockMatrixFirstSplitFlat Ablk) hdet) *
        maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    blockMaxNorm (Nat.succ_pos m) hr
        (blockLUOneStepL Ablk (pivotInv 0) L_S) *
      blockMaxNorm (Nat.succ_pos m) hr (blockLUOneStepU Ablk U_S) ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos m) hr Ablk pivotInv)
            (maxEntryNorm_pos_of_det_ne_zero hN
              (blockMatrixFirstSplitFlat Ablk) hdet)) ^ 3 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + m * r)
              (blockMatrixFirstSplitFlat Ablk))) *
          maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  have hRight :
      IsRightInverse (r + m * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero (r + m * r)
      (blockMatrixFirstSplitFlat Ablk) hdet).2
  simpa using
    higham13_eq13_22_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa
      hm hr hN Ablk pivotInv hpivot
      (maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFirstSplitFlat Ablk) hdet)
      hRight n hsn hNn L_S U_S hTailL hTailU

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero one-step point-row product lift for the source-faithful
    first split.

    The `rho <= 2` side condition is still explicit, but is stated for the
    determinant-derived growth denominator. -/
theorem
    higham13_eq13_23_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hN : 0 < r + m * r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
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
        Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hRho_le_two :
      growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero hN
            (blockMatrixFirstSplitFlat Ablk) hdet) ≤ 2)
    (L_S U_S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hTailL :
      blockMaxNorm hm hr L_S ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos m) hr Ablk pivotInv)
            (maxEntryNorm_pos_of_det_ne_zero hN
              (blockMatrixFirstSplitFlat Ablk) hdet)) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + m * r)
              (blockMatrixFirstSplitFlat Ablk))))
    (hTailU :
      blockMaxNorm hm hr U_S ≤
        growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero hN
            (blockMatrixFirstSplitFlat Ablk) hdet) *
        maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    blockMaxNorm (Nat.succ_pos m) hr
        (blockLUOneStepL Ablk (pivotInv 0) L_S) *
      blockMaxNorm (Nat.succ_pos m) hr (blockLUOneStepU Ablk U_S) ≤
        8 * (n : ℝ) *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + m * r)
              (blockMatrixFirstSplitFlat Ablk))) *
          maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  have hRight :
      IsRightInverse (r + m * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero (r + m * r)
      (blockMatrixFirstSplitFlat Ablk) hdet).2
  simpa using
    higham13_eq13_23_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa
      hm hr hN Ablk pivotInv hpivot
      (maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFirstSplitFlat Ablk) hdet)
      hRight n hsn hNn hRho_le_two L_S U_S hTailL hTailU

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero one-step `BlockLUFactSpec` product witness for the
    source-faithful first split. -/
theorem
    higham13_eq13_22_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hN : 0 < r + m * r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
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
        Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (L_S U_S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hTailFact : BlockLUFactSpec m r (blockSchur Ablk (pivotInv 0)) L_S U_S)
    (hTailL :
      blockMaxNorm hm hr L_S ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos m) hr Ablk pivotInv)
            (maxEntryNorm_pos_of_det_ne_zero hN
              (blockMatrixFirstSplitFlat Ablk) hdet)) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + m * r)
              (blockMatrixFirstSplitFlat Ablk))))
    (hTailU :
      blockMaxNorm hm hr U_S ≤
        growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero hN
            (blockMatrixFirstSplitFlat Ablk) hdet) *
        maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L *
          blockMaxNorm (Nat.succ_pos m) hr U ≤
            (n : ℝ) *
              (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
                (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                  hN (Nat.succ_pos m) hr Ablk pivotInv)
                (maxEntryNorm_pos_of_det_ne_zero hN
                  (blockMatrixFirstSplitFlat Ablk) hdet)) ^ 3 *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + m * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
              maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  have hRight :
      IsRightInverse (r + m * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero (r + m * r)
      (blockMatrixFirstSplitFlat Ablk) hdet).2
  simpa using
    higham13_eq13_22_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa
      hm hr hN Ablk pivotInv hpivot
      (maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFirstSplitFlat Ablk) hdet)
      hRight n hsn hNn L_S U_S hTailFact hTailL hTailU

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero one-step `BlockLUFactSpec` point-row product witness
    for the source-faithful first split. -/
theorem
    higham13_eq13_23_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hN : 0 < r + m * r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
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
        Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hRho_le_two :
      growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero hN
            (blockMatrixFirstSplitFlat Ablk) hdet) ≤ 2)
    (L_S U_S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hTailFact : BlockLUFactSpec m r (blockSchur Ablk (pivotInv 0)) L_S U_S)
    (hTailL :
      blockMaxNorm hm hr L_S ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos m) hr Ablk pivotInv)
            (maxEntryNorm_pos_of_det_ne_zero hN
              (blockMatrixFirstSplitFlat Ablk) hdet)) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + m * r)
              (blockMatrixFirstSplitFlat Ablk))))
    (hTailU :
      blockMaxNorm hm hr U_S ≤
        growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero hN
            (blockMatrixFirstSplitFlat Ablk) hdet) *
        maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L *
          blockMaxNorm (Nat.succ_pos m) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + m * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
              maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  have hRight :
      IsRightInverse (r + m * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero (r + m * r)
      (blockMatrixFirstSplitFlat Ablk) hdet).2
  simpa using
    higham13_eq13_23_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa
      hm hr hN Ablk pivotInv hpivot
      (maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFirstSplitFlat Ablk) hdet)
      hRight n hsn hNn hRho_le_two L_S U_S hTailFact hTailL hTailU

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    successor-shaped one-step factor witness with `rho <= 2` supplied by the
    first-split product-bound/diagonal-update BDD route. -/
theorem
    higham13_eq13_23_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa_of_product_bound_diag_update
    {m r : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
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
    (n : ℕ)
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
    (L_S U_S : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (hTailFact :
      BlockLUFactSpec (m + 1) r (blockSchur Ablk (pivotInv 0)) L_S U_S)
    (hTailL :
      blockMaxNorm (Nat.succ_pos m) hr L_S ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
              (blockMatrixFirstSplitFlat Ablk))))
    (hTailU :
      blockMaxNorm (Nat.succ_pos m) hr U_S ≤
        growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos *
        maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
          blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
              maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  let hmTail : 0 < m + 1 := Nat.succ_pos m
  have hRho_le_two :
      growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos ≤ 2 := by
    exact
      higham13_algorithm13_3_firstSplitStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hr hN Ablk pivotInv hApos invDiagBound stageInvDiagBound hDom
        hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate
  simpa [hmTail] using
    higham13_eq13_23_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa
      hmTail hr hN Ablk pivotInv hpivot hApos hRight n hsn hNn
      hRho_le_two L_S U_S hTailFact hTailL hTailU

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table form of the successor-shaped one-step factor/product
    update witness. -/
theorem
    higham13_eq13_23_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa_of_product_bound_diag_update_reciprocal
    {m r : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
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
    (n : ℕ)
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
    (L_S U_S : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (hTailFact :
      BlockLUFactSpec (m + 1) r (blockSchur Ablk (pivotInv 0)) L_S U_S)
    (hTailL :
      blockMaxNorm (Nat.succ_pos m) hr L_S ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
              (blockMatrixFirstSplitFlat Ablk))))
    (hTailU :
      blockMaxNorm (Nat.succ_pos m) hr U_S ≤
        growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos *
        maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
          blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
              maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  exact
    higham13_eq13_23_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa_of_product_bound_diag_update
      hr hN Ablk pivotInv hpivot hApos hRight n hsn hNn
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate L_S U_S hTailFact hTailL hTailU

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero one-step `BlockLUFactSpec` witness with the
    first-split product/update BDD route supplying `rho <= 2`. -/
theorem
    higham13_eq13_23_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
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
    (L_S U_S : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (hTailFact :
      BlockLUFactSpec (m + 1) r (blockSchur Ablk (pivotInv 0)) L_S U_S)
    (hTailL :
      blockMaxNorm (Nat.succ_pos m) hr L_S ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
            (maxEntryNorm_pos_of_det_ne_zero hN
              (blockMatrixFirstSplitFlat Ablk) hdet)) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
              (blockMatrixFirstSplitFlat Ablk))))
    (hTailU :
      blockMaxNorm (Nat.succ_pos m) hr U_S ≤
        growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero hN
            (blockMatrixFirstSplitFlat Ablk) hdet) *
        maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
          blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
              maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  have hRight :
      IsRightInverse (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero (r + (m + 1) * r)
      (blockMatrixFirstSplitFlat Ablk) hdet).2
  simpa using
    higham13_eq13_23_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa_of_product_bound_diag_update
      hr hN Ablk pivotInv hpivot
      (maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFirstSplitFlat Ablk) hdet)
      hRight n hsn hNn invDiagBound stageInvDiagBound hDom hDiagBound
      hInitInv hPivotInvBound hProduct hDiagUpdate L_S U_S hTailFact
      hTailL hTailU

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero reciprocal-table one-step `BlockLUFactSpec` witness
    for the first-split product/update route. -/
theorem
    higham13_eq13_23_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
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
    (L_S U_S : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (hTailFact :
      BlockLUFactSpec (m + 1) r (blockSchur Ablk (pivotInv 0)) L_S U_S)
    (hTailL :
      blockMaxNorm (Nat.succ_pos m) hr L_S ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
            (maxEntryNorm_pos_of_det_ne_zero hN
              (blockMatrixFirstSplitFlat Ablk) hdet)) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
              (blockMatrixFirstSplitFlat Ablk))))
    (hTailU :
      blockMaxNorm (Nat.succ_pos m) hr U_S ≤
        growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero hN
            (blockMatrixFirstSplitFlat Ablk) hdet) *
        maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
          blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
              maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  exact
    higham13_eq13_23_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
      hr hN Ablk pivotInv hpivot hdet n hsn hNn
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate L_S U_S hTailFact hTailL hTailU

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    existential-tail successor step for the point-row full-factor product lift.

    This is the Eq.13.23 analogue of
    `higham13_eq13_22_exists_blockLUFact_succ_norms_from_tail_witness_matrix_stage_history_exact_kappa`.
    Under the source-side `rho <= 2` hypothesis, an existential Schur-tail
    witness satisfying the Eq.13.22 separate lower/upper budgets yields a
    successor-size `BlockLUFactSpec` witness satisfying the displayed
    `8 n kappa(A) ||A||` product bound. -/
theorem higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_witness_matrix_stage_history_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hN : 0 < r + m * r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
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
      IsRightInverse (r + m * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat Ablk)))
    (n : ℕ)
    (hsn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((r + m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hRho_le_two :
      growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos ≤ 2)
    (hTail :
      ∃ L_S U_S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec m r (blockSchur Ablk (pivotInv 0)) L_S U_S ∧
          blockMaxNorm hm hr L_S ≤
            (n : ℝ) *
              (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
                (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                  hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 2 *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + m * r)
                  (blockMatrixFirstSplitFlat Ablk))) ∧
          blockMaxNorm hm hr U_S ≤
            growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN (Nat.succ_pos m) hr Ablk pivotInv) hApos *
            maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L *
          blockMaxNorm (Nat.succ_pos m) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + m * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
              maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  rcases hTail with ⟨L_S, U_S, hTailFact, hTailL, hTailU⟩
  exact
    higham13_eq13_23_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa
      hm hr hN Ablk pivotInv hpivot hApos hRight n hsn hNn hRho_le_two
      L_S U_S hTailFact hTailL hTailU

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    successor existential-tail product witness with `rho <= 2` supplied by the
    first-split product-bound/diagonal-update BDD route.

    This is the source-shaped product/update companion to
    `higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_witness_matrix_stage_history_exact_kappa`:
    the Schur-tail witness and its Eq.13.22 separate budgets remain explicit,
    while the raw first-split growth-factor side condition is derived from the
    BDD product/update data. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_witness_matrix_stage_history_exact_kappa_of_product_bound_diag_update
    {m r : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
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
    (n : ℕ)
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
      ∃ L_S U_S : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r (blockSchur Ablk (pivotInv 0)) L_S U_S ∧
          blockMaxNorm (Nat.succ_pos m) hr L_S ≤
            (n : ℝ) *
              (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
                (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                  hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos) ^ 2 *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) ∧
          blockMaxNorm (Nat.succ_pos m) hr U_S ≤
            growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos *
            maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
          blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
              maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  let hmTail : 0 < m + 1 := Nat.succ_pos m
  have hRho_le_two :
      growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos ≤ 2 := by
    exact
      higham13_algorithm13_3_firstSplitStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hr hN Ablk pivotInv hApos invDiagBound stageInvDiagBound hDom
        hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate
  simpa [hmTail] using
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_witness_matrix_stage_history_exact_kappa
      hmTail hr hN Ablk pivotInv hpivot hApos hRight n hsn hNn hRho_le_two
      hTail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table form of the successor existential-tail product/update
    witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_witness_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal
    {m r : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
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
    (n : ℕ)
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
      ∃ L_S U_S : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r (blockSchur Ablk (pivotInv 0)) L_S U_S ∧
          blockMaxNorm (Nat.succ_pos m) hr L_S ≤
            (n : ℝ) *
              (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
                (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                  hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos) ^ 2 *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) ∧
          blockMaxNorm (Nat.succ_pos m) hr U_S ≤
            growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos *
            maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
          blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
              maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_witness_matrix_stage_history_exact_kappa_of_product_bound_diag_update
      hr hN Ablk pivotInv hpivot hApos hRight n hsn hNn
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate hTail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero successor existential-tail product/update witness.

    This wrapper derives the positive growth denominator and canonical ambient
    `nonsingInv` right-inverse from `det(blockMatrixFirstSplitFlat Ablk) != 0`,
    while leaving the Schur-tail witness and source BDD product/update
    obligations explicit. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_witness_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
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
      ∃ L_S U_S : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r (blockSchur Ablk (pivotInv 0)) L_S U_S ∧
          blockMaxNorm (Nat.succ_pos m) hr L_S ≤
            (n : ℝ) *
              (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
                (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                  hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
                (maxEntryNorm_pos_of_det_ne_zero hN
                  (blockMatrixFirstSplitFlat Ablk) hdet)) ^ 2 *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) ∧
          blockMaxNorm (Nat.succ_pos m) hr U_S ≤
            growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
              (maxEntryNorm_pos_of_det_ne_zero hN
                (blockMatrixFirstSplitFlat Ablk) hdet) *
            maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
          blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
              maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  have hRight :
      IsRightInverse (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero (r + (m + 1) * r)
      (blockMatrixFirstSplitFlat Ablk) hdet).2
  simpa using
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_witness_matrix_stage_history_exact_kappa_of_product_bound_diag_update
      hr hN Ablk pivotInv hpivot
      (maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFirstSplitFlat Ablk) hdet)
      hRight n hsn hNn invDiagBound stageInvDiagBound hDom hDiagBound
      hInitInv hPivotInvBound hProduct hDiagUpdate hTail

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero reciprocal-table successor existential-tail
    product/update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_witness_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
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
      ∃ L_S U_S : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r (blockSchur Ablk (pivotInv 0)) L_S U_S ∧
          blockMaxNorm (Nat.succ_pos m) hr L_S ≤
            (n : ℝ) *
              (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
                (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                  hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
                (maxEntryNorm_pos_of_det_ne_zero hN
                  (blockMatrixFirstSplitFlat Ablk) hdet)) ^ 2 *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) ∧
          blockMaxNorm (Nat.succ_pos m) hr U_S ≤
            growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
              (maxEntryNorm_pos_of_det_ne_zero hN
                (blockMatrixFirstSplitFlat Ablk) hdet) *
            maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk)) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
          blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
                maxEntryNormRect hN hN (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat Ablk))) *
              maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) := by
  exact
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_witness_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
      hr hN Ablk pivotInv hpivot hdet n hsn hNn
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate hTail

end NumStability
