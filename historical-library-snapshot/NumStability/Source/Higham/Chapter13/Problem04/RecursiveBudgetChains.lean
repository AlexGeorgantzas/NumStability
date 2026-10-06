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
import NumStability.Algorithms.LinearSystems.LU.BlockLU.GrowthBounds
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Equation22
import NumStability.Source.Higham.Chapter13.Equation23
import NumStability.Source.Higham.Chapter13.Problem04.ActiveStageBounds
import NumStability.Source.Higham.Chapter13.Problem04.BlockInverseBounds
import NumStability.Source.Higham.Chapter13.Problem04.HistoryEnvelope
import NumStability.Source.Higham.Chapter13.Problem04.LocalGrowth
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStages
import NumStability.Source.Higham.Chapter13.Problem04.ProductBounds
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis

/-!
# Source.Higham.Chapter13.Problem04.RecursiveBudgetChains

This module formalizes the source-facing Chapter 13 statements for
`Problem04.RecursiveBudgetChains`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    one-block exact-κ instantiation of the ambient-budget chain.

    This is the base constructor for the recursive chain using the source
    constants `rho = growthFactorEntry A G` and
    `kappa(A) = ‖A‖_max * ‖Ainv‖_max`. -/
theorem higham13_eq13_22_blockLUBudgetChain_one_from_matrix_stage_history_exact_kappa
    {r : ℕ} (hr : 0 < r)
    (Ablk : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (1 * r) → Fin (1 * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk))
    (hRight : IsRightInverse (1 * r) (blockMatrixFlatFin Ablk) Ainv)
    (n : ℕ) (hNn : (((1 * r : ℕ) : ℝ) ≤ (n : ℝ))) :
    Higham13BlockLUBudgetChain hr
      ((n : ℝ) *
        (growthFactorEntry (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos 0) hr) (Nat.succ_pos 0) hr Ablk pivotInv)
          hApos) ^ 2 *
        (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
            (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
            (Nat.mul_pos (Nat.succ_pos 0) hr) Ainv))
      (growthFactorEntry (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos 0) hr) (Nat.succ_pos 0) hr Ablk pivotInv)
          hApos *
        maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
          (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk))
      0 Ablk pivotInv := by
  let hm : 0 < 1 := Nat.succ_pos 0
  let hN : 0 < 1 * r := Nat.mul_pos hm hr
  let A0 : Fin (1 * r) → Fin (1 * r) → ℝ := blockMatrixFlatFin Ablk
  let G : Fin (1 * r) → Fin (1 * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv
  let Ainv0 : Fin (1 * r) → Fin (1 * r) → ℝ := Ainv
  let rho : ℝ := growthFactorEntry hN A0 G hApos
  let kappaA : ℝ := maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv0
  let normA : ℝ := maxEntryNormRect hN hN A0
  have hA_le_G : maxEntryNorm hN A0 ≤ maxEntryNorm hN G := by
    simpa [hN, hm, A0, G] using
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_flat_initial
        hm hr Ablk pivotInv
  have hId : 1 ≤ (n : ℝ) * rho ^ 2 * kappaA := by
    simpa [hN, A0, G, Ainv0, rho, kappaA] using
      higham13_eq13_22_lower_diagonal_budget_from_right_inverse_growth
        hN A0 G Ainv0 hApos (by simpa [A0, Ainv0] using hRight)
        n hNn hA_le_G
  have hU_le_G : blockMaxNorm hm hr Ablk ≤ maxEntryNorm hN G := by
    rw [← maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm hm hr Ablk]
    simpa [A0, G] using hA_le_G
  have hU :
      blockMaxNorm hm hr Ablk ≤ rho * normA :=
    blockMaxNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm
      hN hm hr A0 G Ablk hApos hU_le_G
  simpa [hN, hm, A0, G, Ainv0, rho, kappaA, normA] using
    (Higham13BlockLUBudgetChain.one (hr := hr)
      (C_L := (n : ℝ) * rho ^ 2 * kappaA)
      (C_U := rho * normA)
      (A := Ablk) (pivotInv := pivotInv) hId hU)

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    determinant-nonzero base case for the recursive exact-κ chain.

    This removes both auxiliary base-case certificates: `det A ≠ 0` supplies
    the positive growth-factor denominator and the `nonsingInv` right inverse. -/
theorem
    higham13_eq13_22_blockLUBudgetChain_one_from_matrix_stage_history_exact_kappa_of_det_ne_zero
    {r : ℕ} (hr : 0 < r)
    (Ablk : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (1 * r)) (Fin (1 * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : (((1 * r : ℕ) : ℝ) ≤ (n : ℝ))) :
    Higham13BlockLUBudgetChain hr
      ((n : ℝ) *
        (growthFactorEntry (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos 0) hr) (Nat.succ_pos 0) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk) hdet)) ^ 2 *
        (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
            (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
            (Nat.mul_pos (Nat.succ_pos 0) hr)
            (nonsingInv (1 * r) (blockMatrixFlatFin Ablk))))
      (growthFactorEntry (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos 0) hr) (Nat.succ_pos 0) hr Ablk pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk) hdet) *
        maxEntryNormRect (Nat.mul_pos (Nat.succ_pos 0) hr)
          (Nat.mul_pos (Nat.succ_pos 0) hr) (blockMatrixFlatFin Ablk))
      0 Ablk pivotInv := by
  let hN : 0 < 1 * r := Nat.mul_pos (Nat.succ_pos 0) hr
  let A0 : Fin (1 * r) → Fin (1 * r) → ℝ := blockMatrixFlatFin Ablk
  let hApos : 0 < maxEntryNorm hN A0 :=
    maxEntryNorm_pos_of_det_ne_zero hN A0 hdet
  have hRight : IsRightInverse (1 * r) A0 (nonsingInv (1 * r) A0) :=
    (isInverse_nonsingInv_of_det_ne_zero (1 * r) A0 hdet).2
  simpa [hN, A0, hApos] using
    higham13_eq13_22_blockLUBudgetChain_one_from_matrix_stage_history_exact_kappa
      hr Ablk pivotInv (nonsingInv (1 * r) A0) hApos hRight n hNn

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    local block product bound using the finite local growth-history envelope.

    This removes the three explicit common-containment hypotheses from
    `higham13_eq13_22_local_block_product_from_source_growthFactorEntry_exact_kappa`
    by using the envelope whose max entry is the maximum of the initial matrix,
    the current Schur complement, and the block upper factor. -/
theorem higham13_eq13_22_local_block_product_from_history_envelope_exact_kappa
    {r s mb rb : ℕ} (hr : 0 < r) (hs : 0 < s) (hN : 0 < r + s)
    (hmb : 0 < mb) (hrb : 0 < rb)
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (Ufac : Fin mb → Fin mb → (Fin rb → Fin rb → ℝ))
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin s) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)]
    (hA11_block : A11 =
      fun i j : Fin r =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA12_block : A12 =
      fun (i : Fin r) (j : Fin s) =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hApos : 0 < maxEntryNorm hN A)
    (n : ℕ)
    (hsn : (s : ℝ) ≤ (n : ℝ)) :
    let S : Matrix (Fin s) (Fin s) ℝ := A22 - A21 * ⅟A11 * A12
    let G : Fin (r + s) → Fin (r + s) → ℝ :=
      higham13_problem13_4_localGrowthEnvelope hN hs hmb hrb A S Ufac
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) *
        blockMaxNorm hmb hrb Ufac ≤
      (n : ℝ) * (growthFactorEntry hN A G hApos) ^ 3 *
        (maxEntryNormRect hN hN A *
          maxEntryNormRect hN hN (nonsingInv (r + s) A)) *
        maxEntryNormRect hN hN A := by
  intro S G
  exact
    higham13_eq13_22_local_block_product_from_source_growthFactorEntry_exact_kappa
      hr hs hN hmb hrb A G Ufac A11 A12 A21 A22
      hA11_block hA12_block hA21_block hA22_block
      hApos n hsn
      (by
        simpa [G, S] using
          higham13_problem13_4_localGrowthEnvelope_contains_initial
            hN hs hmb hrb A S Ufac)
      (by
        simpa [G, S] using
          higham13_problem13_4_localGrowthEnvelope_contains_schur
            hN hs hmb hrb A S Ufac)
      (by
        simpa [G, S] using
          higham13_problem13_4_localGrowthEnvelope_contains_block_upper
            hN hs hmb hrb A S Ufac)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    local block product bound from the finite local growth-history envelope
    plus the source-side point-row hypothesis `ρ_n <= 2`. -/
theorem higham13_eq13_23_local_block_product_from_history_envelope_exact_kappa
    {r s mb rb : ℕ} (hr : 0 < r) (hs : 0 < s) (hN : 0 < r + s)
    (hmb : 0 < mb) (hrb : 0 < rb)
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (Ufac : Fin mb → Fin mb → (Fin rb → Fin rb → ℝ))
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin s) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)]
    (hA11_block : A11 =
      fun i j : Fin r =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA12_block : A12 =
      fun (i : Fin r) (j : Fin s) =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hApos : 0 < maxEntryNorm hN A)
    (n : ℕ)
    (hsn : (s : ℝ) ≤ (n : ℝ))
    (hRho_le_two :
      let S : Matrix (Fin s) (Fin s) ℝ := A22 - A21 * ⅟A11 * A12
      let G : Fin (r + s) → Fin (r + s) → ℝ :=
        higham13_problem13_4_localGrowthEnvelope hN hs hmb hrb A S Ufac
      growthFactorEntry hN A G hApos ≤ 2) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) *
        blockMaxNorm hmb hrb Ufac ≤
      8 * (n : ℝ) *
        (maxEntryNormRect hN hN A *
          maxEntryNormRect hN hN (nonsingInv (r + s) A)) *
        maxEntryNormRect hN hN A := by
  let S : Matrix (Fin s) (Fin s) ℝ := A22 - A21 * ⅟A11 * A12
  let G : Fin (r + s) → Fin (r + s) → ℝ :=
    higham13_problem13_4_localGrowthEnvelope hN hs hmb hrb A S Ufac
  exact
    higham13_eq13_23_local_block_product_from_source_growthFactorEntry_exact_kappa
      hr hs hN hmb hrb A G Ufac A11 A12 A21 A22
      hA11_block hA12_block hA21_block hA22_block
      hApos n hsn
      (by
        simpa [G, S] using
          higham13_problem13_4_localGrowthEnvelope_contains_initial
            hN hs hmb hrb A S Ufac)
      (by
        simpa [G, S] using
          higham13_problem13_4_localGrowthEnvelope_contains_schur
            hN hs hmb hrb A S Ufac)
      (by
        simpa [G, S] using
          higham13_problem13_4_localGrowthEnvelope_contains_block_upper
            hN hs hmb hrb A S Ufac)
      (by simpa [G, S] using hRho_le_two)

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    local block product bound from any growth matrix that dominates the finite
    local history envelope.

    This is the single-containment interface needed by the recursive GE route:
    prove that the global history object dominates the local envelope, and the
    separate initial/Schur/upper containment hypotheses are discharged. -/
theorem higham13_eq13_22_local_block_product_from_dominated_history_envelope_exact_kappa
    {r s mb rb : ℕ} (hr : 0 < r) (hs : 0 < s) (hN : 0 < r + s)
    (hmb : 0 < mb) (hrb : 0 < rb)
    (A G : Fin (r + s) → Fin (r + s) → ℝ)
    (Ufac : Fin mb → Fin mb → (Fin rb → Fin rb → ℝ))
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin s) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)]
    (hA11_block : A11 =
      fun i j : Fin r =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA12_block : A12 =
      fun (i : Fin r) (j : Fin s) =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hApos : 0 < maxEntryNorm hN A)
    (n : ℕ)
    (hsn : (s : ℝ) ≤ (n : ℝ))
    (hEnv_le_G :
      let S : Matrix (Fin s) (Fin s) ℝ := A22 - A21 * ⅟A11 * A12
      maxEntryNorm hN
          (higham13_problem13_4_localGrowthEnvelope hN hs hmb hrb A S Ufac) ≤
        maxEntryNorm hN G) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) *
        blockMaxNorm hmb hrb Ufac ≤
      (n : ℝ) * (growthFactorEntry hN A G hApos) ^ 3 *
        (maxEntryNormRect hN hN A *
          maxEntryNormRect hN hN (nonsingInv (r + s) A)) *
        maxEntryNormRect hN hN A := by
  let S : Matrix (Fin s) (Fin s) ℝ := A22 - A21 * ⅟A11 * A12
  have hA_le_G : maxEntryNorm hN A ≤ maxEntryNorm hN G := by
    exact le_trans
      (higham13_problem13_4_localGrowthEnvelope_contains_initial
        hN hs hmb hrb A S Ufac)
      (by simpa [S] using hEnv_le_G)
  have hS_le_G : maxEntryNormRect hs hs S ≤ maxEntryNorm hN G := by
    exact le_trans
      (higham13_problem13_4_localGrowthEnvelope_contains_schur
        hN hs hmb hrb A S Ufac)
      (by simpa [S] using hEnv_le_G)
  have hU_le_G : blockMaxNorm hmb hrb Ufac ≤ maxEntryNorm hN G := by
    exact le_trans
      (higham13_problem13_4_localGrowthEnvelope_contains_block_upper
        hN hs hmb hrb A S Ufac)
      (by simpa [S] using hEnv_le_G)
  simpa [S] using
    higham13_eq13_22_local_block_product_from_source_growthFactorEntry_exact_kappa
      hr hs hN hmb hrb A G Ufac A11 A12 A21 A22
      hA11_block hA12_block hA21_block hA22_block
      hApos n hsn hA_le_G hS_le_G hU_le_G

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row specialization of the dominated local history-envelope bridge. -/
theorem higham13_eq13_23_local_block_product_from_dominated_history_envelope_exact_kappa
    {r s mb rb : ℕ} (hr : 0 < r) (hs : 0 < s) (hN : 0 < r + s)
    (hmb : 0 < mb) (hrb : 0 < rb)
    (A G : Fin (r + s) → Fin (r + s) → ℝ)
    (Ufac : Fin mb → Fin mb → (Fin rb → Fin rb → ℝ))
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin s) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)]
    (hA11_block : A11 =
      fun i j : Fin r =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA12_block : A12 =
      fun (i : Fin r) (j : Fin s) =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hApos : 0 < maxEntryNorm hN A)
    (n : ℕ)
    (hsn : (s : ℝ) ≤ (n : ℝ))
    (hEnv_le_G :
      let S : Matrix (Fin s) (Fin s) ℝ := A22 - A21 * ⅟A11 * A12
      maxEntryNorm hN
          (higham13_problem13_4_localGrowthEnvelope hN hs hmb hrb A S Ufac) ≤
        maxEntryNorm hN G)
    (hRho_le_two : growthFactorEntry hN A G hApos ≤ 2) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) *
        blockMaxNorm hmb hrb Ufac ≤
      8 * (n : ℝ) *
        (maxEntryNormRect hN hN A *
          maxEntryNormRect hN hN (nonsingInv (r + s) A)) *
        maxEntryNormRect hN hN A := by
  let S : Matrix (Fin s) (Fin s) ℝ := A22 - A21 * ⅟A11 * A12
  have hA_le_G : maxEntryNorm hN A ≤ maxEntryNorm hN G := by
    exact le_trans
      (higham13_problem13_4_localGrowthEnvelope_contains_initial
        hN hs hmb hrb A S Ufac)
      (by simpa [S] using hEnv_le_G)
  have hS_le_G : maxEntryNormRect hs hs S ≤ maxEntryNorm hN G := by
    exact le_trans
      (higham13_problem13_4_localGrowthEnvelope_contains_schur
        hN hs hmb hrb A S Ufac)
      (by simpa [S] using hEnv_le_G)
  have hU_le_G : blockMaxNorm hmb hrb Ufac ≤ maxEntryNorm hN G := by
    exact le_trans
      (higham13_problem13_4_localGrowthEnvelope_contains_block_upper
        hN hs hmb hrb A S Ufac)
      (by simpa [S] using hEnv_le_G)
  simpa [S] using
    higham13_eq13_23_local_block_product_from_source_growthFactorEntry_exact_kappa
      hr hs hN hmb hrb A G Ufac A11 A12 A21 A22
      hA11_block hA12_block hA21_block hA22_block
      hApos n hsn hA_le_G hS_le_G hU_le_G hRho_le_two

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 feeding equation (13.22):
    the source-faithful matrix-product Algorithm 13.3 stage history supplies the
    first-split lower-left premise `‖A₂₁ A₁₁⁻¹‖ <= n ρ_n² κ(A)`.

    This is the first-split lower-factor half used by recursive Eq.13.22/13.23
    assembly.  The remaining full-factor recursion is kept separate; here the
    only growth bookkeeping is that the stage-history matrix contains the
    initial matrix and the first Schur-complement tail. -/
theorem higham13_problem13_4_L21_eq13_22_premise_from_matrix_stage_history_first_split_exact_kappa
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
    (n : ℕ) (hsn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    maxEntryNormRect (Nat.mul_pos hm hr) hr
        ((blockMatrixFirstSplitA21 Ablk *
          ⅟(blockMatrixFirstSplitA11 Ablk) : Matrix (Fin (m * r)) (Fin r) ℝ)) ≤
      (n : ℝ) *
        (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos m) hr Ablk pivotInv) hApos) ^ 2 *
        (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
          maxEntryNormRect hN hN (nonsingInv (r + m * r)
            (blockMatrixFirstSplitFlat Ablk))) := by
  letI hA11Inv : Invertible (blockMatrixFirstSplitA11 Ablk) := inferInstance
  let A11_inv : Matrix (Fin r) (Fin r) ℝ := ⅟(blockMatrixFirstSplitA11 Ablk)
  refine
    higham13_problem13_4_L21_eq13_22_premise_from_source_global_growth_tableau_exact_kappa
      hr (Nat.mul_pos hm hr) hN
      (blockMatrixFirstSplitFlat Ablk)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hN (Nat.succ_pos m) hr Ablk pivotInv)
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk)
      ?_ ?_ ?_ ?_ hApos n hsn ?_ ?_
  · ext i j
    simp [blockMatrixFirstSplitA11, blockMatrixFirstSplitFlat]
  · ext i j
    simp [blockMatrixFirstSplitA12, blockMatrixFirstSplitFlat]
  · ext i j
    simp [blockMatrixFirstSplitA21, blockMatrixFirstSplitFlat]
  · ext i j
    simp [blockMatrixFirstSplitA22, blockMatrixFirstSplitFlat, blockMatrixFlatFin]
  · exact le_trans
      (maxEntryNorm_blockMatrixFirstSplitFlat_le_blockMaxNorm_of_hN hN hm hr Ablk)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
        hN (Nat.succ_pos m) hr Ablk pivotInv)
  · have htail :
        higham13_algorithm13_3_schurStageMatrixTailBlock Ablk pivotInv 1 Fin.succ =
          blockSchur Ablk A11_inv := by
        exact higham13_algorithm13_3_schurStageMatrixBlock_one_tail_eq_blockSchur
          Ablk pivotInv A11_inv (by simpa [A11_inv] using hpivot)
    have hS :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_flat_stage_tail
        hN (Nat.succ_pos m) hr hm Ablk pivotInv 1 (by omega) Fin.succ
    rw [htail] at hS
    rw [blockMatrixFirstSplit_schur_eq_blockMatrixFlatFin_blockSchur
      Ablk A11_inv]
    simpa [maxEntryNormRect_eq_maxEntryNorm (Nat.mul_pos hm hr)] using hS

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    first-split block product bound with the finite matrix-product Algorithm
    13.3 stage history as the dominating growth object.

    The equalities `hA_eq` and `hG_eq` are representation bridges tying the
    abstract local Eq.13.22 API to the source-shaped first-split flattening and
    stage-history matrix; they carry no additional mathematical assumption. -/
theorem higham13_eq13_22_local_block_product_from_matrix_stage_history_first_split_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hN : 0 < r + m * r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (A G : Fin (r + m * r) → Fin (r + m * r) → ℝ)
    (hA_eq : A = blockMatrixFirstSplitFlat Ablk)
    (hG_eq :
      G =
        higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos m) hr Ablk pivotInv)
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
    (hApos : 0 < maxEntryNorm hN A)
    (n : ℕ) (hsn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let Ufac : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ) :=
      higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv
    maxEntryNormRect (Nat.mul_pos hm hr) hr
        ((blockMatrixFirstSplitA21 Ablk *
          ⅟(blockMatrixFirstSplitA11 Ablk) : Matrix (Fin (m * r)) (Fin r) ℝ)) *
        blockMaxNorm (Nat.succ_pos m) hr Ufac ≤
      (n : ℝ) * (growthFactorEntry hN A G hApos) ^ 3 *
        (maxEntryNormRect hN hN A *
          maxEntryNormRect hN hN (nonsingInv (r + m * r) A)) *
        maxEntryNormRect hN hN A := by
  subst A
  subst G
  dsimp only
  refine
    higham13_eq13_22_local_block_product_from_dominated_history_envelope_exact_kappa
      hr (Nat.mul_pos hm hr) hN
      (Nat.succ_pos m) hr
      (blockMatrixFirstSplitFlat Ablk)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hN (Nat.succ_pos m) hr Ablk pivotInv)
      (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv)
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk)
      ?_ ?_ ?_ ?_ hApos n hsn ?_
  · ext i j
    simp [blockMatrixFirstSplitA11, blockMatrixFirstSplitFlat]
  · ext i j
    simp [blockMatrixFirstSplitA12, blockMatrixFirstSplitFlat]
  · ext i j
    simp [blockMatrixFirstSplitA21, blockMatrixFirstSplitFlat]
  · ext i j
    simp [blockMatrixFirstSplitA22, blockMatrixFirstSplitFlat, blockMatrixFlatFin]
  · dsimp only
    rw [blockMatrixFirstSplit_schur_eq_blockMatrixFlatFin_blockSchur]
    exact
      higham13_problem13_4_localGrowthEnvelope_le_matrixStageHistoryGrowthMatrix_of_blockSchur_first_split_of_hN
        hm hr hN Ablk pivotInv (⅟(blockMatrixFirstSplitA11 Ablk)) hpivot

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row specialization of the first-split matrix-stage-history local
    block product bound, using the source-side hypothesis `ρ_n <= 2`. -/
theorem higham13_eq13_23_local_block_product_from_matrix_stage_history_first_split_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hN : 0 < r + m * r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (A G : Fin (r + m * r) → Fin (r + m * r) → ℝ)
    (hA_eq : A = blockMatrixFirstSplitFlat Ablk)
    (hG_eq :
      G =
        higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos m) hr Ablk pivotInv)
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
    (hApos : 0 < maxEntryNorm hN A)
    (n : ℕ) (hsn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hRho_le_two : growthFactorEntry hN A G hApos ≤ 2) :
    let Ufac : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ) :=
      higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv
    maxEntryNormRect (Nat.mul_pos hm hr) hr
        ((blockMatrixFirstSplitA21 Ablk *
          ⅟(blockMatrixFirstSplitA11 Ablk) : Matrix (Fin (m * r)) (Fin r) ℝ)) *
        blockMaxNorm (Nat.succ_pos m) hr Ufac ≤
      8 * (n : ℝ) *
        (maxEntryNormRect hN hN A *
          maxEntryNormRect hN hN (nonsingInv (r + m * r) A)) *
        maxEntryNormRect hN hN A := by
  subst A
  subst G
  dsimp only
  refine
    higham13_eq13_23_local_block_product_from_dominated_history_envelope_exact_kappa
      hr (Nat.mul_pos hm hr) hN
      (Nat.succ_pos m) hr
      (blockMatrixFirstSplitFlat Ablk)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hN (Nat.succ_pos m) hr Ablk pivotInv)
      (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv)
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk)
      ?_ ?_ ?_ ?_ hApos n hsn ?_ hRho_le_two
  · ext i j
    simp [blockMatrixFirstSplitA11, blockMatrixFirstSplitFlat]
  · ext i j
    simp [blockMatrixFirstSplitA12, blockMatrixFirstSplitFlat]
  · ext i j
    simp [blockMatrixFirstSplitA21, blockMatrixFirstSplitFlat]
  · ext i j
    simp [blockMatrixFirstSplitA22, blockMatrixFirstSplitFlat, blockMatrixFlatFin]
  · dsimp only
    rw [blockMatrixFirstSplit_schur_eq_blockMatrixFlatFin_blockSchur]
    exact
      higham13_problem13_4_localGrowthEnvelope_le_matrixStageHistoryGrowthMatrix_of_blockSchur_first_split_of_hN
        hm hr hN Ablk pivotInv (⅟(blockMatrixFirstSplitA11 Ablk)) hpivot

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    successor exact-κ instantiation of the ambient-budget chain.

    Given a tail chain under the full first-split source constants, this
    theorem discharges the new successor constructor obligations from the
    source-faithful first-split matrix-stage history.  The recursive tail chain
    remains the visible source obligation. -/
theorem higham13_eq13_22_blockLUBudgetChain_succ_from_matrix_stage_history_first_split_exact_kappa
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
    (hRight :
      IsRightInverse (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
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
      (m + 1) Ablk pivotInv := by
  let hmTail : 0 < m + 1 := Nat.succ_pos m
  let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    blockMatrixFirstSplitFlat Ablk
  let G : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hmFull hr Ablk pivotInv
  let Ainv : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    nonsingInv (r + (m + 1) * r) A0
  let rho : ℝ := growthFactorEntry hN A0 G hApos
  let kappaA : ℝ := maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv
  let normA : ℝ := maxEntryNormRect hN hN A0
  have hA_le_G : maxEntryNorm hN A0 ≤ maxEntryNorm hN G := by
    exact le_trans
      (by
        simpa [A0] using
          maxEntryNorm_blockMatrixFirstSplitFlat_le_blockMaxNorm_of_hN
            hN hmTail hr Ablk)
      (by
        simpa [G] using
          higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
            hN hmFull hr Ablk pivotInv)
  have hId : 1 ≤ (n : ℝ) * rho ^ 2 * kappaA := by
    simpa [A0, G, Ainv, rho, kappaA] using
      higham13_eq13_22_lower_diagonal_budget_from_right_inverse_growth
        hN A0 G Ainv hApos (by simpa [A0, Ainv] using hRight)
        n hNn hA_le_G
  have hL21 :
      maxEntryNormRect (Nat.mul_pos hmTail hr) hr
          ((blockMatrixFirstSplitA21 Ablk * pivotInv 0 :
            Matrix (Fin ((m + 1) * r)) (Fin r) ℝ)) ≤
        (n : ℝ) * rho ^ 2 * kappaA := by
    simpa [A0, G, Ainv, rho, kappaA, hpivot] using
      higham13_problem13_4_L21_eq13_22_premise_from_matrix_stage_history_first_split_exact_kappa
        hmTail hr hN Ablk pivotInv hpivot hApos n hsn
  have hFirstRow :
      ∀ j : Fin ((m + 1) + 1), maxEntryNorm hr (Ablk 0 j) ≤ rho * normA := by
    have hInput :
        blockMaxNorm hmFull hr Ablk ≤ rho * normA := by
      simpa [A0, G, rho, normA] using
        blockMaxNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm
          hN hmFull hr A0 G Ablk hApos
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
            hN hmFull hr Ablk pivotInv)
    intro j
    exact le_trans (block_le_blockMaxNorm hmFull hr Ablk 0 j) hInput
  simpa [A0, G, Ainv, rho, kappaA, normA, hmTail, hmFull] using
    (Higham13BlockLUBudgetChain.succ (hr := hr)
      (C_L := (n : ℝ) * rho ^ 2 * kappaA)
      (C_U := rho * normA)
      (A := Ablk) (pivotInv := pivotInv)
      hpivot hId hL21 hFirstRow hTail)

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    successor exact-κ chain constructor from a tail-local chain plus the
    source inverse-ratio comparison.

    This is the recursive-chain version of the remaining Problem 13.4 route:
    the tail chain may be proved under its own exact matrix-stage constants,
    and the inverse-ratio comparison transports it to the full ambient budgets
    before the first-split successor constructor is applied. -/
theorem
    higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa
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
    (hRight :
      IsRightInverse (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
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
  dsimp only
  intro hInvRatio hTailLocal
  let hNFull : 0 < r + (m + 1) * r :=
    Nat.add_pos_left hr ((m + 1) * r)
  have hTailFull :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFull (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hNFull hNFull
              (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))))
        (growthFactorEntry hNFull (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos *
          maxEntryNormRect hNFull hNFull (blockMatrixFirstSplitFlat Ablk))
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) := by
    simpa [hNFull] using
      higham13_eq13_22_tail_chain_to_full_budget_from_inverse_ratio_matrix_stage_history_exact_kappa
        hr Ablk pivotInv hTailPos hApos n hInvRatio hTailLocal
  simpa [hNFull] using
    higham13_eq13_22_blockLUBudgetChain_succ_from_matrix_stage_history_first_split_exact_kappa
      hr hNFull Ablk pivotInv hpivot hApos hRight n hsn hNn hTailFull

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    successor exact-kappa chain constructor from a tail-local chain plus the
    direct lower-budget comparison.

    This is the same recursive-tail assembly as the inverse-ratio wrapper, but
    it exposes the scalar lower-budget comparison itself.  It is the route used
    by source arguments that prove the needed lower/condition comparison
    directly, without packaging it first as an inverse-ratio statement. -/
theorem
    higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa
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
    (hRight :
      IsRightInverse (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
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
  dsimp only
  intro hLower hTailLocal
  let hNFull : 0 < r + (m + 1) * r :=
    Nat.add_pos_left hr ((m + 1) * r)
  have hTailFull :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFull (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hNFull hNFull
              (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))))
        (growthFactorEntry hNFull (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv) hApos *
          maxEntryNormRect hNFull hNFull (blockMatrixFirstSplitFlat Ablk))
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) := by
    simpa [hNFull] using
      higham13_eq13_22_tail_chain_to_full_budget_from_lower_comparison_matrix_stage_history_exact_kappa
        hr Ablk pivotInv hTailPos hApos n hLower hTailLocal
  simpa [hNFull] using
    higham13_eq13_22_blockLUBudgetChain_succ_from_matrix_stage_history_first_split_exact_kappa
      hr hNFull Ablk pivotInv hpivot hApos hRight n hsn hNn hTailFull

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    source-shaped successor product witness from an ambient tail chain.

    This composes the exact-κ first-split constructor with the chain-to-product
    wrapper.  The recursive tail chain is still the visible source obligation,
    but the full matrix conclusion is now a concrete `BlockLUFactSpec`
    witness with the displayed Eq.13.22 product bound. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_chain_matrix_stage_history_exact_kappa
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
    (hRight :
      IsRightInverse (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
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
  let G : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv
  let Ainv : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)
  have hchain :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk) G hApos) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN Ainv))
        (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk) G hApos *
          maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk))
        (m + 1) Ablk pivotInv := by
    simpa [G, Ainv] using
      higham13_eq13_22_blockLUBudgetChain_succ_from_matrix_stage_history_first_split_exact_kappa
        hr hN Ablk pivotInv hpivot hApos hRight n hsn hNn hTail
  simpa [G, Ainv] using
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_22_product_exact_kappa
      (r := r) hr (hN := hN)
      (A0 := blockMatrixFirstSplitFlat Ablk)
      (G := G)
      (Ainv := Ainv)
      hApos n hchain

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row successor product witness from an ambient tail chain.

    This is the Eq.13.23 companion to
    `higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_chain_matrix_stage_history_exact_kappa`;
    it additionally requires the source-side `rho <= 2` hypothesis for the
    full first-split growth matrix. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_chain_matrix_stage_history_exact_kappa
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
    (hRight :
      IsRightInverse (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
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
  let G : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv
  let Ainv : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)
  have hchain :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) *
          (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk) G hApos) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hN hN Ainv))
        (growthFactorEntry hN (blockMatrixFirstSplitFlat Ablk) G hApos *
          maxEntryNormRect hN hN (blockMatrixFirstSplitFlat Ablk))
        (m + 1) Ablk pivotInv := by
    simpa [G, Ainv] using
      higham13_eq13_22_blockLUBudgetChain_succ_from_matrix_stage_history_first_split_exact_kappa
        hr hN Ablk pivotInv hpivot hApos hRight n hsn hNn hTail
  simpa [G, Ainv] using
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_23_product_exact_kappa
      (r := r) hr (hN := hN)
      (A0 := blockMatrixFirstSplitFlat Ablk)
      (G := G)
      (Ainv := Ainv)
      hApos n hchain (by simpa [G] using hRho_le_two)

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    successor product witness from a tail-local chain plus the source
    inverse-ratio comparison.

    This packages the recursive-tail transport route all the way to a concrete
    `BlockLUFactSpec` witness: a tail chain under its own exact matrix-stage
    constants, together with the inverse-ratio comparison that transports those
    constants to the full matrix, yields the displayed Eq.13.22 product bound
    for the successor full matrix. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa
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
    (hRight :
      IsRightInverse (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
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
  dsimp only
  intro hInvRatio hTailLocal
  let hNFull : 0 < r + (m + 1) * r :=
    Nat.add_pos_left hr ((m + 1) * r)
  let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    blockMatrixFirstSplitFlat Ablk
  let Gfull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv
  let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    nonsingInv (r + (m + 1) * r) A0
  have hchain :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull))
        (growthFactorEntry hNFull A0 Gfull hApos *
          maxEntryNormRect hNFull hNFull A0)
        (m + 1) Ablk pivotInv := by
    simpa [hNFull, A0, Gfull, AinvFull] using
      higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa
        hr Ablk pivotInv hpivot hTailPos hApos hRight n hsn hNn
        hInvRatio hTailLocal
  simpa [hNFull, A0, Gfull, AinvFull] using
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_22_product_exact_kappa
      (r := r) hr (hN := hNFull)
      (A0 := A0) (G := Gfull) (Ainv := AinvFull)
      hApos n hchain

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row successor product witness from a tail-local chain plus the source
    inverse-ratio comparison.

    This is the Eq.13.23 companion of the preceding Eq.13.22 wrapper.  It
    carries the source-side `rho <= 2` hypothesis for the full first-split
    growth matrix and otherwise uses the same tail-local transport route. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa
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
    (hRight :
      IsRightInverse (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
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
  dsimp only
  intro hInvRatio hTailLocal
  let hNFull : 0 < r + (m + 1) * r :=
    Nat.add_pos_left hr ((m + 1) * r)
  let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    blockMatrixFirstSplitFlat Ablk
  let Gfull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv
  let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    nonsingInv (r + (m + 1) * r) A0
  have hchain :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull))
        (growthFactorEntry hNFull A0 Gfull hApos *
          maxEntryNormRect hNFull hNFull A0)
        (m + 1) Ablk pivotInv := by
    simpa [hNFull, A0, Gfull, AinvFull] using
      higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa
        hr Ablk pivotInv hpivot hTailPos hApos hRight n hsn hNn
        hInvRatio hTailLocal
  simpa [hNFull, A0, Gfull, AinvFull] using
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_23_product_exact_kappa
      (r := r) hr (hN := hNFull)
      (A0 := A0) (G := Gfull) (Ainv := AinvFull)
      hApos n hchain (by simpa [hNFull, A0, Gfull] using hRho_le_two)

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    successor product witness from a tail-local chain plus the direct
    lower-budget comparison.

    This packages the lower-comparison transport route all the way to a
    concrete `BlockLUFactSpec` witness.  The remaining source obligations are
    the recursive tail-local chain and the direct lower/condition scalar
    comparison displayed in the hypotheses. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa
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
    (hRight :
      IsRightInverse (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
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
  dsimp only
  intro hLower hTailLocal
  let hNFull : 0 < r + (m + 1) * r :=
    Nat.add_pos_left hr ((m + 1) * r)
  let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    blockMatrixFirstSplitFlat Ablk
  let Gfull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv
  let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    nonsingInv (r + (m + 1) * r) A0
  have hchain :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull))
        (growthFactorEntry hNFull A0 Gfull hApos *
          maxEntryNormRect hNFull hNFull A0)
        (m + 1) Ablk pivotInv := by
    simpa [hNFull, A0, Gfull, AinvFull] using
      higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa
        hr Ablk pivotInv hpivot hTailPos hApos hRight n hsn hNn
        hLower hTailLocal
  simpa [hNFull, A0, Gfull, AinvFull] using
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_22_product_exact_kappa
      (r := r) hr (hN := hNFull)
      (A0 := A0) (G := Gfull) (Ainv := AinvFull)
      hApos n hchain

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row successor product witness from a tail-local chain plus the direct
    lower-budget comparison.

    This is the Eq.13.23 companion of the preceding lower-comparison wrapper.
    It carries the source-side `rho <= 2` hypothesis for the full first-split
    growth matrix and otherwise uses the direct lower-budget transport route. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa
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
    (hRight :
      IsRightInverse (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)))
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
  dsimp only
  intro hLower hTailLocal
  let hNFull : 0 < r + (m + 1) * r :=
    Nat.add_pos_left hr ((m + 1) * r)
  let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    blockMatrixFirstSplitFlat Ablk
  let Gfull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      hNFull (Nat.succ_pos (m + 1)) hr Ablk pivotInv
  let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    nonsingInv (r + (m + 1) * r) A0
  have hchain :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFull A0 Gfull hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull))
        (growthFactorEntry hNFull A0 Gfull hApos *
          maxEntryNormRect hNFull hNFull A0)
        (m + 1) Ablk pivotInv := by
    simpa [hNFull, A0, Gfull, AinvFull] using
      higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa
        hr Ablk pivotInv hpivot hTailPos hApos hRight n hsn hNn
        hLower hTailLocal
  simpa [hNFull, A0, Gfull, AinvFull] using
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_23_product_exact_kappa
      (r := r) hr (hN := hNFull)
      (A0 := A0) (G := Gfull) (Ainv := AinvFull)
      hApos n hchain (by simpa [hNFull, A0, Gfull] using hRho_le_two)

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    determinant-nonzero bridge for the first-split flat matrix.

    This removes the auxiliary right-inverse certificate from source-facing
    exact-κ wrappers when nonsingularity is supplied as `det A ≠ 0`. -/
theorem higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero
    {m r : ℕ}
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ)
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat Ablk :
        Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0) :
    IsRightInverse (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)
      (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)) :=
  (isInverse_nonsingInv_of_det_ne_zero
    (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk) hdet).2

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    determinant-nonzero variant of the first-split exact-κ successor chain.

    The conclusion is identical to
    `higham13_eq13_22_blockLUBudgetChain_succ_from_matrix_stage_history_first_split_exact_kappa`,
    but the right-inverse premise is derived from `det A ≠ 0`. -/
theorem
    higham13_eq13_22_blockLUBudgetChain_succ_from_matrix_stage_history_first_split_exact_kappa_of_det_ne_zero
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
      (m + 1) Ablk pivotInv := by
  exact
    higham13_eq13_22_blockLUBudgetChain_succ_from_matrix_stage_history_first_split_exact_kappa
      hr hN Ablk pivotInv hpivot hApos
      (higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero Ablk hdet)
      n hsn hNn hTail

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    uniform-flat determinant-nonzero exact-κ successor chain constructor.

    This is the source-facing successor version of the first-split exact-κ
    constructor.  Its budgets are stated against the uniform flattened source
    matrix `blockMatrixFlatFin Ablk`; the proof uses the first-split local
    lower-left bridge only internally and then transports that lower budget to
    the uniform flat representation.  The recursive tail chain is still an
    explicit hypothesis. -/
theorem
    higham13_eq13_22_blockLUBudgetChain_succ_from_flat_matrix_stage_history_exact_kappa_of_det_ne_zero
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
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFull A0 G hApos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull Ainv))
        (growthFactorEntry hNFull A0 G hApos *
          maxEntryNormRect hNFull hNFull A0)
        (m + 1) Ablk pivotInv := by
  dsimp only
  intro hTail
  let hmTail : 0 < m + 1 := Nat.succ_pos m
  let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  let hNFull : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
  let hNSplit : 0 < r + (m + 1) * r := Nat.add_pos_left hr ((m + 1) * r)
  let A0 : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    blockMatrixFlatFin Ablk
  let G : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      hNFull hmFull hr Ablk pivotInv
  let Ainv : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    nonsingInv (((m + 1) + 1) * r) A0
  let rho : ℝ := growthFactorEntry hNFull A0 G
    (maxEntryNorm_pos_of_det_ne_zero hNFull A0 hdetFlat)
  let kappaA : ℝ := maxEntryNormRect hNFull hNFull A0 *
    maxEntryNormRect hNFull hNFull Ainv
  let normA : ℝ := maxEntryNormRect hNFull hNFull A0
  have hApos : 0 < maxEntryNorm hNFull A0 :=
    maxEntryNorm_pos_of_det_ne_zero hNFull A0 hdetFlat
  have hRight : IsRightInverse (((m + 1) + 1) * r) A0 Ainv := by
    simpa [A0, Ainv] using
      (isInverse_nonsingInv_of_det_ne_zero (((m + 1) + 1) * r) A0 hdetFlat).2
  have hA_le_G : maxEntryNorm hNFull A0 ≤ maxEntryNorm hNFull G := by
    simpa [hNFull, hmFull, A0, G] using
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_flat_initial
        hmFull hr Ablk pivotInv
  have hId : 1 ≤ (n : ℝ) * rho ^ 2 * kappaA := by
    simpa [rho, kappaA, A0, G, Ainv, hApos] using
      higham13_eq13_22_lower_diagonal_budget_from_right_inverse_growth
        hNFull A0 G Ainv hApos hRight n hNn hA_le_G
  have hSplitPos :
      0 < maxEntryNorm hNSplit (blockMatrixFirstSplitFlat Ablk) := by
    rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin hmTail hr Ablk]
    exact hApos
  have hL21_firstSplit :
      maxEntryNormRect (Nat.mul_pos hmTail hr) hr
          ((blockMatrixFirstSplitA21 Ablk * pivotInv 0 :
            Matrix (Fin ((m + 1) * r)) (Fin r) ℝ)) ≤
        (n : ℝ) *
          (growthFactorEntry hNSplit (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hNSplit hmFull hr Ablk pivotInv) hSplitPos) ^ 2 *
          (maxEntryNormRect hNSplit hNSplit (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hNSplit hNSplit
              (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) := by
    simpa [hNSplit, hmFull, hpivot] using
      higham13_problem13_4_L21_eq13_22_premise_from_matrix_stage_history_first_split_exact_kappa
        hmTail hr hNSplit Ablk pivotInv hpivot hSplitPos n hsn
  have hLowerBridge :
      (n : ℝ) *
          (growthFactorEntry hNSplit (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hNSplit hmFull hr Ablk pivotInv) hSplitPos) ^ 2 *
          (maxEntryNormRect hNSplit hNSplit (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hNSplit hNSplit
              (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))) ≤
        (n : ℝ) * rho ^ 2 * kappaA := by
    simpa [hNSplit, hNFull, hmFull, A0, G, Ainv, rho, kappaA, hApos, hSplitPos] using
      higham13_eq13_22_firstSplit_lower_budget_le_flat_matrix_stage_history_exact_kappa
        hmTail hr Ablk pivotInv hdetFlat n
  have hL21 :
      maxEntryNormRect (Nat.mul_pos hmTail hr) hr
          ((blockMatrixFirstSplitA21 Ablk * pivotInv 0 :
            Matrix (Fin ((m + 1) * r)) (Fin r) ℝ)) ≤
        (n : ℝ) * rho ^ 2 * kappaA :=
    le_trans hL21_firstSplit hLowerBridge
  have hU_le_G : blockMaxNorm hmFull hr Ablk ≤ maxEntryNorm hNFull G := by
    rw [← maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm hmFull hr Ablk]
    simpa [A0, G] using hA_le_G
  have hInput : blockMaxNorm hmFull hr Ablk ≤ rho * normA := by
    simpa [rho, normA, A0, G, hApos] using
      blockMaxNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm
        hNFull hmFull hr A0 G Ablk hApos hU_le_G
  have hFirstRow :
      ∀ j : Fin ((m + 1) + 1), maxEntryNorm hr (Ablk 0 j) ≤ rho * normA := by
    intro j
    exact le_trans (block_le_blockMaxNorm hmFull hr Ablk 0 j) hInput
  simpa [hNFull, hmFull, A0, G, Ainv, rho, kappaA, normA, hApos] using
    (Higham13BlockLUBudgetChain.succ (hr := hr)
      (C_L := (n : ℝ) * rho ^ 2 * kappaA)
      (C_U := rho * normA)
      (A := Ablk) (pivotInv := pivotInv)
      hpivot hId hL21 hFirstRow hTail)

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    uniform-flat determinant-nonzero successor chain from a tail-local chain
    plus the direct lower-budget comparison.

    This composes the new flat tail-budget transport with the uniform-flat
    successor constructor, so the remaining scalar source obligation is the
    direct lower comparison rather than a first-split representation artifact. -/
theorem
    higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero
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
    (hdetFlat :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (((m + 1) + 1) * r)) (Fin (((m + 1) + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNSplit : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
    let hNFlat : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let ASplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let GSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNSplit hmFull hr Ablk pivotInv
    let AinvSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) ASplit
    let A0 : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      blockMatrixFlatFin Ablk
    let G : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFlat hmFull hr Ablk pivotInv
    let Ainv : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      nonsingInv (((m + 1) + 1) * r) A0
    let hApos : 0 < maxEntryNorm hNFlat A0 :=
      maxEntryNorm_pos_of_det_ne_zero hNFlat A0 hdetFlat
    let hSplitPos : 0 < maxEntryNorm hNSplit ASplit := by
      rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin hmTail hr Ablk]
      exact hApos
    ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail) ≤
        (n : ℝ) * (growthFactorEntry hNSplit ASplit GSplit hSplitPos) ^ 2 *
          (maxEntryNormRect hNSplit hNSplit ASplit *
            maxEntryNormRect hNSplit hNSplit AinvSplit)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFlat A0 G hApos) ^ 2 *
          (maxEntryNormRect hNFlat hNFlat A0 *
            maxEntryNormRect hNFlat hNFlat Ainv))
        (growthFactorEntry hNFlat A0 G hApos *
          maxEntryNormRect hNFlat hNFlat A0)
        (m + 1) Ablk pivotInv := by
  dsimp only
  intro hLower hTailLocal
  let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  let hNFlat : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
  let A0 : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    blockMatrixFlatFin Ablk
  let G : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      hNFlat hmFull hr Ablk pivotInv
  let Ainv : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    nonsingInv (((m + 1) + 1) * r) A0
  let hApos : 0 < maxEntryNorm hNFlat A0 :=
    maxEntryNorm_pos_of_det_ne_zero hNFlat A0 hdetFlat
  have hTailFlat :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFlat A0 G hApos) ^ 2 *
          (maxEntryNormRect hNFlat hNFlat A0 *
            maxEntryNormRect hNFlat hNFlat Ainv))
        (growthFactorEntry hNFlat A0 G hApos *
          maxEntryNormRect hNFlat hNFlat A0)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) := by
    simpa [hmFull, hNFlat, A0, G, Ainv, hApos] using
      higham13_eq13_22_tail_chain_to_flat_budget_from_lower_comparison_matrix_stage_history_exact_kappa_of_det_ne_zero
        hr Ablk pivotInv hTailPos hdetFlat n hLower hTailLocal
  simpa [hmFull, hNFlat, A0, G, Ainv, hApos] using
    higham13_eq13_22_blockLUBudgetChain_succ_from_flat_matrix_stage_history_exact_kappa_of_det_ne_zero
      hr Ablk pivotInv hpivot hdetFlat n hsn hNn hTailFlat

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    uniform-flat determinant-nonzero successor chain from a tail-local chain
    plus the inverse-ratio comparison.

    This is the inverse-ratio companion to
    `higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero`:
    the proved tail-history domination first converts the inverse-ratio
    hypothesis into the direct lower-budget comparison, then the existing
    uniform-flat successor bridge removes the first-split representation
    artifact. -/
theorem
    higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_inverse_ratio_flat_matrix_stage_history_exact_kappa_of_det_ne_zero
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
    (hdetFlat :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (((m + 1) + 1) * r)) (Fin (((m + 1) + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNSplit : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
    let hNFlat : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let ASplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let AinvSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) ASplit
    let A0 : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      blockMatrixFlatFin Ablk
    let G : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFlat hmFull hr Ablk pivotInv
    let Ainv : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      nonsingInv (((m + 1) + 1) * r) A0
    let hApos : 0 < maxEntryNorm hNFlat A0 :=
      maxEntryNorm_pos_of_det_ne_zero hNFlat A0 hdetFlat
    (maxEntryNormRect hNTail hNTail AinvTail *
          maxEntryNormRect hNSplit hNSplit ASplit ≤
        maxEntryNormRect hNSplit hNSplit AinvSplit *
          maxEntryNormRect hNTail hNTail Atail) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFlat A0 G hApos) ^ 2 *
          (maxEntryNormRect hNFlat hNFlat A0 *
            maxEntryNormRect hNFlat hNFlat Ainv))
        (growthFactorEntry hNFlat A0 G hApos *
          maxEntryNormRect hNFlat hNFlat A0)
        (m + 1) Ablk pivotInv := by
  dsimp only
  intro hInvRatio hTailLocal
  let hmTail : 0 < m + 1 := Nat.succ_pos m
  let hNSplit : 0 < r + (m + 1) * r :=
    Nat.add_pos_left hr ((m + 1) * r)
  let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  let hNFlat : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
  let A0 : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    blockMatrixFlatFin Ablk
  let hApos : 0 < maxEntryNorm hNFlat A0 :=
    maxEntryNorm_pos_of_det_ne_zero hNFlat A0 hdetFlat
  let hSplitPos : 0 < maxEntryNorm hNSplit (blockMatrixFirstSplitFlat Ablk) := by
    rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin hmTail hr Ablk]
    exact hApos
  have hLower :
      (n : ℝ) *
          (growthFactorEntry (Nat.mul_pos hmTail hr)
            (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0)))
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos hmTail hr) hmTail hr
              (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)))
            hTailPos) ^ 2 *
          (maxEntryNormRect (Nat.mul_pos hmTail hr)
            (Nat.mul_pos hmTail hr)
            (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))) *
            maxEntryNormRect (Nat.mul_pos hmTail hr)
              (Nat.mul_pos hmTail hr)
              (nonsingInv ((m + 1) * r)
                (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))))) ≤
        (n : ℝ) *
          (growthFactorEntry hNSplit (blockMatrixFirstSplitFlat Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hNSplit hmFull hr Ablk pivotInv) hSplitPos) ^ 2 *
          (maxEntryNormRect hNSplit hNSplit (blockMatrixFirstSplitFlat Ablk) *
            maxEntryNormRect hNSplit hNSplit
              (nonsingInv (r + (m + 1) * r)
                (blockMatrixFirstSplitFlat Ablk))) := by
    simpa [hmTail, hNSplit, hmFull, hSplitPos] using
      higham13_eq13_22_tail_lower_budget_le_full_from_inverse_ratio_matrix_stage_history_exact_kappa
        hr Ablk pivotInv hTailPos hSplitPos n hInvRatio
  simpa [hmTail, hNSplit, hmFull, hNFlat, A0, hApos, hSplitPos] using
    higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero
      hr Ablk pivotInv hpivot hTailPos hdetFlat n hsn hNn hLower hTailLocal

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    uniform-flat determinant-nonzero successor product witness from a
    tail-local chain plus the direct lower-budget comparison. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero
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
    (hdetFlat :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (((m + 1) + 1) * r)) (Fin (((m + 1) + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNSplit : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
    let hNFlat : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let ASplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let GSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNSplit hmFull hr Ablk pivotInv
    let AinvSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) ASplit
    let A0 : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      blockMatrixFlatFin Ablk
    let G : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFlat hmFull hr Ablk pivotInv
    let Ainv : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      nonsingInv (((m + 1) + 1) * r) A0
    let hApos : 0 < maxEntryNorm hNFlat A0 :=
      maxEntryNorm_pos_of_det_ne_zero hNFlat A0 hdetFlat
    let hSplitPos : 0 < maxEntryNorm hNSplit ASplit := by
      rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin hmTail hr Ablk]
      exact hApos
    ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail) ≤
        (n : ℝ) * (growthFactorEntry hNSplit ASplit GSplit hSplitPos) ^ 2 *
          (maxEntryNormRect hNSplit hNSplit ASplit *
            maxEntryNormRect hNSplit hNSplit AinvSplit)) →
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
            (n : ℝ) * (growthFactorEntry hNFlat A0 G hApos) ^ 3 *
              (maxEntryNormRect hNFlat hNFlat A0 *
                maxEntryNormRect hNFlat hNFlat Ainv) *
              maxEntryNormRect hNFlat hNFlat A0 := by
  dsimp only
  intro hLower hTailLocal
  let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  let hNFlat : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
  let A0 : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    blockMatrixFlatFin Ablk
  let G : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      hNFlat hmFull hr Ablk pivotInv
  let Ainv : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    nonsingInv (((m + 1) + 1) * r) A0
  let hApos : 0 < maxEntryNorm hNFlat A0 :=
    maxEntryNorm_pos_of_det_ne_zero hNFlat A0 hdetFlat
  have hchain :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFlat A0 G hApos) ^ 2 *
          (maxEntryNormRect hNFlat hNFlat A0 *
            maxEntryNormRect hNFlat hNFlat Ainv))
        (growthFactorEntry hNFlat A0 G hApos *
          maxEntryNormRect hNFlat hNFlat A0)
        (m + 1) Ablk pivotInv := by
    simpa [hmFull, hNFlat, A0, G, Ainv, hApos] using
      higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero
        hr Ablk pivotInv hpivot hTailPos hdetFlat n hsn hNn hLower hTailLocal
  simpa [hmFull, hNFlat, A0, G, Ainv, hApos] using
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_22_product_exact_kappa
      (r := r) hr (hN := hNFlat) (A0 := A0) (G := G) (Ainv := Ainv)
      hApos n hchain

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    uniform-flat determinant-nonzero point-row successor product witness from a
    tail-local chain plus the direct lower-budget comparison. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero
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
    (hdetFlat :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (((m + 1) + 1) * r)) (Fin (((m + 1) + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNSplit : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
    let hNFlat : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let ASplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let GSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNSplit hmFull hr Ablk pivotInv
    let AinvSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) ASplit
    let A0 : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      blockMatrixFlatFin Ablk
    let G : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFlat hmFull hr Ablk pivotInv
    let Ainv : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      nonsingInv (((m + 1) + 1) * r) A0
    let hApos : 0 < maxEntryNorm hNFlat A0 :=
      maxEntryNorm_pos_of_det_ne_zero hNFlat A0 hdetFlat
    let hSplitPos : 0 < maxEntryNorm hNSplit ASplit := by
      rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin hmTail hr Ablk]
      exact hApos
    growthFactorEntry hNFlat A0 G hApos ≤ 2 →
      ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
            (maxEntryNormRect hNTail hNTail Atail *
              maxEntryNormRect hNTail hNTail AinvTail) ≤
          (n : ℝ) * (growthFactorEntry hNSplit ASplit GSplit hSplitPos) ^ 2 *
            (maxEntryNormRect hNSplit hNSplit ASplit *
              maxEntryNormRect hNSplit hNSplit AinvSplit)) →
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
                (maxEntryNormRect hNFlat hNFlat A0 *
                  maxEntryNormRect hNFlat hNFlat Ainv) *
                maxEntryNormRect hNFlat hNFlat A0 := by
  dsimp only
  intro hRho_le_two hLower hTailLocal
  let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  let hNFlat : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
  let A0 : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    blockMatrixFlatFin Ablk
  let G : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      hNFlat hmFull hr Ablk pivotInv
  let Ainv : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    nonsingInv (((m + 1) + 1) * r) A0
  let hApos : 0 < maxEntryNorm hNFlat A0 :=
    maxEntryNorm_pos_of_det_ne_zero hNFlat A0 hdetFlat
  have hchain :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFlat A0 G hApos) ^ 2 *
          (maxEntryNormRect hNFlat hNFlat A0 *
            maxEntryNormRect hNFlat hNFlat Ainv))
        (growthFactorEntry hNFlat A0 G hApos *
          maxEntryNormRect hNFlat hNFlat A0)
        (m + 1) Ablk pivotInv := by
    simpa [hmFull, hNFlat, A0, G, Ainv, hApos] using
      higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero
        hr Ablk pivotInv hpivot hTailPos hdetFlat n hsn hNn hLower hTailLocal
  simpa [hmFull, hNFlat, A0, G, Ainv, hApos] using
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_23_product_exact_kappa
      (r := r) hr (hN := hNFlat) (A0 := A0) (G := G) (Ainv := Ainv)
      hApos n hchain hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    uniform-flat tail-budget transport with the Schur-tail denominator
    positivity derived from first-split Schur-complement invertibility. -/
theorem
    higham13_eq13_22_tail_chain_to_flat_budget_from_lower_comparison_matrix_stage_history_exact_kappa_of_det_ne_zero_of_schur_invertible
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk))
    (hdetFlat :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (((m + 1) + 1) * r)) (Fin (((m + 1) + 1) * r)) ℝ) ≠ 0)
    (n : ℕ) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNSplit : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
    let hNFlat : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let ASplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let GSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNSplit hmFull hr Ablk pivotInv
    let AinvSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) ASplit
    let A0 : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      blockMatrixFlatFin Ablk
    let G : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFlat hmFull hr Ablk pivotInv
    let Ainv : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      nonsingInv (((m + 1) + 1) * r) A0
    let hTailPos : 0 < maxEntryNorm hNTail Atail :=
      maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
        hr Ablk pivotInv hpivot
    let hApos : 0 < maxEntryNorm hNFlat A0 :=
      maxEntryNorm_pos_of_det_ne_zero hNFlat A0 hdetFlat
    let hSplitPos : 0 < maxEntryNorm hNSplit ASplit := by
      rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin hmTail hr Ablk]
      exact hApos
    ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail) ≤
        (n : ℝ) * (growthFactorEntry hNSplit ASplit GSplit hSplitPos) ^ 2 *
          (maxEntryNormRect hNSplit hNSplit ASplit *
            maxEntryNormRect hNSplit hNSplit AinvSplit)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFlat A0 G hApos) ^ 2 *
          (maxEntryNormRect hNFlat hNFlat A0 *
            maxEntryNormRect hNFlat hNFlat Ainv))
        (growthFactorEntry hNFlat A0 G hApos *
          maxEntryNormRect hNFlat hNFlat A0)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) := by
  dsimp only
  intro hLower hTailLocal
  let hTailPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))) :=
    maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
      hr Ablk pivotInv hpivot
  simpa [hTailPos] using
    higham13_eq13_22_tail_chain_to_flat_budget_from_lower_comparison_matrix_stage_history_exact_kappa_of_det_ne_zero
      hr Ablk pivotInv hTailPos hdetFlat n hLower hTailLocal

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    uniform-flat successor chain from a tail-local chain and the direct
    lower-budget comparison, with tail positivity derived from Schur
    invertibility instead of supplied as a separate hypothesis. -/
theorem
    higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero_of_schur_invertible
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
    (hdetFlat :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (((m + 1) + 1) * r)) (Fin (((m + 1) + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNSplit : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
    let hNFlat : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let ASplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let GSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNSplit hmFull hr Ablk pivotInv
    let AinvSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) ASplit
    let A0 : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      blockMatrixFlatFin Ablk
    let G : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFlat hmFull hr Ablk pivotInv
    let Ainv : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      nonsingInv (((m + 1) + 1) * r) A0
    let hTailPos : 0 < maxEntryNorm hNTail Atail :=
      maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
        hr Ablk pivotInv hpivot
    let hApos : 0 < maxEntryNorm hNFlat A0 :=
      maxEntryNorm_pos_of_det_ne_zero hNFlat A0 hdetFlat
    let hSplitPos : 0 < maxEntryNorm hNSplit ASplit := by
      rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin hmTail hr Ablk]
      exact hApos
    ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail) ≤
        (n : ℝ) * (growthFactorEntry hNSplit ASplit GSplit hSplitPos) ^ 2 *
          (maxEntryNormRect hNSplit hNSplit ASplit *
            maxEntryNormRect hNSplit hNSplit AinvSplit)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFlat A0 G hApos) ^ 2 *
          (maxEntryNormRect hNFlat hNFlat A0 *
            maxEntryNormRect hNFlat hNFlat Ainv))
        (growthFactorEntry hNFlat A0 G hApos *
          maxEntryNormRect hNFlat hNFlat A0)
        (m + 1) Ablk pivotInv := by
  dsimp only
  intro hLower hTailLocal
  let hTailPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))) :=
    maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
      hr Ablk pivotInv hpivot
  simpa [hTailPos] using
    higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero
      hr Ablk pivotInv hpivot hTailPos hdetFlat n hsn hNn hLower hTailLocal

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    concrete Eq.13.22 product witness from a tail-local chain and direct lower
    comparison, deriving Schur-tail positivity from the source invertibility
    assumptions. -/
theorem
    higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero_of_schur_invertible
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
    (hdetFlat :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (((m + 1) + 1) * r)) (Fin (((m + 1) + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNSplit : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
    let hNFlat : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let ASplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let GSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNSplit hmFull hr Ablk pivotInv
    let AinvSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) ASplit
    let A0 : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      blockMatrixFlatFin Ablk
    let G : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFlat hmFull hr Ablk pivotInv
    let Ainv : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      nonsingInv (((m + 1) + 1) * r) A0
    let hTailPos : 0 < maxEntryNorm hNTail Atail :=
      maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
        hr Ablk pivotInv hpivot
    let hApos : 0 < maxEntryNorm hNFlat A0 :=
      maxEntryNorm_pos_of_det_ne_zero hNFlat A0 hdetFlat
    let hSplitPos : 0 < maxEntryNorm hNSplit ASplit := by
      rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin hmTail hr Ablk]
      exact hApos
    ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail) ≤
        (n : ℝ) * (growthFactorEntry hNSplit ASplit GSplit hSplitPos) ^ 2 *
          (maxEntryNormRect hNSplit hNSplit ASplit *
            maxEntryNormRect hNSplit hNSplit AinvSplit)) →
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
            (n : ℝ) * (growthFactorEntry hNFlat A0 G hApos) ^ 3 *
              (maxEntryNormRect hNFlat hNFlat A0 *
                maxEntryNormRect hNFlat hNFlat Ainv) *
              maxEntryNormRect hNFlat hNFlat A0 := by
  dsimp only
  intro hLower hTailLocal
  let hTailPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))) :=
    maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
      hr Ablk pivotInv hpivot
  simpa [hTailPos] using
    higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero
      hr Ablk pivotInv hpivot hTailPos hdetFlat n hsn hNn hLower hTailLocal

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    concrete point-row Eq.13.23 product witness from a tail-local chain and
    direct lower comparison, deriving Schur-tail positivity from the source
    invertibility assumptions. -/
theorem
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero_of_schur_invertible
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
    (hdetFlat :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (((m + 1) + 1) * r)) (Fin (((m + 1) + 1) * r)) ℝ) ≠ 0)
    (n : ℕ)
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hNn : ((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNSplit : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
    let hNFlat : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let ASplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat Ablk
    let GSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNSplit hmFull hr Ablk pivotInv
    let AinvSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) ASplit
    let A0 : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      blockMatrixFlatFin Ablk
    let G : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFlat hmFull hr Ablk pivotInv
    let Ainv : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      nonsingInv (((m + 1) + 1) * r) A0
    let hTailPos : 0 < maxEntryNorm hNTail Atail :=
      maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
        hr Ablk pivotInv hpivot
    let hApos : 0 < maxEntryNorm hNFlat A0 :=
      maxEntryNorm_pos_of_det_ne_zero hNFlat A0 hdetFlat
    let hSplitPos : 0 < maxEntryNorm hNSplit ASplit := by
      rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin hmTail hr Ablk]
      exact hApos
    growthFactorEntry hNFlat A0 G hApos ≤ 2 →
      ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
            (maxEntryNormRect hNTail hNTail Atail *
              maxEntryNormRect hNTail hNTail AinvTail) ≤
          (n : ℝ) * (growthFactorEntry hNSplit ASplit GSplit hSplitPos) ^ 2 *
            (maxEntryNormRect hNSplit hNSplit ASplit *
              maxEntryNormRect hNSplit hNSplit AinvSplit)) →
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
                (maxEntryNormRect hNFlat hNFlat A0 *
                  maxEntryNormRect hNFlat hNFlat Ainv) *
                maxEntryNormRect hNFlat hNFlat A0 := by
  dsimp only
  intro hRho_le_two hLower hTailLocal
  let hTailPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))) :=
    maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
      hr Ablk pivotInv hpivot
  simpa [hTailPos] using
    higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero
      hr Ablk pivotInv hpivot hTailPos hdetFlat n hsn hNn
      hRho_le_two hLower hTailLocal

end NumStability
