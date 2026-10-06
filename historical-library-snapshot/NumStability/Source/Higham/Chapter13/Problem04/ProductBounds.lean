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
import NumStability.Source.Higham.Chapter13.Equation22
import NumStability.Source.Higham.Chapter13.Equation23
import NumStability.Source.Higham.Chapter13.Problem04.ActiveStageBounds
import NumStability.Source.Higham.Chapter13.Problem04.BlockInverseBounds
import NumStability.Source.Higham.Chapter13.Problem04.LocalGrowth
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStages
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis

/-!
# Source.Higham.Chapter13.Problem04.ProductBounds

This module formalizes the source-facing Chapter 13 statements for
`Problem04.ProductBounds`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, equations (13.21)--(13.22):
    local source-facing product bridge using one common max-entry growth
    object.

    The theorem combines the Problem 13.4 lower-block premise with the
    equation (13.21) upper-factor premise when the same growth matrix `G`
    contains the initial matrix, the current Schur complement, and the upper
    factor being multiplied.  It is local to one Schur step; the recursive GE
    bookkeeping that supplies those containments remains explicit. -/
theorem higham13_eq13_22_local_product_from_source_growthFactorEntry_exact_kappa
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hN : 0 < r + s)
    (A G Ufac : Fin (r + s) → Fin (r + s) → ℝ)
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
    (hA_le_G : maxEntryNorm hN A ≤ maxEntryNorm hN G)
    (hS_le_G :
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) ≤
        maxEntryNorm hN G)
    (hU_le_G : maxEntryNorm hN Ufac ≤ maxEntryNorm hN G) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) *
        maxEntryNorm hN Ufac ≤
      (n : ℝ) * (growthFactorEntry hN A G hApos) ^ 3 *
        (maxEntryNormRect hN hN A *
          maxEntryNormRect hN hN (nonsingInv (r + s) A)) *
        maxEntryNormRect hN hN A := by
  let rho : ℝ := growthFactorEntry hN A G hApos
  let kappaA : ℝ :=
    maxEntryNormRect hN hN A *
      maxEntryNormRect hN hN (nonsingInv (r + s) A)
  have hL :
      maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
        (n : ℝ) * rho ^ 2 * kappaA := by
    simpa [rho, kappaA] using
      higham13_problem13_4_L21_eq13_22_premise_from_source_growthFactorEntry_exact_kappa
        hr hs hN A G A11 A12 A21 A22
        hA11_block hA12_block hA21_block hA22_block
        hApos n hsn hA_le_G hS_le_G
  have hU :
      maxEntryNorm hN Ufac ≤ rho * maxEntryNormRect hN hN A := by
    simpa [rho] using
      maxEntryNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm
        hN A G Ufac hApos hU_le_G
  have hrho_nonneg : 0 ≤ rho := by
    simpa [rho] using growthFactorEntry_nonneg hN A G hApos
  have hkappa_nonneg : 0 ≤ kappaA := by
    exact mul_nonneg (maxEntryNormRect_nonneg hN hN A)
      (maxEntryNormRect_nonneg hN hN (nonsingInv (r + s) A))
  exact
    block_lu_normLU_bound_general_higham_13_22
      (maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)))
      (maxEntryNorm hN Ufac)
      (maxEntryNormRect hN hN A)
      rho kappaA n
      (maxEntryNorm_nonneg hN Ufac)
      hrho_nonneg hkappa_nonneg hL hU

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    local source-facing point-row product bridge from the common growth-object
    form of equation (13.22) and the additional source hypothesis `ρ_n <= 2`.

    As with
    `higham13_eq13_22_local_product_from_source_growthFactorEntry_exact_kappa`,
    this records the exact scalar consequence while keeping the recursive
    growth-object containments and the `ρ_n <= 2` row-dominance theorem
    explicit. -/
theorem higham13_eq13_23_local_product_from_source_growthFactorEntry_exact_kappa
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hN : 0 < r + s)
    (A G Ufac : Fin (r + s) → Fin (r + s) → ℝ)
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
    (hA_le_G : maxEntryNorm hN A ≤ maxEntryNorm hN G)
    (hS_le_G :
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) ≤
        maxEntryNorm hN G)
    (hU_le_G : maxEntryNorm hN Ufac ≤ maxEntryNorm hN G)
    (hRho_le_two : growthFactorEntry hN A G hApos ≤ 2) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) *
        maxEntryNorm hN Ufac ≤
      8 * (n : ℝ) *
        (maxEntryNormRect hN hN A *
          maxEntryNormRect hN hN (nonsingInv (r + s) A)) *
        maxEntryNormRect hN hN A := by
  let rho : ℝ := growthFactorEntry hN A G hApos
  let kappaA : ℝ :=
    maxEntryNormRect hN hN A *
      maxEntryNormRect hN hN (nonsingInv (r + s) A)
  have hL :
      maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
        (n : ℝ) * rho ^ 2 * kappaA := by
    simpa [rho, kappaA] using
      higham13_problem13_4_L21_eq13_22_premise_from_source_growthFactorEntry_exact_kappa
        hr hs hN A G A11 A12 A21 A22
        hA11_block hA12_block hA21_block hA22_block
        hApos n hsn hA_le_G hS_le_G
  have hU :
      maxEntryNorm hN Ufac ≤ rho * maxEntryNormRect hN hN A := by
    simpa [rho] using
      maxEntryNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm
        hN A G Ufac hApos hU_le_G
  have hrho_nonneg : 0 ≤ rho := by
    simpa [rho] using growthFactorEntry_nonneg hN A G hApos
  have hkappa_nonneg : 0 ≤ kappaA := by
    exact mul_nonneg (maxEntryNormRect_nonneg hN hN A)
      (maxEntryNormRect_nonneg hN hN (nonsingInv (r + s) A))
  exact
    higham13_eq13_23_point_row_from_growth
      (maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)))
      (maxEntryNorm hN Ufac)
      (maxEntryNormRect hN hN A)
      rho kappaA n
      (maxEntryNorm_nonneg hN Ufac)
      (maxEntryNormRect_nonneg hN hN A)
      hrho_nonneg
      (by simpa [rho] using hRho_le_two)
      hkappa_nonneg hL hU

/-- Higham, 2nd ed., Chapter 13, equations (13.21)--(13.22):
    local source-facing product bridge with a block upper factor.

    This is the block-norm version of
    `higham13_eq13_22_local_product_from_source_growthFactorEntry_exact_kappa`.
    The lower-left factor is the local Problem 13.4 block, while the upper
    factor may be an Algorithm 13.3 block upper factor.  The remaining recursive
    GE bookkeeping is the containment hypothesis saying that this block upper
    factor is included in the same max-entry growth object `G`. -/
theorem higham13_eq13_22_local_block_product_from_source_growthFactorEntry_exact_kappa
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
    (hA_le_G : maxEntryNorm hN A ≤ maxEntryNorm hN G)
    (hS_le_G :
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) ≤
        maxEntryNorm hN G)
    (hU_le_G : blockMaxNorm hmb hrb Ufac ≤ maxEntryNorm hN G) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) *
        blockMaxNorm hmb hrb Ufac ≤
      (n : ℝ) * (growthFactorEntry hN A G hApos) ^ 3 *
        (maxEntryNormRect hN hN A *
          maxEntryNormRect hN hN (nonsingInv (r + s) A)) *
        maxEntryNormRect hN hN A := by
  let rho : ℝ := growthFactorEntry hN A G hApos
  let kappaA : ℝ :=
    maxEntryNormRect hN hN A *
      maxEntryNormRect hN hN (nonsingInv (r + s) A)
  have hL :
      maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
        (n : ℝ) * rho ^ 2 * kappaA := by
    simpa [rho, kappaA] using
      higham13_problem13_4_L21_eq13_22_premise_from_source_growthFactorEntry_exact_kappa
        hr hs hN A G A11 A12 A21 A22
        hA11_block hA12_block hA21_block hA22_block
        hApos n hsn hA_le_G hS_le_G
  have hU :
      blockMaxNorm hmb hrb Ufac ≤ rho * maxEntryNormRect hN hN A := by
    simpa [rho] using
      blockMaxNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm
        hN hmb hrb A G Ufac hApos hU_le_G
  have hrho_nonneg : 0 ≤ rho := by
    simpa [rho] using growthFactorEntry_nonneg hN A G hApos
  have hkappa_nonneg : 0 ≤ kappaA := by
    exact mul_nonneg (maxEntryNormRect_nonneg hN hN A)
      (maxEntryNormRect_nonneg hN hN (nonsingInv (r + s) A))
  exact
    block_lu_normLU_bound_general_higham_13_22
      (maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)))
      (blockMaxNorm hmb hrb Ufac)
      (maxEntryNormRect hN hN A)
      rho kappaA n
      (blockMaxNorm_nonneg hmb hrb Ufac)
      hrho_nonneg hkappa_nonneg hL hU

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    block-upper-factor specialization of the local point-row product bridge.

    It combines the local Problem 13.4 lower block with a contained block upper
    factor and the additional source condition `ρ_n <= 2`. -/
theorem higham13_eq13_23_local_block_product_from_source_growthFactorEntry_exact_kappa
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
    (hA_le_G : maxEntryNorm hN A ≤ maxEntryNorm hN G)
    (hS_le_G :
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) ≤
        maxEntryNorm hN G)
    (hU_le_G : blockMaxNorm hmb hrb Ufac ≤ maxEntryNorm hN G)
    (hRho_le_two : growthFactorEntry hN A G hApos ≤ 2) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) *
        blockMaxNorm hmb hrb Ufac ≤
      8 * (n : ℝ) *
        (maxEntryNormRect hN hN A *
          maxEntryNormRect hN hN (nonsingInv (r + s) A)) *
        maxEntryNormRect hN hN A := by
  let rho : ℝ := growthFactorEntry hN A G hApos
  let kappaA : ℝ :=
    maxEntryNormRect hN hN A *
      maxEntryNormRect hN hN (nonsingInv (r + s) A)
  have hL :
      maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
        (n : ℝ) * rho ^ 2 * kappaA := by
    simpa [rho, kappaA] using
      higham13_problem13_4_L21_eq13_22_premise_from_source_growthFactorEntry_exact_kappa
        hr hs hN A G A11 A12 A21 A22
        hA11_block hA12_block hA21_block hA22_block
        hApos n hsn hA_le_G hS_le_G
  have hU :
      blockMaxNorm hmb hrb Ufac ≤ rho * maxEntryNormRect hN hN A := by
    simpa [rho] using
      blockMaxNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm
        hN hmb hrb A G Ufac hApos hU_le_G
  have hrho_nonneg : 0 ≤ rho := by
    simpa [rho] using growthFactorEntry_nonneg hN A G hApos
  have hkappa_nonneg : 0 ≤ kappaA := by
    exact mul_nonneg (maxEntryNormRect_nonneg hN hN A)
      (maxEntryNormRect_nonneg hN hN (nonsingInv (r + s) A))
  exact
    higham13_eq13_23_point_row_from_growth
      (maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)))
      (blockMaxNorm hmb hrb Ufac)
      (maxEntryNormRect hN hN A)
      rho kappaA n
      (blockMaxNorm_nonneg hmb hrb Ufac)
      (maxEntryNormRect_nonneg hN hN A)
      hrho_nonneg
      (by simpa [rho] using hRho_le_two)
      hkappa_nonneg hL hU

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    assembled matrix-stage `L*U` product bound from per-stage multiplier
    bounds.

    This is the full-factor matrix-stage lift: the lower factor is
    `higham13_algorithm13_3_lowerFromMatrixStages`, the upper factor is
    `higham13_algorithm13_3_upperFromMatrixStages`, and the remaining
    source-specific obligation is the per-stage multiplier bound supplied by
    Problem 13.4 at every active pivot column. -/
theorem higham13_eq13_22_matrix_stage_product_from_multiplier_bounds
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A0 G : Fin N → Fin N → ℝ)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN A0)
    (n : ℕ) (kappaA : ℝ)
    (hKappa : 0 ≤ kappaA)
    (hId :
      1 ≤ (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hU_le_G :
      blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        maxEntryNorm hN G) :
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 3 * kappaA *
        maxEntryNormRect hN hN A0 := by
  let rho : ℝ := growthFactorEntry hN A0 G hApos
  have hL :
      blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) ≤
        (n : ℝ) * rho ^ 2 * kappaA := by
    exact
      higham13_algorithm13_3_lowerFromMatrixStages_blockMaxNorm_bound
        hm hr Ablk pivotInv
        (by simpa [rho] using hId)
        (by
          intro i j hij
          simpa [rho] using hLower i j hij)
  have hU :
      blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        rho * maxEntryNormRect hN hN A0 := by
    simpa [rho] using
      blockMaxNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm
        hN hm hr A0 G
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv)
        hApos hU_le_G
  have hrho_nonneg : 0 ≤ rho := by
    simpa [rho] using growthFactorEntry_nonneg hN A0 G hApos
  exact
    block_lu_normLU_bound_general_higham_13_22
      (blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv))
      (blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv))
      (maxEntryNormRect hN hN A0)
      rho kappaA n
      (blockMaxNorm_nonneg hm hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv))
      hrho_nonneg hKappa hL hU

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    assembled matrix-stage point-row specialization of the Eq.13.22 product
    lift from per-stage multiplier bounds and `ρ_n <= 2`. -/
theorem higham13_eq13_23_matrix_stage_product_from_multiplier_bounds
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A0 G : Fin N → Fin N → ℝ)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN A0)
    (n : ℕ) (kappaA : ℝ)
    (hKappa : 0 ≤ kappaA)
    (hId :
      1 ≤ (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hU_le_G :
      blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        maxEntryNorm hN G)
    (hRho_le_two : growthFactorEntry hN A0 G hApos ≤ 2) :
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) * kappaA * maxEntryNormRect hN hN A0 := by
  let rho : ℝ := growthFactorEntry hN A0 G hApos
  have hL :
      blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) ≤
        (n : ℝ) * rho ^ 2 * kappaA := by
    exact
      higham13_algorithm13_3_lowerFromMatrixStages_blockMaxNorm_bound
        hm hr Ablk pivotInv
        (by simpa [rho] using hId)
        (by
          intro i j hij
          simpa [rho] using hLower i j hij)
  have hU :
      blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        rho * maxEntryNormRect hN hN A0 := by
    simpa [rho] using
      blockMaxNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm
        hN hm hr A0 G
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv)
        hApos hU_le_G
  have hrho_nonneg : 0 ≤ rho := by
    simpa [rho] using growthFactorEntry_nonneg hN A0 G hApos
  exact
    higham13_eq13_23_point_row_from_growth
      (blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv))
      (blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv))
      (maxEntryNormRect hN hN A0)
      rho kappaA n
      (blockMaxNorm_nonneg hm hr
        (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv))
      (maxEntryNormRect_nonneg hN hN A0)
      hrho_nonneg
      (by simpa [rho] using hRho_le_two)
      hKappa hL hU

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    assembled matrix-stage `BlockLUFactSpec` witness from per-stage multiplier
    bounds.

    This is the witness version of
    `higham13_eq13_22_matrix_stage_product_from_multiplier_bounds`: once the
    assembled matrix-stage factors are known to reconstruct the input, the
    concrete `L` and `U` also satisfy the displayed Eq.13.22 product bound. -/
theorem higham13_eq13_22_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A0 G : Fin N → Fin N → ℝ)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hprod : ∀ (i j : Fin m) (s t : Fin r),
      ∑ k : Fin m, ∑ l : Fin r,
        higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv i k s l *
          higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv k j l t =
        Ablk i j s t)
    (hApos : 0 < maxEntryNorm hN A0)
    (n : ℕ) (kappaA : ℝ)
    (hKappa : 0 ≤ kappaA)
    (hId :
      1 ≤ (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hU_le_G :
      blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        maxEntryNorm hN G) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 3 * kappaA *
            maxEntryNormRect hN hN A0 := by
  let L : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv
  let U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv
  refine ⟨L, U, ?_, ?_⟩
  · simpa [L, U] using
      higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_product_eq
        Ablk pivotInv hprod
  · simpa [L, U] using
      higham13_eq13_22_matrix_stage_product_from_multiplier_bounds
        hN hm hr A0 G Ablk pivotInv hApos n kappaA hKappa hId hLower hU_le_G

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    assembled matrix-stage `BlockLUFactSpec` witness from per-stage multiplier
    bounds and the point-row growth hypothesis `ρ_n <= 2`. -/
theorem higham13_eq13_23_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A0 G : Fin N → Fin N → ℝ)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hprod : ∀ (i j : Fin m) (s t : Fin r),
      ∑ k : Fin m, ∑ l : Fin r,
        higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv i k s l *
          higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv k j l t =
        Ablk i j s t)
    (hApos : 0 < maxEntryNorm hN A0)
    (n : ℕ) (kappaA : ℝ)
    (hKappa : 0 ≤ kappaA)
    (hId :
      1 ≤ (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hU_le_G :
      blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        maxEntryNorm hN G)
    (hRho_le_two : growthFactorEntry hN A0 G hApos ≤ 2) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) * kappaA * maxEntryNormRect hN hN A0 := by
  let L : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv
  let U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv
  refine ⟨L, U, ?_, ?_⟩
  · simpa [L, U] using
      higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_product_eq
        Ablk pivotInv hprod
  · simpa [L, U] using
      higham13_eq13_23_matrix_stage_product_from_multiplier_bounds
        hN hm hr A0 G Ablk pivotInv hApos n kappaA hKappa hId hLower hU_le_G
        hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    assembled matrix-stage `BlockLUFactSpec` witness from per-stage multiplier
    bounds and explicit pivot-left-inverse certificates. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds_of_pivot_left_inverse
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A0 G : Fin N → Fin N → ℝ)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotLeft : ∀ k : ℕ, ∀ hk : k < m,
      IsLeftInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hApos : 0 < maxEntryNorm hN A0)
    (n : ℕ) (kappaA : ℝ)
    (hKappa : 0 ≤ kappaA)
    (hId :
      1 ≤ (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hU_le_G :
      blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        maxEntryNorm hN G) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 3 * kappaA *
            maxEntryNormRect hN hN A0 := by
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds
      hN hm hr A0 G Ablk pivotInv
      (higham13_algorithm13_3_matrixStages_product_eq_of_pivot_left_inverse
        Ablk pivotInv hPivotLeft)
      hApos n kappaA hKappa hId hLower hU_le_G

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    assembled matrix-stage `BlockLUFactSpec` witness from per-stage multiplier
    bounds, explicit pivot-left-inverse certificates, and `ρ_n <= 2`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds_of_pivot_left_inverse
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A0 G : Fin N → Fin N → ℝ)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotLeft : ∀ k : ℕ, ∀ hk : k < m,
      IsLeftInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hApos : 0 < maxEntryNorm hN A0)
    (n : ℕ) (kappaA : ℝ)
    (hKappa : 0 ≤ kappaA)
    (hId :
      1 ≤ (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hU_le_G :
      blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        maxEntryNorm hN G)
    (hRho_le_two : growthFactorEntry hN A0 G hApos ≤ 2) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) * kappaA * maxEntryNormRect hN hN A0 := by
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds
      hN hm hr A0 G Ablk pivotInv
      (higham13_algorithm13_3_matrixStages_product_eq_of_pivot_left_inverse
        Ablk pivotInv hPivotLeft)
      hApos n kappaA hKappa hId hLower hU_le_G hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    assembled matrix-stage `BlockLUFactSpec` witness from per-stage multiplier
    bounds and exact pivot right-inverse certificates. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds_of_pivot_right_inverse
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A0 G : Fin N → Fin N → ℝ)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hApos : 0 < maxEntryNorm hN A0)
    (n : ℕ) (kappaA : ℝ)
    (hKappa : 0 ≤ kappaA)
    (hId :
      1 ≤ (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hU_le_G :
      blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        maxEntryNorm hN G) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 3 * kappaA *
            maxEntryNormRect hN hN A0 := by
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds_of_pivot_left_inverse
      hN hm hr A0 G Ablk pivotInv
      (higham13_algorithm13_3_pivot_left_inverse_of_pivot_right_inverse
        Ablk pivotInv hPivotRight)
      hApos n kappaA hKappa hId hLower hU_le_G

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    assembled matrix-stage `BlockLUFactSpec` witness from per-stage multiplier
    bounds, exact pivot right-inverse certificates, and `ρ_n <= 2`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds_of_pivot_right_inverse
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A0 G : Fin N → Fin N → ℝ)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hApos : 0 < maxEntryNorm hN A0)
    (n : ℕ) (kappaA : ℝ)
    (hKappa : 0 ≤ kappaA)
    (hId :
      1 ≤ (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hU_le_G :
      blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        maxEntryNorm hN G)
    (hRho_le_two : growthFactorEntry hN A0 G hApos ≤ 2) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) * kappaA * maxEntryNormRect hN hN A0 := by
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds_of_pivot_left_inverse
      hN hm hr A0 G Ablk pivotInv
      (higham13_algorithm13_3_pivot_left_inverse_of_pivot_right_inverse
        Ablk pivotInv hPivotRight)
      hApos n kappaA hKappa hId hLower hU_le_G hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    assembled matrix-stage `BlockLUFactSpec` witness from per-stage multiplier
    bounds and canonical active pivots `pivotInv k = nonsingInv pivot_k`.

    This removes the explicit pivot right-inverse certificate from the
    Eq.13.22 product-witness surface once the active pivot determinant table
    and canonical inverse table are supplied. -/
theorem
    higham13_eq13_22_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds_of_pivotInv_eq_nonsingInv
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A0 G : Fin N → Fin N → ℝ)
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
    (hApos : 0 < maxEntryNorm hN A0)
    (n : ℕ) (kappaA : ℝ)
    (hKappa : 0 ≤ kappaA)
    (hId :
      1 ≤ (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hU_le_G :
      blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        maxEntryNorm hN G) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 3 * kappaA *
            maxEntryNormRect hN hN A0 := by
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds_of_pivot_right_inverse
      hN hm hr A0 G Ablk pivotInv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hApos n kappaA hKappa hId hLower hU_le_G

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    assembled matrix-stage `BlockLUFactSpec` witness from per-stage multiplier
    bounds, `ρ_n <= 2`, and canonical active pivots
    `pivotInv k = nonsingInv pivot_k`. -/
theorem
    higham13_eq13_23_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds_of_pivotInv_eq_nonsingInv
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A0 G : Fin N → Fin N → ℝ)
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
    (hApos : 0 < maxEntryNorm hN A0)
    (n : ℕ) (kappaA : ℝ)
    (hKappa : 0 ≤ kappaA)
    (hId :
      1 ≤ (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 * kappaA)
    (hU_le_G :
      blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
        maxEntryNorm hN G)
    (hRho_le_two : growthFactorEntry hN A0 G hApos ≤ 2) :
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) * kappaA * maxEntryNormRect hN hN A0 := by
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds_of_pivot_right_inverse
      hN hm hr A0 G Ablk pivotInv
      (higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv
        Ablk pivotInv hPivotDet hPivotInv)
      hApos n kappaA hKappa hId hLower hU_le_G hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    assembled matrix-stage product bound using the finite matrix-stage history
    as the growth object.

    This specializes
    `higham13_eq13_22_matrix_stage_product_from_multiplier_bounds` by
    discharging the assembled-upper containment with
    `higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_upperFromMatrixStages`. -/
theorem higham13_eq13_22_matrix_stage_history_product_from_multiplier_bounds
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A0 : Fin N → Fin N → ℝ)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN A0)
    (n : ℕ) (kappaA : ℝ)
    (hKappa : 0 ≤ kappaA)
    (hId :
      1 ≤ (n : ℝ) *
        (growthFactorEntry hN A0
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos) ^ 2 * kappaA)
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) *
          (growthFactorEntry hN A0
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN hm hr Ablk pivotInv) hApos) ^ 2 * kappaA) :
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      (n : ℝ) *
        (growthFactorEntry hN A0
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos) ^ 3 * kappaA *
        maxEntryNormRect hN hN A0 := by
  exact
    higham13_eq13_22_matrix_stage_product_from_multiplier_bounds
      hN hm hr A0
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hN hm hr Ablk pivotInv)
      Ablk pivotInv hApos n kappaA hKappa hId hLower
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_upperFromMatrixStages
        hN hm hr Ablk pivotInv)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row specialization of the assembled matrix-stage product bound using
    the finite matrix-stage history as the growth object. -/
theorem higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A0 : Fin N → Fin N → ℝ)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN A0)
    (n : ℕ) (kappaA : ℝ)
    (hKappa : 0 ≤ kappaA)
    (hId :
      1 ≤ (n : ℝ) *
        (growthFactorEntry hN A0
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos) ^ 2 * kappaA)
    (hLower : ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) *
          (growthFactorEntry hN A0
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN hm hr Ablk pivotInv) hApos) ^ 2 * kappaA)
    (hRho_le_two :
      growthFactorEntry hN A0
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos ≤ 2) :
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) * kappaA * maxEntryNormRect hN hN A0 := by
  exact
    higham13_eq13_23_matrix_stage_product_from_multiplier_bounds
      hN hm hr A0
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hN hm hr Ablk pivotInv)
      Ablk pivotInv hApos n kappaA hKappa hId hLower
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_upperFromMatrixStages
        hN hm hr Ablk pivotInv)
      hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ matrix-stage-history product bound for the flattened source block
    matrix.

    Compared with
    `higham13_eq13_22_matrix_stage_history_product_from_multiplier_bounds`,
    this wrapper discharges the diagonal lower-factor budget
    `1 <= nρ^2κ(A)` from a right inverse of the flattened input, the finite
    stage-history containment of that input, and the dimension comparison
    `(m*r : ℝ) <= n`.  The per-stage multiplier bounds remain explicit. -/
theorem higham13_eq13_22_matrix_stage_history_product_from_multiplier_bounds_exact_kappa
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
  let G : Fin (m * r) → Fin (m * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv
  let kappaA : ℝ :=
    maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
      maxEntryNormRect hN hN Ainv
  have hKappa : 0 ≤ kappaA := by
    exact mul_nonneg
      (maxEntryNormRect_nonneg hN hN (blockMatrixFlatFin Ablk))
      (maxEntryNormRect_nonneg hN hN Ainv)
  have hA_le_G : maxEntryNorm hN (blockMatrixFlatFin Ablk) ≤ maxEntryNorm hN G := by
    simpa [hN, G] using
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_flat_initial
        hm hr Ablk pivotInv
  have hId :
      1 ≤ (n : ℝ) * (growthFactorEntry hN (blockMatrixFlatFin Ablk) G hApos) ^ 2 *
        kappaA := by
    exact
      higham13_eq13_22_lower_diagonal_budget_from_right_inverse_growth
        hN (blockMatrixFlatFin Ablk) G Ainv hApos hRight n hNn hA_le_G
  simpa [hN, G, kappaA] using
    higham13_eq13_22_matrix_stage_history_product_from_multiplier_bounds
      hN hm hr (blockMatrixFlatFin Ablk) Ablk pivotInv hApos
      n kappaA hKappa hId
      (by
        intro i j hij
        simpa [hN, G, kappaA] using hLower i j hij)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ specialization of the matrix-stage-history product bound
    for the flattened source block matrix. -/
theorem higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa
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
    (hRho_le_two :
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos ≤ 2) :
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
  have hKappa : 0 ≤ kappaA := by
    exact mul_nonneg
      (maxEntryNormRect_nonneg hN hN (blockMatrixFlatFin Ablk))
      (maxEntryNormRect_nonneg hN hN Ainv)
  have hA_le_G : maxEntryNorm hN (blockMatrixFlatFin Ablk) ≤ maxEntryNorm hN G := by
    simpa [hN, G] using
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_flat_initial
        hm hr Ablk pivotInv
  have hId :
      1 ≤ (n : ℝ) * (growthFactorEntry hN (blockMatrixFlatFin Ablk) G hApos) ^ 2 *
        kappaA := by
    exact
      higham13_eq13_22_lower_diagonal_budget_from_right_inverse_growth
        hN (blockMatrixFlatFin Ablk) G Ainv hApos hRight n hNn hA_le_G
  simpa [hN, G, kappaA] using
    higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds
      hN hm hr (blockMatrixFlatFin Ablk) Ablk pivotInv hApos
      n kappaA hKappa hId
      (by
        intro i j hij
        simpa [hN, G, kappaA] using hLower i j hij)
      (by simpa [hN, G] using hRho_le_two)

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 feeding equation (13.22):
    per-stage matrix-product multiplier bounds from source-shaped local
    lower-block budgets.

    This is the source-shaped alternative to assuming the final squared
    ambient multiplier budget directly.  For every active multiplier block, it
    accepts a local lower-block estimate of the form
    `r * rhoLocal * kappaLocal`, together with the book's scalar comparisons
    `rhoLocal <= rhoFull` and `kappaLocal <= rhoFull * kappaFull`, and returns
    the exact per-stage hypothesis consumed by the matrix-stage Eq.13.22 and
    Eq.13.23 product wrappers. -/
theorem higham13_algorithm13_3_multiplier_bounds_from_source_lblock_budgets_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
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
    ∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) *
          (growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
              (blockMatrixFlatFin Ablk) *
            maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) := by
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let rhoFull : ℝ :=
    growthFactorEntry hN (blockMatrixFlatFin Ablk)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hN hm hr Ablk pivotInv) hApos
  let kappaFull : ℝ :=
    maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
      maxEntryNormRect hN hN Ainv
  have hr_le_mr_nat : r ≤ m * r := by
    nth_rewrite 1 [← Nat.one_mul r]
    exact Nat.mul_le_mul_right r (Nat.succ_le_of_lt hm)
  have hrn : (r : ℝ) ≤ (n : ℝ) := by
    exact le_trans (by exact_mod_cast hr_le_mr_nat) hNn
  have hrhoFull_nonneg : 0 ≤ rhoFull := by
    simpa [rhoFull] using
      growthFactorEntry_nonneg hN (blockMatrixFlatFin Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN hm hr Ablk pivotInv) hApos
  have hkappaFull_nonneg : 0 ≤ kappaFull := by
    exact mul_nonneg
      (maxEntryNormRect_nonneg hN hN (blockMatrixFlatFin Ablk))
      (maxEntryNormRect_nonneg hN hN Ainv)
  intro i j hij
  have hBudget :
      (r : ℝ) * rhoLocal i j * kappaLocal i j ≤
        (n : ℝ) * rhoFull ^ 2 * kappaFull :=
    higham13_stage_local_source_lblock_budget_le_of_problem13_4_bound
      (hs_nonneg := Nat.cast_nonneg r) (hsn := hrn)
      (hrho_nonneg := hrhoFull_nonneg)
      (hrhoTail_nonneg := hRhoLocal_nonneg i j hij)
      (hkappa_nonneg := hkappaFull_nonneg)
      (hTail := by simpa [hN, rhoFull] using hRhoLocal_le i j hij)
      (hCond := by simpa [hN, rhoFull, kappaFull] using hKappaLocal_le i j hij)
  exact le_trans (hLocal i j hij)
    (by simpa [hN, rhoFull, kappaFull] using hBudget)

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ matrix-stage-history product bound from source-shaped local
    Problem 13.4 lower-block budgets.

    This wrapper composes
    `higham13_algorithm13_3_multiplier_bounds_from_source_lblock_budgets_exact_kappa`
    with the existing assembled matrix-stage product theorem.  It still leaves
    the local lower-block budgets and the source scalar comparisons visible. -/
theorem higham13_eq13_22_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    higham13_eq13_22_matrix_stage_history_product_from_multiplier_bounds_exact_kappa
      hm hr Ablk pivotInv Ainv hApos hRight n hNn
      (higham13_algorithm13_3_multiplier_bounds_from_source_lblock_budgets_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn rhoLocal kappaLocal
        hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ matrix-stage-history product bound from source-shaped
    local Problem 13.4 lower-block budgets and the source `rho <= 2` side
    condition. -/
theorem higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
      hm hr Ablk pivotInv Ainv hApos hRight n hNn
      (higham13_algorithm13_3_multiplier_bounds_from_source_lblock_budgets_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn rhoLocal kappaLocal
        hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le)
      hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ matrix-stage-history product bound from source-shaped
    local Problem 13.4 lower-block budgets and the matrix-stage BDD
    `rho <= 2` proof layer.

    This is the source-lower-block-budget analogue of the inverse-bound
    `..._of_product_bound_diag_update` theorem: it removes the raw
    `rho <= 2` premise by using the diagonal-update/product-bound route for
    Theorem 13.8.  The source scalar comparison table and the product-bound
    assumptions remain explicit. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa
      hm hr Ablk pivotInv Ainv hApos hRight n hNn rhoLocal kappaLocal
      hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
      (higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hm hr Ablk pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
        hInitInv hPivotInvBound hProduct hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table form of
    `higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update`.

    This accepts the source-style active reciprocal pivot table from
    Theorem 13.7 and derives the scalar pivot-product bound internally. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update_reciprocal
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update
      hm hr Ablk pivotInv Ainv hApos hRight n hNn rhoLocal kappaLocal
      hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ matrix-stage-history product bound from the canonical
    stage-local-growth source comparison route.

    This composes the source local lower-block estimate
    `higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_source_comparisons_exact_kappa`
    with the assembled Eq.13.22 product wrapper.  Thus the local Problem 13.4
    lower-block estimate is discharged by the canonical stage-local growth
    object; the source scalar comparisons `rhoLocal <= rhoFull` and
    `kappaLocal <= rhoFull * kappaFull` remain explicit. -/
theorem
    higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
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
    higham13_eq13_22_matrix_stage_history_product_from_multiplier_bounds_exact_kappa
      hm hr Ablk pivotInv Ainv hApos hRight n hNn
      (higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_source_comparisons_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn hInvPivot hInvSchur hInvFull
        hPivotRight hLocalApos hRhoLocal_le hKappaLocal_le)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ matrix-stage-history product bound from the canonical
    stage-local-growth source comparison route and the source `rho <= 2`
    side condition. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
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
      hm hr Ablk pivotInv Ainv hApos hRight n hNn
      (higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_source_comparisons_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn hInvPivot hInvSchur hInvFull
        hPivotRight hLocalApos hRhoLocal_le hKappaLocal_le)
      hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ matrix-stage-history product bound from canonical stage-local
    growth, an explicit local/global base comparison, and the source condition
    comparison.

    Compared with
    `higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa`,
    this wrapper discharges the raw `rhoLocal <= rhoFull` premise from the
    explicit denominator/base comparison
    `||A||_max <= ||A_local||_max`. -/
theorem
    higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
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
    higham13_eq13_22_matrix_stage_history_product_from_multiplier_bounds_exact_kappa
      hm hr Ablk pivotInv Ainv hApos hRight n hNn
      (higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_base_comparisons_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn hInvPivot hInvSchur hInvFull
        hPivotRight hLocalApos hBaseLocal hKappaLocal_le)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ matrix-stage-history product bound from canonical
    stage-local growth, an explicit local/global base comparison, the source
    condition comparison, and the source `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
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
      hm hr Ablk pivotInv Ainv hApos hRight n hNn
      (higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_base_comparisons_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn hInvPivot hInvSchur hInvFull
        hPivotRight hLocalApos hBaseLocal hKappaLocal_le)
      hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ matrix-stage-history product bound from the canonical
    stage-local-growth source comparison route and the matrix-stage BDD
    `rho <= 2` proof layer.

    This is the canonical stage-local-growth analogue of
    `higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update`:
    it removes the raw `rho <= 2` premise by using the
    diagonal-update/product-bound route, while the local-to-full scalar
    comparison table and active product/update assumptions remain explicit. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_product_bound_diag_update
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hLocalApos hRhoLocal_le hKappaLocal_le
      (higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hm hr Ablk pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
        hInitInv hPivotInvBound hProduct hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table companion to the source-comparison product/update route.

    The Theorem 13.7-style reciprocal table supplies the scalar pivot-product
    premise consumed by the existing matrix-stage product/update bridge. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_product_bound_diag_update_reciprocal
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_product_bound_diag_update
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hLocalApos hRhoLocal_le hKappaLocal_le invDiagBound
      stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ matrix-stage-history product bound from the
    base-comparison stage-local-growth route and the matrix-stage BDD
    `rho <= 2` proof layer.

    This removes both the raw `rhoLocal <= rhoFull` premise and the raw
    `rho <= 2` premise, replacing them by the explicit base comparison, the
    condition comparison, and active product/update data. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_product_bound_diag_update
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hLocalApos hBaseLocal hKappaLocal_le
      (higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hm hr Ablk pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
        hInitInv hPivotInvBound hProduct hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table companion to the base-comparison product/update route.

    The Theorem 13.7-style reciprocal table supplies the scalar pivot-product
    premise consumed by the existing matrix-stage product/update bridge. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_product_bound_diag_update_reciprocal
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_product_bound_diag_update
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hLocalApos hBaseLocal hKappaLocal_le invDiagBound
      stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ matrix-stage-history product bound from canonical stage-local
    growth and an explicit local-inverse upper bound.

    This composes
    `higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_inverse_bound_exact_kappa`
    with the assembled Eq.13.22 product wrapper.  The remaining visible
    source obligation is the local inverse comparison
    `||A_local^{-1}|| <= rhoFull * ||A^{-1}||`. -/
theorem
    higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
    (hInvLocal_le : ∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) :
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
    higham13_eq13_22_matrix_stage_history_product_from_multiplier_bounds_exact_kappa
      hm hr Ablk pivotInv Ainv hApos hRight n hNn
      (higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_inverse_bound_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn hInvPivot hInvSchur hInvFull
        hPivotRight hInvLocal_le)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ matrix-stage-history product bound from canonical
    stage-local growth, an explicit local-inverse upper bound, and the source
    `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
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
      hm hr Ablk pivotInv Ainv hApos hRight n hNn
      (higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_inverse_bound_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn hInvPivot hInvSchur hInvFull
        hPivotRight hInvLocal_le)
      hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-κ matrix-stage-history product bound from canonical stage-local
    growth and a plain local-inverse comparison.

    This composes
    `higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_plain_inverse_bound_exact_kappa`
    with the assembled Eq.13.22 product wrapper.  The remaining visible source
    obligation is now the sharper inverse comparison
    `||A_local^{-1}||_max <= ||A^{-1}||_max`, with the extra `rhoFull` factor
    supplied internally by growth nonvacuity. -/
theorem
    higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
    (hInvLocal_le : ∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) :
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
    higham13_eq13_22_matrix_stage_history_product_from_multiplier_bounds_exact_kappa
      hm hr Ablk pivotInv Ainv hApos hRight n hNn
      (higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_plain_inverse_bound_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn hInvPivot hInvSchur hInvFull
        hPivotRight hInvLocal_le)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row exact-κ matrix-stage-history product bound from canonical
    stage-local growth, a plain local-inverse comparison, and the source
    `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
    (hInvLocal_le : ∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv)
    (hRho_le_two :
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos ≤ 2) :
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
      hm hr Ablk pivotInv Ainv hApos hRight n hNn
      (higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_plain_inverse_bound_exact_kappa
        hm hr Ablk pivotInv Ainv hApos n hNn hInvPivot hInvSchur hInvFull
        hPivotRight hInvLocal_le)
      hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero canonical-inverse matrix-stage-history product bound
    from canonical stage-local growth and the plain local-inverse comparison.

    This is the `nonsingInv`/`det != 0` variant of
    `higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa`.
    It derives the full positive denominator and right-inverse certificate
    from `det(blockMatrixFlatFin Ablk) != 0`; the Schur-tail inverse comparison
    remains the explicit source obligation. -/
theorem
    higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
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
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val)) :
    let hN : 0 < m * r := Nat.mul_pos hm hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) ≤
        maxEntryNormRect hN hN
          (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) →
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
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
    higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hApos hRight n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hInvLocal_le

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero canonical-inverse point-row product bound from the
    plain local-inverse comparison route and the source `rho <= 2` side
    condition. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
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
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val)) :
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
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
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hApos hRight n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hInvLocal_le hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    exact-kappa matrix-stage-history product bound from the plain
    stage-local inverse comparison and the source-strength conditional
    active-stage product-bound/diagonal-update layer.

    This replaces the raw `rho <= 2` premise in
    `higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa`
    by the existing matrix-stage Theorem 13.8 proof layer.  The plain local
    inverse comparison and the dimension-free triple-product max-entry estimate
    remain explicit source obligations. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hInvLocal_le
      (higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hm hr Ablk pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
        hInitInv hPivotInvBound hProduct hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    exact-kappa matrix-stage-history product bound from the plain
    stage-local inverse comparison and reciprocal-table product/update data.

    This is the reciprocal-table companion to
    `higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update`. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_reciprocal
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound
      hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    dimension-aware exact-kappa matrix-stage-history product bound from the
    plain stage-local inverse comparison and the diagonal lower-update layer.

    This is the proved `(r : ℝ)^2` matrix-product route; it does not assert the
    source's dimension-free structured product estimate. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_with_dim_factor_of_diag_update
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hInvLocal_le
      (higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_with_dim_factor_of_diag_update
        hm hr Ablk pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
        hInitInv hPivotInvBound hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero canonical-inverse product bound from the plain
    inverse-comparison route and the source-strength product-bound/
    diagonal-update `rho <= 2` proof layer. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
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
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val)) :
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
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
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hApos hRight n hNn hInvPivot hInvSchur hInvFull hPivotRight
      hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hPivotInvBound hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero canonical-inverse product bound from the plain
    inverse-comparison route and reciprocal-table product/update data. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
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
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val)) :
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
        maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hReciprocal hProduct hDiagUpdate
  exact
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
      hm hr Ablk pivotInv hdet n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound
      hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero canonical-inverse product bound from the plain
    inverse-comparison route and the dimension-aware diagonal-update layer. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_with_dim_factor_of_diag_update_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
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
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val)) :
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
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
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_with_dim_factor_of_diag_update
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hApos hRight n hNn hInvPivot hInvSchur hInvFull hPivotRight
      hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hPivotInvBound hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    exact-κ matrix-stage-history product bound from the direct stage-local
    inverse-bound route and the source-strength conditional active-stage
    product-bound/diagonal-update layer.

    This replaces the raw `rho <= 2` premise in
    `higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa`
    by the existing matrix-stage Theorem 13.8 proof layer.  The local inverse
    comparison and the dimension-free triple-product max-entry estimate remain
    explicit source obligations. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_product_bound_diag_update
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hInvLocal_le
      (higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hm hr Ablk pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
        hInitInv hPivotInvBound hProduct hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table companion to the direct stage-local inverse-bound
    product/update route.  The Theorem 13.7 reciprocal certificate supplies the
    scalar pivot-product premise used by the existing source-strength wrapper. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_product_bound_diag_update_reciprocal
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_product_bound_diag_update
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound
      hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    dimension-aware exact-κ matrix-stage-history product bound from the direct
    stage-local inverse-bound route and the diagonal lower-update layer.

    This is the proved `(r : ℝ)^2` matrix-product route; it does not assert the
    source's dimension-free structured product estimate. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_with_dim_factor_of_diag_update
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
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
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
            (blockMatrixFlatFin Ablk) *
          maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr) Ainv) *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Ablk) := by
  exact
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa
      hm hr Ablk pivotInv Ainv hApos hRight n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hInvLocal_le
      (higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_with_dim_factor_of_diag_update
        hm hr Ablk pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
        hInitInv hPivotInvBound hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero canonical-inverse matrix-stage-history product bound
    from the direct stage-local inverse-bound route.

    This is the `nonsingInv`/`det != 0` variant of
    `higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa`:
    the full-matrix positive denominator and right-inverse certificate are
    derived from `det(blockMatrixFlatFin Ablk) != 0`; the local inverse
    comparison remains visible. -/
theorem
    higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
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
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val)) :
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
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
    higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hApos hRight n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hInvLocal_le

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero canonical-inverse point-row product bound from the
    direct stage-local inverse-bound route and the source `rho <= 2` side
    condition. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
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
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val)) :
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
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
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hApos hRight n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hInvLocal_le hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero canonical-inverse product bound from the direct
    inverse-bound route and the source-strength product-bound/diagonal-update
    `rho <= 2` proof layer. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
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
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val)) :
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
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
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_product_bound_diag_update
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hApos hRight n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound
      hInitInv hPivotInvBound hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero reciprocal-table companion to the direct inverse-bound
    product/update route. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
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
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val)) :
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
        maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hReciprocal hProduct hDiagUpdate
  exact
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
      hm hr Ablk pivotInv hdet n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound
      hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero canonical-inverse product bound from the direct
    inverse-bound route and the dimension-aware diagonal-update layer. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_with_dim_factor_of_diag_update_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
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
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val)) :
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
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
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_inverse_bound_exact_kappa_with_dim_factor_of_diag_update
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hApos hRight n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hInvLocal_le invDiagBound stageInvDiagBound hDom hDiagBound
      hInitInv hPivotInvBound hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero canonical-inverse matrix-stage-history product bound
    from the canonical stage-local-growth source comparison route.

    This is the `nonsingInv`/`det != 0` variant of
    `higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa`:
    the full-matrix positive denominator and right-inverse certificate are
    derived from `det(blockMatrixFlatFin Ablk) != 0`. -/
theorem
    higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
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
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val)) :
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
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
    higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hApos hRight n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hLocalApos hRhoLocal_le hKappaLocal_le

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero canonical-inverse point-row product bound from the
    canonical stage-local-growth source comparison route and the source
    `rho <= 2` side condition. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
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
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
    (hPivotRight : ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val)) :
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
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
    higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hApos hRight n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hLocalApos hRhoLocal_le hKappaLocal_le hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero canonical-inverse matrix-stage-history product bound
    from source-shaped local Problem 13.4 lower-block budgets. -/
theorem
    higham13_eq13_22_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hN : 0 < m * r := Nat.mul_pos hm hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    ∀ rhoLocal kappaLocal : Fin m → Fin m → ℝ,
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j) →
    (∀ i j : Fin m, j.val < i.val → 0 ≤ rhoLocal i j) →
    (∀ i j : Fin m, j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos) →
    (∀ i j : Fin m, j.val < i.val →
      kappaLocal i j ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv (m * r) (blockMatrixFlatFin Ablk)))) →
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      (n : ℝ) *
        (growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos) ^ 3 *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
        maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  have hRight :
      IsRightInverse (m * r) (blockMatrixFlatFin Ablk)
        (nonsingInv (m * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      (m * r) (blockMatrixFlatFin Ablk) hdet).2
  exact
    higham13_eq13_22_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hApos hRight n hNn rhoLocal kappaLocal
      hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero canonical-inverse point-row matrix-stage-history
    product bound from source-shaped local Problem 13.4 lower-block budgets. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hN : 0 < m * r := Nat.mul_pos hm hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    ∀ rhoLocal kappaLocal : Fin m → Fin m → ℝ,
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j) →
    (∀ i j : Fin m, j.val < i.val → 0 ≤ rhoLocal i j) →
    (∀ i j : Fin m, j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos) →
    (∀ i j : Fin m, j.val < i.val →
      kappaLocal i j ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv (m * r) (blockMatrixFlatFin Ablk)))) →
    (growthFactorEntry hN (blockMatrixFlatFin Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN hm hr Ablk pivotInv) hApos ≤ 2) →
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
        maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le
    hKappaLocal_le hRho_le_two
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  have hRight :
      IsRightInverse (m * r) (blockMatrixFlatFin Ablk)
        (nonsingInv (m * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      (m * r) (blockMatrixFlatFin Ablk) hdet).2
  exact
    higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hApos hRight n hNn rhoLocal kappaLocal
      hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero canonical-inverse point-row product bound from
    source-shaped local Problem 13.4 lower-block budgets and the matrix-stage
    BDD `rho <= 2` proof layer.

    This derives both the canonical inverse certificate and the final
    `rho <= 2` side condition from source-style data: determinant
    nonsingularity supplies `nonsingInv`, while the diagonal-update/product
    route supplies the matrix-stage growth-factor bound. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_det_ne_zero_of_product_bound_diag_update
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hN : 0 < m * r := Nat.mul_pos hm hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    ∀ rhoLocal kappaLocal : Fin m → Fin m → ℝ,
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j) →
    (∀ i j : Fin m, j.val < i.val → 0 ≤ rhoLocal i j) →
    (∀ i j : Fin m, j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos) →
    (∀ i j : Fin m, j.val < i.val →
      kappaLocal i j ≤
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
        maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
    invDiagBound stageInvDiagBound hDom hDiagBound hInitInv hPivotInvBound
    hProduct hDiagUpdate
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  have hRight :
      IsRightInverse (m * r) (blockMatrixFlatFin Ablk)
        (nonsingInv (m * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      (m * r) (blockMatrixFlatFin Ablk) hdet).2
  exact
    higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hApos hRight n hNn rhoLocal kappaLocal
      hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hPivotInvBound hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero canonical-inverse point-row product bound from
    source-shaped local Problem 13.4 lower-block budgets and reciprocal
    matrix-stage BDD data.

    This is the reciprocal-table companion to
    `higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_det_ne_zero_of_product_bound_diag_update`:
    determinant nonsingularity supplies the canonical full inverse, while the
    active reciprocal table supplies the scalar pivot-product premise used by
    the diagonal-update/product-bound `rho <= 2` route. -/
theorem
    higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_det_ne_zero_of_product_bound_diag_update_reciprocal
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hN : 0 < m * r := Nat.mul_pos hm hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    ∀ rhoLocal kappaLocal : Fin m → Fin m → ℝ,
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal i j * kappaLocal i j) →
    (∀ i j : Fin m, j.val < i.val → 0 ≤ rhoLocal i j) →
    (∀ i j : Fin m, j.val < i.val →
      rhoLocal i j ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr Ablk pivotInv) hApos) →
    (∀ i j : Fin m, j.val < i.val →
      kappaLocal i j ≤
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
    blockMaxNorm hm hr (higham13_algorithm13_3_lowerFromMatrixStages Ablk pivotInv) *
        blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
      8 * (n : ℝ) *
        (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
          maxEntryNormRect hN hN
            (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
        maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro rhoLocal kappaLocal hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
    invDiagBound stageInvDiagBound hDom hDiagBound hInitInv hReciprocal
    hProduct hDiagUpdate
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  have hRight :
      IsRightInverse (m * r) (blockMatrixFlatFin Ablk)
        (nonsingInv (m * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      (m * r) (blockMatrixFlatFin Ablk) hdet).2
  exact
    higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_product_bound_diag_update_reciprocal
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hApos hRight n hNn rhoLocal kappaLocal
      hLocal hRhoLocal_nonneg hRhoLocal_le hKappaLocal_le
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hReciprocal hProduct hDiagUpdate

end NumStability
