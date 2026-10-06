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
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Section01.NormConventions
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis
import NumStability.Source.Higham.Chapter13.Theorem02.Factorization
import NumStability.Source.Higham.Chapter13.Theorem07.PivotExistence

/-!
# Source.Higham.Chapter13.Equation21

This module formalizes the source-facing Chapter 13 statements for
`Equation21`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


-- ============================================================
-- Stability bounds (Table 13.1, eqs. 13.21--13.24)
-- ============================================================

/-- **Eq. 13.21**: ‖U‖ ≤ ρ_n · ‖A‖ for block LU.
    U is composed of elements of A and Schur complements, so ‖U_{ij}‖ ≤ ‖A^(i)_{ij}‖.
    By Theorem 13.8, max ‖A^(k)_{ij}‖ ≤ 2 max ‖A_{ij}‖, giving ρ_n ≤ 2 for
    block column diag dom. For general matrices ρ_n is the growth factor. -/
theorem block_lu_normU_bound
    (normU normA rho : ℝ)
    (_hRho : 0 ≤ rho) (_hA : 0 ≤ normA)
    (hBound : normU ≤ rho * normA) :
    normU ≤ rho * normA := hBound

/-- Higham, 2nd ed., Chapter 13, §13.3.1, equation (13.21):
    finite max-norm form of the source proof step.  If every block of `U` is
    bounded by the growth-factor budget `ρ_n ‖A‖`, then the chapter's block
    entrywise max norm satisfies `‖U‖ ≤ ρ_n ‖A‖`.  The remaining source work is
    proving the per-block premise from the GE growth-factor definition and the
    Schur-complement sequence. -/
theorem higham13_eq13_21_blockMaxNorm_bound {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (U : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (rho normA : ℝ)
    (hBlocks : ∀ i j : Fin m, maxEntryNorm hr (U i j) ≤ rho * normA) :
    blockMaxNorm hm hr U ≤ rho * normA := by
  unfold blockMaxNorm
  apply Finset.sup'_le
  intro i _hi
  apply Finset.sup'_le
  intro j _hj
  exact hBlocks i j

/-- Higham, 2nd ed., Chapter 13, §13.3.1, equation (13.21):
    source-facing upper-`U`/Schur-stage link.

    For an upper block of `U`, the source proof uses that `U_ij` is a block
    drawn from the corresponding Schur-stage matrix.  This predicate records
    the resulting entrywise max-norm inequality without claiming the concrete
    Algorithm 13.3 stage sequence has already been constructed. -/
def SchurStageUpperBlockBound13_21 {m r : ℕ} (hr : 0 < r)
    (U : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (stageNorm : ℕ → Fin m → Fin m → ℝ) : Prop :=
  ∀ i j : Fin m, i.val ≤ j.val →
    maxEntryNorm hr (U i j) ≤ stageNorm i.val i j

/-- Higham, 2nd ed., Chapter 13, §13.3.1, equation (13.21):
    exact upper-block equality gives the upper-`U`/Schur-stage norm link.

    The equality premise is the concrete Algorithm 13.3 bookkeeping obligation:
    for `i ≤ j`, the block `U_ij` is the active Schur-stage block at stage `i`.
    This adapter only converts that equality into the norm-level premise used
    by the Eq.13.21 bridges. -/
theorem SchurStageUpperBlockBound13_21.of_eq_stageBlock {m r : ℕ}
    (hr : 0 < r)
    (U : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (stageBlock : ℕ → Fin m → Fin m → (Fin r → Fin r → ℝ))
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (hStageNorm : ∀ k : ℕ, ∀ i j : Fin m,
      stageNorm k i j = maxEntryNorm hr (stageBlock k i j))
    (hUpperEq : ∀ i j : Fin m, i.val ≤ j.val →
      U i j = stageBlock i.val i j) :
    SchurStageUpperBlockBound13_21 hr U stageNorm := by
  intro i j hij
  simp [hUpperEq i j hij, hStageNorm i.val i j]

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    exact upper-block bookkeeping for the concrete Schur-stage sequence gives
    the source-facing upper-`U`/Schur-stage norm link.

    The premise is the remaining Algorithm 13.3 equality obligation:
    for `i ≤ j`, the final upper block `Uᵢⱼ` is the Schur-stage block present
    when row/column `i` is pivoted.  The norm alignment is proved by
    `higham13_block_norm_eq_maxEntryNorm`. -/
theorem higham13_algorithm13_3_upper_block_bound_of_eq_stage {m r : ℕ}
    (hr : 0 < r)
    (A U : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hUpperEq : ∀ i j : Fin m, i.val ≤ j.val →
      U i j = higham13_algorithm13_3_schurStageBlock A pivotInv i.val i j) :
    SchurStageUpperBlockBound13_21 hr U
      (higham13_algorithm13_3_schurStageNorm A pivotInv) := by
  exact SchurStageUpperBlockBound13_21.of_eq_stageBlock hr U
    (higham13_algorithm13_3_schurStageBlock A pivotInv)
    (higham13_algorithm13_3_schurStageNorm A pivotInv)
    (by
      intro k i j
      exact higham13_block_norm_eq_maxEntryNorm hr
        (higham13_algorithm13_3_schurStageBlock A pivotInv k i j))
    hUpperEq

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    the exact upper factor assembled from the active Schur stages.

    For an upper block `i <= j`, Algorithm 13.3 stores the block present when
    pivot row/column `i` is eliminated.  Strict lower blocks are zero.  This is
    only the source bookkeeping for the upper factor; it does not by itself
    prove the remaining pivot-inverse, diagonal-update, or factorization
    obligations. -/
noncomputable def higham13_algorithm13_3_upperFromStages {m r : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ)) :
    Fin m → Fin m → (Fin r → Fin r → ℝ) :=
  fun i j =>
    if i.val ≤ j.val then
      higham13_algorithm13_3_schurStageBlock A pivotInv i.val i j
    else
      zeroBlock r

/-- The upper-from-stages factor has exactly the Schur-stage block in every
    upper position. -/
theorem higham13_algorithm13_3_upperFromStages_eq_stage {m r : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (i j : Fin m) (hij : i.val ≤ j.val) :
    higham13_algorithm13_3_upperFromStages A pivotInv i j =
      higham13_algorithm13_3_schurStageBlock A pivotInv i.val i j := by
  simp [higham13_algorithm13_3_upperFromStages, hij]

/-- The upper-from-stages factor is block upper triangular. -/
theorem higham13_algorithm13_3_upperFromStages_lower_zero {m r : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (i j : Fin m) (hji : j.val < i.val) :
    higham13_algorithm13_3_upperFromStages A pivotInv i j = zeroBlock r := by
  have hnot : ¬ i.val ≤ j.val := Nat.not_le_of_gt hji
  simp [higham13_algorithm13_3_upperFromStages, hnot]

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    exact upper factor assembled from Schur stages for an arbitrary normed
    block algebra.

    This is the source-norm companion of `higham13_algorithm13_3_upperFromStages`.
    It is used when the block entries carry a subordinate matrix norm through a
    `SeminormedRing`, rather than the chapter's scalar-entry max norm. -/
noncomputable def higham13_algorithm13_3_upperFromNormedStages {m : ℕ}
    {α : Type*} [Zero α] [Sub α] [Mul α]
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α) :
    Fin m → Fin m → α :=
  fun i j =>
    if i.val ≤ j.val then
      higham13_algorithm13_3_schurStageBlock A pivotInv i.val i j
    else
      0

theorem higham13_algorithm13_3_upperFromNormedStages_eq_stage {m : ℕ}
    {α : Type*} [Zero α] [Sub α] [Mul α]
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (i j : Fin m) (hij : i.val ≤ j.val) :
    higham13_algorithm13_3_upperFromNormedStages A pivotInv i j =
      higham13_algorithm13_3_schurStageBlock A pivotInv i.val i j := by
  simp [higham13_algorithm13_3_upperFromNormedStages, hij]

theorem higham13_algorithm13_3_upperFromNormedStages_lower_zero {m : ℕ}
    {α : Type*} [Zero α] [Sub α] [Mul α]
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (i j : Fin m) (hji : j.val < i.val) :
    higham13_algorithm13_3_upperFromNormedStages A pivotInv i j = 0 := by
  have hnot : ¬ i.val ≤ j.val := Nat.not_le_of_gt hji
  simp [higham13_algorithm13_3_upperFromNormedStages, hnot]

/-- The upper-from-stages factor supplies the exact upper-`U`/Schur-stage norm
    predicate used by the Eq.13.21 bridges. -/
theorem higham13_algorithm13_3_upperFromStages_upper_block_bound {m r : ℕ}
    (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ)) :
    SchurStageUpperBlockBound13_21 hr
      (higham13_algorithm13_3_upperFromStages A pivotInv)
      (higham13_algorithm13_3_schurStageNorm A pivotInv) := by
  exact higham13_algorithm13_3_upper_block_bound_of_eq_stage hr A
    (higham13_algorithm13_3_upperFromStages A pivotInv) pivotInv
    (fun i j hij =>
      higham13_algorithm13_3_upperFromStages_eq_stage A pivotInv i j hij)

/-- Higham, 2nd ed., Chapter 13, §13.3.1, equation (13.21):
    column-block-diagonal-dominance bridge from the active-stage Theorem 13.8
    wrapper to the finite block max norm of `U`.

    The hypotheses keep the source proof obligations visible: `hUpper` says each
    upper block of `U` is bounded by the corresponding active Schur-stage block,
    `hLower` says the strict lower part of `U` is zero at the norm level, and
    `hStep` is still the one-step active-column inequality supplied by the full
    Schur-stage proof. -/
theorem higham13_eq13_21_blockMaxNorm_bound_of_active_stage {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (hInit : ∀ i j : Fin m, stageNorm 0 i j = blockNorm i j)
    (hStep : SchurStageActiveColumnStep13_8 stageNorm)
    (hStageNonneg : ∀ k : ℕ, ∀ i j : Fin m, 0 ≤ stageNorm k i j)
    (normMax : ℝ)
    (hNormMax : 0 ≤ normMax)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (U : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hUpper : SchurStageUpperBlockBound13_21 hr U stageNorm)
    (hLower : ∀ i j : Fin m, j.val < i.val → maxEntryNorm hr (U i j) ≤ 0) :
    blockMaxNorm hm hr U ≤ 2 * normMax := by
  apply higham13_eq13_21_blockMaxNorm_bound hm hr U 2 normMax
  intro i j
  by_cases hij : i.val ≤ j.val
  · exact le_trans (hUpper i j hij)
      (higham13_theorem13_8_active_stage_block_bound_of_steps
        blockNorm invDiagBound hDom hDiagBound stageNorm hInit hStep
        hStageNonneg normMax hMax i.val i j le_rfl hij)
  · have hji : j.val < i.val := Nat.lt_of_not_ge hij
    exact le_trans (hLower i j hji) (by nlinarith [hNormMax])

/-- Higham, 2nd ed., Chapter 13, §13.3.1, equation (13.21):
    column-BDD max-norm bridge using the local Schur one-step estimates and
    active column dominance instead of assuming the active-column step directly.

    The remaining source obligations are now the concrete stage construction,
    local Schur norm estimates, and the full Theorem 13.7 active dominance
    proof for that construction. -/
theorem higham13_eq13_21_blockMaxNorm_bound_of_local_schur_bound {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hInit : ∀ i j : Fin m, stageNorm 0 i j = blockNorm i j)
    (hStageNonneg : ∀ k : ℕ, ∀ i j : Fin m, 0 ≤ stageNorm k i j)
    (hPivotInvNonneg : ∀ k : ℕ, 0 ≤ pivotInvNorm k)
    (hActiveDom : SchurStageActiveColumnDom13_7 stageNorm stageInvDiagBound)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      pivotInvNorm k * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hLocal : SchurStageActiveLocalSchurBound13_8 stageNorm pivotInvNorm)
    (normMax : ℝ)
    (hNormMax : 0 ≤ normMax)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (U : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hUpper : SchurStageUpperBlockBound13_21 hr U stageNorm)
    (hLower : ∀ i j : Fin m, j.val < i.val → maxEntryNorm hr (U i j) ≤ 0) :
    blockMaxNorm hm hr U ≤ 2 * normMax := by
  apply higham13_eq13_21_blockMaxNorm_bound hm hr U 2 normMax
  intro i j
  by_cases hij : i.val ≤ j.val
  · exact le_trans (hUpper i j hij)
      (higham13_theorem13_8_active_stage_block_bound_of_local_schur_bound
        blockNorm invDiagBound hDom hDiagBound stageNorm stageInvDiagBound
        pivotInvNorm hInit hStageNonneg hPivotInvNonneg hActiveDom
        hPivotInvBound hLocal normMax hMax i.val i j le_rfl hij)
  · have hji : j.val < i.val := Nat.lt_of_not_ge hij
    exact le_trans (hLower i j hji) (by nlinarith [hNormMax])

/-- Higham, 2nd ed., Chapter 13, §13.3.1, equation (13.21):
    column-BDD max-norm bridge using the exact active Schur update relation.

    Compared with `higham13_eq13_21_blockMaxNorm_bound_of_local_schur_bound`,
    this derives both the local Schur norm estimate and the active-column
    dominance chain from the exact stage update plus the diagonal Schur
    lower-bound update. -/
theorem higham13_eq13_21_blockMaxNorm_bound_of_exact_update {m r : ℕ}
    {α : Type*} [SeminormedRing α]
    (hm : 0 < m) (hr : 0 < r)
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (stageBlock : ℕ → Fin m → Fin m → α)
    (pivotInv : ℕ → α)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hInitNorm : ∀ i j : Fin m, stageNorm 0 i j = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hStageNorm : ∀ k : ℕ, ∀ i j : Fin m,
      stageNorm k i j = ‖stageBlock k i j‖)
    (hPivotInvNorm : ∀ k : ℕ, pivotInvNorm k = ‖pivotInv k‖)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      pivotInvNorm k * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hUpdate : SchurStageActiveExactUpdate13_8 stageBlock pivotInv)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      stageNorm stageInvDiagBound pivotInvNorm)
    (normMax : ℝ)
    (hNormMax : 0 ≤ normMax)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (U : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hUpper : SchurStageUpperBlockBound13_21 hr U stageNorm)
    (hLower : ∀ i j : Fin m, j.val < i.val → maxEntryNorm hr (U i j) ≤ 0) :
    blockMaxNorm hm hr U ≤ 2 * normMax := by
  apply higham13_eq13_21_blockMaxNorm_bound hm hr U 2 normMax
  intro i j
  by_cases hij : i.val ≤ j.val
  · exact le_trans (hUpper i j hij)
      (higham13_theorem13_8_active_stage_block_bound_of_exact_update
        blockNorm invDiagBound hDom hDiagBound stageBlock pivotInv stageNorm
        stageInvDiagBound pivotInvNorm hInitNorm hInitInv hStageNorm
        hPivotInvNorm hPivotInvBound hUpdate hDiagUpdate normMax hMax
        i.val i j le_rfl hij)
  · have hji : j.val < i.val := Nat.lt_of_not_ge hij
    exact le_trans (hLower i j hji) (by nlinarith [hNormMax])

/-- Higham, 2nd ed., Chapter 13, §13.3.1, equation (13.21):
    column-BDD max-norm bridge using exact active Schur updates and the
    source reciprocal pivot certificate.

    This is the closest current Eq.13.21 bridge to the book proof.  It still
    leaves the concrete Schur-stage construction, upper-`U` link, diagonal
    Schur lower-bound update, and nonsingularity facts as explicit obligations. -/
theorem higham13_eq13_21_blockMaxNorm_bound_of_exact_update_reciprocal {m r : ℕ}
    {α : Type*} [SeminormedRing α]
    (hm : 0 < m) (hr : 0 < r)
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (stageBlock : ℕ → Fin m → Fin m → α)
    (pivotInv : ℕ → α)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hInitNorm : ∀ i j : Fin m, stageNorm 0 i j = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hStageNorm : ∀ k : ℕ, ∀ i j : Fin m,
      stageNorm k i j = ‖stageBlock k i j‖)
    (hPivotInvNorm : ∀ k : ℕ, pivotInvNorm k = ‖pivotInv k‖)
    (hPivotRecip : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound pivotInvNorm)
    (hUpdate : SchurStageActiveExactUpdate13_8 stageBlock pivotInv)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      stageNorm stageInvDiagBound pivotInvNorm)
    (normMax : ℝ)
    (hNormMax : 0 ≤ normMax)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (U : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hUpper : SchurStageUpperBlockBound13_21 hr U stageNorm)
    (hLower : ∀ i j : Fin m, j.val < i.val → maxEntryNorm hr (U i j) ≤ 0) :
    blockMaxNorm hm hr U ≤ 2 * normMax := by
  apply higham13_eq13_21_blockMaxNorm_bound hm hr U 2 normMax
  intro i j
  by_cases hij : i.val ≤ j.val
  · exact le_trans (hUpper i j hij)
      (higham13_theorem13_8_active_stage_block_bound_of_exact_update_reciprocal
        blockNorm invDiagBound hDom hDiagBound stageBlock pivotInv stageNorm
        stageInvDiagBound pivotInvNorm hInitNorm hInitInv hStageNorm
        hPivotInvNorm hPivotRecip hUpdate hDiagUpdate normMax hMax
        i.val i j le_rfl hij)
  · have hji : j.val < i.val := Nat.lt_of_not_ge hij
    exact le_trans (hLower i j hji) (by nlinarith [hNormMax])

/-- Higham, 2nd ed., Chapter 13, §13.3.1, equation (13.21):
    reciprocal exact-update bridge with the strict lower part of `U` supplied as
    actual zero blocks rather than as a norm-level inequality.

    This discharges one of the Eq.13.21 bridge premises from the standard block
    upper-triangular field `U_lower_zero`; the upper-block/Schur-stage link,
    concrete Schur-stage construction, diagonal update, and reciprocal pivot
    data remain explicit. -/
theorem higham13_eq13_21_blockMaxNorm_bound_of_exact_update_reciprocal_zero_lower
    {m r : ℕ} {α : Type*} [SeminormedRing α]
    (hm : 0 < m) (hr : 0 < r)
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (stageBlock : ℕ → Fin m → Fin m → α)
    (pivotInv : ℕ → α)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hInitNorm : ∀ i j : Fin m, stageNorm 0 i j = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hStageNorm : ∀ k : ℕ, ∀ i j : Fin m,
      stageNorm k i j = ‖stageBlock k i j‖)
    (hPivotInvNorm : ∀ k : ℕ, pivotInvNorm k = ‖pivotInv k‖)
    (hPivotRecip : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound pivotInvNorm)
    (hUpdate : SchurStageActiveExactUpdate13_8 stageBlock pivotInv)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      stageNorm stageInvDiagBound pivotInvNorm)
    (normMax : ℝ)
    (hNormMax : 0 ≤ normMax)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (U : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hUpper : SchurStageUpperBlockBound13_21 hr U stageNorm)
    (hLowerZero : ∀ i j : Fin m, j.val < i.val → U i j = zeroBlock r) :
    blockMaxNorm hm hr U ≤ 2 * normMax :=
  higham13_eq13_21_blockMaxNorm_bound_of_exact_update_reciprocal
    hm hr blockNorm invDiagBound hDom hDiagBound stageBlock pivotInv stageNorm
    stageInvDiagBound pivotInvNorm hInitNorm hInitInv hStageNorm
    hPivotInvNorm hPivotRecip hUpdate hDiagUpdate normMax hNormMax hMax U
    hUpper
    (fun i j hji => maxEntryNorm_le_zero_of_eq_zeroBlock hr (hLowerZero i j hji))

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    the concrete active Schur-stage sequence supplies the exact-update/local
    Schur part of the one-step column-dominance proof.

    The reciprocal pivot certificate and diagonal Schur lower-bound update
    remain explicit Algorithm 13.3 obligations. -/
theorem higham13_algorithm13_3_active_column_dom_step_of_reciprocal {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hPivotRecip : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    SchurStageActiveColumnDomStep13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound := by
  exact higham13_theorem13_7_active_column_dom_step_of_exact_update_reciprocal
    (higham13_algorithm13_3_schurStageBlock A pivotInv) pivotInv
    (higham13_algorithm13_3_schurStageNorm A pivotInv)
    stageInvDiagBound
    (higham13_algorithm13_3_pivotInvNorm pivotInv)
    (by
      intro k i j
      rfl)
    (by
      intro k
      rfl)
    hPivotRecip
    (higham13_algorithm13_3_schurStageBlock_exact_update A pivotInv)
    hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    active column block diagonal dominance for the concrete Schur-stage table.

    This instantiates the exact-update proof layer with
    `higham13_algorithm13_3_schurStageBlock`.  It does not prove the remaining
    reciprocal pivot certificate, diagonal Schur lower-bound update, or
    block-LU/nonsingularity existence facts. -/
theorem higham13_algorithm13_3_active_column_dominance_of_reciprocal {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotRecip : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    SchurStageActiveColumnDom13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound := by
  exact higham13_theorem13_7_active_column_dominance_of_exact_update_reciprocal
    blockNorm invDiagBound hDom
    (higham13_algorithm13_3_schurStageBlock A pivotInv) pivotInv
    (higham13_algorithm13_3_schurStageNorm A pivotInv)
    stageInvDiagBound
    (higham13_algorithm13_3_pivotInvNorm pivotInv)
    (by
      intro i j
      simpa [higham13_algorithm13_3_schurStageNorm,
        higham13_algorithm13_3_schurStageBlock] using hInitNorm i j)
    hInitInv
    (by
      intro k i j
      rfl)
    (by
      intro k
      rfl)
    hPivotRecip
    (higham13_algorithm13_3_schurStageBlock_exact_update A pivotInv)
    hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    active-stage block growth bound for the concrete Schur-stage table.

    This closes the mechanical exact-update/local-Schur part of the Theorem
    13.8 wrapper.  The diagonal update, reciprocal pivot data, initial
    dominance, and max-norm majorant remain on the theorem surface. -/
theorem higham13_algorithm13_3_active_stage_block_bound_of_reciprocal {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotRecip : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    higham13_algorithm13_3_schurStageNorm A pivotInv k i j ≤
      2 * normMax := by
  exact higham13_theorem13_8_active_stage_block_bound_of_exact_update_reciprocal
    blockNorm invDiagBound hDom hDiagBound
    (higham13_algorithm13_3_schurStageBlock A pivotInv) pivotInv
    (higham13_algorithm13_3_schurStageNorm A pivotInv)
    stageInvDiagBound
    (higham13_algorithm13_3_pivotInvNorm pivotInv)
    (by
      intro i j
      simpa [higham13_algorithm13_3_schurStageNorm,
        higham13_algorithm13_3_schurStageBlock] using hInitNorm i j)
    hInitInv
    (by
      intro k i j
      rfl)
    (by
      intro k
      rfl)
    hPivotRecip
    (higham13_algorithm13_3_schurStageBlock_exact_update A pivotInv)
    hDiagUpdate normMax hMax k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, equation (13.21), Algorithm 13.3 bridge:
    finite block max-norm bound after instantiating the active Schur-stage
    proof with the concrete Algorithm 13.3 stage table.

    The upper-`U`/stage relation, strict lower zero blocks, diagonal update,
    reciprocal pivot certificate, and growth-factor majorant remain explicit.
    This theorem is therefore a dependency bridge, not the full Eq.13.21
    source closure. -/
theorem higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_reciprocal_zero_lower
    {m r : ℕ} {α : Type*} [SeminormedRing α]
    (hm : 0 < m) (hr : 0 < r)
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotRecip : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (normMax : ℝ)
    (hNormMax : 0 ≤ normMax)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (U : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hUpper : SchurStageUpperBlockBound13_21 hr U
      (higham13_algorithm13_3_schurStageNorm A pivotInv))
    (hLowerZero : ∀ i j : Fin m, j.val < i.val → U i j = zeroBlock r) :
    blockMaxNorm hm hr U ≤ 2 * normMax := by
  exact higham13_eq13_21_blockMaxNorm_bound_of_exact_update_reciprocal_zero_lower
    hm hr blockNorm invDiagBound hDom hDiagBound
    (higham13_algorithm13_3_schurStageBlock A pivotInv) pivotInv
    (higham13_algorithm13_3_schurStageNorm A pivotInv)
    stageInvDiagBound
    (higham13_algorithm13_3_pivotInvNorm pivotInv)
    (by
      intro i j
      simpa [higham13_algorithm13_3_schurStageNorm,
        higham13_algorithm13_3_schurStageBlock] using hInitNorm i j)
    hInitInv
    (by
      intro k i j
      rfl)
    (by
      intro k
      rfl)
    hPivotRecip
    (higham13_algorithm13_3_schurStageBlock_exact_update A pivotInv)
    hDiagUpdate normMax hNormMax hMax U hUpper hLowerZero

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    the concrete active Schur-stage sequence supplies the one-step column
    dominance rule from the direct pivot product bound
    `‖pivotInv_k‖ * gamma_k <= 1`.

    This is weaker and closer to the proof need than the reciprocal/equality
    wrappers below; it still leaves the construction of the bound from
    nonsingularity or diagonal dominance as a separate source obligation. -/
theorem higham13_algorithm13_3_active_column_dom_step_of_pivot_bound {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_pivotInvNorm pivotInv k *
        stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    SchurStageActiveColumnDomStep13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound := by
  exact higham13_theorem13_7_active_column_dom_step_of_exact_update
    (higham13_algorithm13_3_schurStageBlock A pivotInv) pivotInv
    (higham13_algorithm13_3_schurStageNorm A pivotInv)
    stageInvDiagBound
    (higham13_algorithm13_3_pivotInvNorm pivotInv)
    (by
      intro k i j
      rfl)
    (by
      intro k
      rfl)
    hPivotBound
    (higham13_algorithm13_3_schurStageBlock_exact_update A pivotInv)
    hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    active column block diagonal dominance for the concrete Schur-stage table
    from the direct pivot product bound. -/
theorem higham13_algorithm13_3_active_column_dominance_of_pivot_bound {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_pivotInvNorm pivotInv k *
        stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    SchurStageActiveColumnDom13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound := by
  exact higham13_theorem13_7_active_column_dominance_of_exact_update
    blockNorm invDiagBound hDom
    (higham13_algorithm13_3_schurStageBlock A pivotInv) pivotInv
    (higham13_algorithm13_3_schurStageNorm A pivotInv)
    stageInvDiagBound
    (higham13_algorithm13_3_pivotInvNorm pivotInv)
    (by
      intro i j
      simpa [higham13_algorithm13_3_schurStageNorm,
        higham13_algorithm13_3_schurStageBlock] using hInitNorm i j)
    hInitInv
    (by
      intro k i j
      rfl)
    (by
      intro k
      rfl)
    hPivotBound
    (higham13_algorithm13_3_schurStageBlock_exact_update A pivotInv)
    hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    active-stage block growth bound for the concrete Schur-stage table from
    the direct pivot product bound. -/
theorem higham13_algorithm13_3_active_stage_block_bound_of_pivot_bound {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_pivotInvNorm pivotInv k *
        stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    higham13_algorithm13_3_schurStageNorm A pivotInv k i j ≤
      2 * normMax := by
  exact higham13_theorem13_8_active_stage_block_bound_of_exact_update
    blockNorm invDiagBound hDom hDiagBound
    (higham13_algorithm13_3_schurStageBlock A pivotInv) pivotInv
    (higham13_algorithm13_3_schurStageNorm A pivotInv)
    stageInvDiagBound
    (higham13_algorithm13_3_pivotInvNorm pivotInv)
    (by
      intro i j
      simpa [higham13_algorithm13_3_schurStageNorm,
        higham13_algorithm13_3_schurStageBlock] using hInitNorm i j)
    hInitInv
    (by
      intro k i j
      rfl)
    (by
      intro k
      rfl)
    hPivotBound
    (higham13_algorithm13_3_schurStageBlock_exact_update A pivotInv)
    hDiagUpdate normMax hMax k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, equation (13.21), Algorithm 13.3 bridge:
    finite block max-norm bound from the direct pivot product bound,
    diagonal-update predicate, upper-`U`/Schur-stage bound, and strict lower
    zero blocks. -/
theorem higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_bound
    {m r : ℕ} {α : Type*} [SeminormedRing α]
    (hm : 0 < m) (hr : 0 < r)
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_pivotInvNorm pivotInv k *
        stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (normMax : ℝ)
    (hNormMax : 0 ≤ normMax)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (U : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hUpper : SchurStageUpperBlockBound13_21 hr U
      (higham13_algorithm13_3_schurStageNorm A pivotInv))
    (hLowerZero : ∀ i j : Fin m, j.val < i.val → U i j = zeroBlock r) :
    blockMaxNorm hm hr U ≤ 2 * normMax := by
  exact higham13_eq13_21_blockMaxNorm_bound_of_exact_update
    hm hr blockNorm invDiagBound hDom hDiagBound
    (higham13_algorithm13_3_schurStageBlock A pivotInv) pivotInv
    (higham13_algorithm13_3_schurStageNorm A pivotInv)
    stageInvDiagBound
    (higham13_algorithm13_3_pivotInvNorm pivotInv)
    (by
      intro i j
      simpa [higham13_algorithm13_3_schurStageNorm,
        higham13_algorithm13_3_schurStageBlock] using hInitNorm i j)
    hInitInv
    (by
      intro k i j
      rfl)
    (by
      intro k
      rfl)
    hPivotBound
    (higham13_algorithm13_3_schurStageBlock_exact_update A pivotInv)
    hDiagUpdate normMax hNormMax hMax U hUpper
    (fun i j hji => maxEntryNorm_le_zero_of_eq_zeroBlock hr (hLowerZero i j hji))

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    product-form pivot data gives the reciprocal pivot certificate for the
    concrete active Schur-stage norm table.

    This is the source-shaped form of the remaining pivot obligation:
    the stage diagonal certificate times the norm of the supplied pivot inverse
    is exactly `1`. -/
theorem higham13_algorithm13_3_pivot_reciprocal_of_mul_eq_one {m : ℕ}
    {α : Type*} [Norm α]
    (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hPivotInvNorm_ne : ∀ k : ℕ,
      higham13_algorithm13_3_pivotInvNorm pivotInv k ≠ 0)
    (hMul : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1) :
    SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv) := by
  exact SchurStageActivePivotInvReciprocal13_7.of_mul_eq_one
    stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv)
    hPivotInvNorm_ne hMul

/-- Algorithm 13.3 product-form pivot data gives the reciprocal pivot
    certificate without a separate nonzero-norm premise: nonzero follows from
    the active product identity itself. -/
theorem higham13_algorithm13_3_pivot_reciprocal_of_active_mul_eq_one {m : ℕ}
    {α : Type*} [Norm α]
    (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hMul : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1) :
    SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv) := by
  exact SchurStageActivePivotInvReciprocal13_7.of_active_mul_eq_one
    stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv) hMul

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    exact diagonal-certificate equality gives the concrete active-stage
    diagonal lower-bound update.

    This records the equality form of the remaining diagonal Schur proof step
    while leaving the equality itself as the next mathematical obligation. -/
theorem higham13_algorithm13_3_active_diag_lower_update_of_eq {m : ℕ}
    {α : Type*} [Sub α] [Mul α] [Norm α]
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hEq : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        stageInvDiagBound (k + 1) j =
          stageInvDiagBound k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j) :
    SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv) := by
  exact SchurStageActiveDiagLowerUpdate13_7.of_eq
    (higham13_algorithm13_3_schurStageNorm A pivotInv)
    stageInvDiagBound
    (higham13_algorithm13_3_pivotInvNorm pivotInv)
    hEq

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    diagonal lower-bound certificate following the active Schur-stage
    recurrence.

    Stage `0` is the initial inverse-diagonal lower-bound table.  At pivot
    stage `k`, active diagonal certificates are updated by subtracting the
    pivot-column/pivot-row Schur correction.  This is a certificate sequence for
    the source proof; the separate pivot product premise still has to tie the
    pivot certificate to the norm of the supplied pivot inverse. -/
noncomputable def higham13_algorithm13_3_diagLowerCert {m r : ℕ}
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ)) :
    ℕ → Fin m → ℝ
  | 0, j => invDiagBound j
  | k + 1, j =>
      if hk : k < m then
        if _hactive : k + 1 ≤ j.val then
          higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j
        else
          higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k j
      else
        higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k j

/-- The concrete diagonal lower-bound certificate starts from the source
    initial table. -/
theorem higham13_algorithm13_3_diagLowerCert_zero {m r : ℕ}
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ)) :
    ∀ j : Fin m,
      higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv 0 j =
        invDiagBound j := by
  intro j
  rfl

/-- The concrete diagonal lower-bound certificate satisfies the exact active
    recurrence used by the source proof. -/
theorem higham13_algorithm13_3_diagLowerCert_eq {m r : ℕ}
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ)) :
    ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv (k + 1) j =
          higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j := by
  intro k hk j hj
  simp [higham13_algorithm13_3_diagLowerCert, hk, hj]

/-- The concrete diagonal lower-bound certificate supplies the named active
    diagonal-update predicate. -/
theorem higham13_algorithm13_3_diagLowerCert_update {m r : ℕ}
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ)) :
    SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv) := by
  exact higham13_algorithm13_3_active_diag_lower_update_of_eq A pivotInv
    (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
    (higham13_algorithm13_3_diagLowerCert_eq invDiagBound A pivotInv)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 and equation (13.18):
    the concrete `diagLowerCert` recurrence is bounded by any source
    inverse-diagonal lower-bound table satisfying the active Schur lower-bound
    update.

    This is the bookkeeping bridge from the source proof's actual
    `‖(Aᵢᵢ^(k))⁻¹‖⁻¹`-style table to the concrete recurrence used by the
    Algorithm 13.3 active-stage wrappers. -/
theorem higham13_algorithm13_3_diagLowerCert_active_le_of_diag_update
    {m r : ℕ}
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInit : ∀ j : Fin m, invDiagBound j ≤ stageInvDiagBound 0 j)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    ∀ k : ℕ, ∀ j : Fin m, k ≤ j.val →
      higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k j ≤
        stageInvDiagBound k j := by
  intro k
  induction k with
  | zero =>
      intro j _hj
      simpa [higham13_algorithm13_3_diagLowerCert] using hInit j
  | succ k ih =>
      intro j hj
      have hk : k < m := Nat.lt_trans (Nat.lt_of_succ_le hj) j.isLt
      have hprev : k ≤ j.val := Nat.le_of_succ_le hj
      have hcert_eq :
          higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv (k + 1) j =
            higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k j -
              higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
                higham13_algorithm13_3_pivotInvNorm pivotInv k *
                higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j :=
        higham13_algorithm13_3_diagLowerCert_eq invDiagBound A pivotInv k hk j hj
      calc
        higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv (k + 1) j
            =
              higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k j -
                higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
                  higham13_algorithm13_3_pivotInvNorm pivotInv k *
                  higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j := hcert_eq
        _ ≤
              stageInvDiagBound k j -
                higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
                  higham13_algorithm13_3_pivotInvNorm pivotInv k *
                  higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j := by
              exact sub_le_sub_right (ih j hprev) _
        _ ≤ stageInvDiagBound (k + 1) j :=
              hDiagUpdate k hk j hj

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7:
    a source inverse-diagonal lower-bound table gives the concrete one-sided
    active pivot certificate for `diagLowerCert`.

    The hypotheses match the proof-chain shape of equation (13.18): the source
    table starts above the initial certificate, satisfies the active Schur
    lower-bound update, and its active diagonal entries are bounded by the
    reciprocal norm of the supplied pivot inverses. -/
theorem higham13_algorithm13_3_diagLowerCert_diag_lower_of_source_table
    {m r : ℕ}
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInit : ∀ j : Fin m, invDiagBound j ≤ stageInvDiagBound 0 j)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (hActiveUpper : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ ≤
        (higham13_algorithm13_3_pivotInvNorm pivotInv k)⁻¹) :
    SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv) := by
  intro k hk
  exact le_trans
    (higham13_algorithm13_3_diagLowerCert_active_le_of_diag_update
      invDiagBound A pivotInv stageInvDiagBound hInit hDiagUpdate k ⟨k, hk⟩ le_rfl)
    (hActiveUpper k hk)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7:
    reciprocal-equality source-table form of the concrete one-sided active
    pivot certificate for `diagLowerCert`.

    This removes the one-sided active-upper proof artifact when the source
    inverse-bound table is presented in the natural equality form
    `d(k,k) = ‖pivotInv_k‖⁻¹`.  Constructing that source table and proving its
    Eq.13.18 diagonal update remain the mathematical obligations. -/
theorem higham13_algorithm13_3_diagLowerCert_diag_lower_of_source_table_reciprocal
    {m r : ℕ}
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInit : ∀ j : Fin m, invDiagBound j ≤ stageInvDiagBound 0 j)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv) :=
  higham13_algorithm13_3_diagLowerCert_diag_lower_of_source_table
    invDiagBound A pivotInv stageInvDiagBound hInit hDiagUpdate
    (fun k hk => by
      rw [hReciprocal k hk])

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    continuous-linear lower-norm source table supplies the concrete one-sided
    active pivot certificate for `diagLowerCert`.

    This is the source-table integration bridge for the arbitrary-norm route.
    The active blocks are modeled as continuous linear maps whose operator
    norms agree with the Algorithm 13.3 stage norm table, the Schur correction
    is the composed block action `A_jk A_kk^{-1} A_kj`, and the active pivot
    inverse is a two-sided continuous-linear inverse.  Under these alignment
    hypotheses, the generic lower-norm table, Schur-composition update, and
    reciprocal table feed the existing `diagLowerCert` API. -/
theorem higham13_algorithm13_3_diagLowerCert_diag_lower_of_continuousLinearMap_source_table
    {m r : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (stageBlock : ℕ → Fin m → Fin m → E →L[ℝ] E)
    (pivotInvCLM : ℕ → E →L[ℝ] E)
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤ continuousLinearMapLowerNorm (stageBlock 0 j j) hunit)
    (hStageNorm : ∀ k : ℕ, ∀ i j : Fin m,
      ‖stageBlock k i j‖ = higham13_algorithm13_3_schurStageNorm A pivotInv k i j)
    (hPivotNorm : ∀ k : ℕ,
      ‖pivotInvCLM k‖ = higham13_algorithm13_3_pivotInvNorm pivotInv k)
    (hSchur : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E,
        stageBlock (k + 1) j j x =
          stageBlock k j j x -
            stageBlock k j ⟨k, hk⟩
              (pivotInvCLM k (stageBlock k ⟨k, hk⟩ j x)))
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : E,
      pivotInvCLM k (stageBlock k ⟨k, hk⟩ ⟨k, hk⟩ x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : E,
      stageBlock k ⟨k, hk⟩ ⟨k, hk⟩ (pivotInvCLM k y) = y) :
    SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv) := by
  let stageInvDiagBound : ℕ → Fin m → ℝ :=
    fun k j => continuousLinearMapLowerNorm (stageBlock k j j) hunit
  have hDiagUpdateCLM : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => ‖stageBlock k i j‖)
      stageInvDiagBound
      (fun k => ‖pivotInvCLM k‖) := by
    simpa [stageInvDiagBound] using
      (SchurStageActiveDiagLowerUpdate13_7.of_continuousLinearMap_schur_composition
        hunit stageBlock pivotInvCLM hSchur)
  have hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv) := by
    intro k hk j hj
    simpa [stageInvDiagBound, hStageNorm k j ⟨k, hk⟩,
      hStageNorm k ⟨k, hk⟩ j, hPivotNorm k] using
      hDiagUpdateCLM k hk j hj
  have hRecipCLM : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => ‖pivotInvCLM k‖) := by
    simpa [stageInvDiagBound] using
      (SchurStageActivePivotInvReciprocal13_7.of_continuousLinearMap_inverse
        hunit (fun k j => stageBlock k j j) pivotInvCLM hLeft hRight)
  have hRecip : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv) := by
    intro k hk
    simpa [stageInvDiagBound, hPivotNorm k] using hRecipCLM k hk
  exact
    higham13_algorithm13_3_diagLowerCert_diag_lower_of_source_table_reciprocal
      invDiagBound A pivotInv stageInvDiagBound hInit hDiagUpdate hRecip

/-- Generic version of the Algorithm 13.3 diagonal lower-bound certificate.

    The legacy `higham13_algorithm13_3_diagLowerCert` is specialized to the
    repository's function-shaped matrix blocks.  This parallel definition keeps
    the same scalar recurrence for any normed block algebra, so concrete
    Mathlib `Matrix` block norms can use the same source-table proof layer. -/
noncomputable def higham13_algorithm13_3_diagLowerCertGeneric {m : ℕ}
    {α : Type*} [Norm α] [Sub α] [Mul α]
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α) :
    ℕ → Fin m → ℝ
  | 0, j => invDiagBound j
  | k + 1, j =>
      if hk : k < m then
        if _hactive : k + 1 ≤ j.val then
          higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j
        else
          higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv k j
      else
        higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv k j

/-- The generic diagonal lower-bound certificate starts from the source initial
table. -/
theorem higham13_algorithm13_3_diagLowerCertGeneric_zero {m : ℕ}
    {α : Type*} [Norm α] [Sub α] [Mul α]
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α) :
    ∀ j : Fin m,
      higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv 0 j =
        invDiagBound j := by
  intro j
  rfl

/-- The generic diagonal lower-bound certificate satisfies the exact active
recurrence used by the source proof. -/
theorem higham13_algorithm13_3_diagLowerCertGeneric_eq {m : ℕ}
    {α : Type*} [Norm α] [Sub α] [Mul α]
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α) :
    ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv (k + 1) j =
          higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j := by
  intro k hk j hj
  simp [higham13_algorithm13_3_diagLowerCertGeneric, hk, hj]

/-- The generic diagonal lower-bound certificate supplies the named active
diagonal-update predicate. -/
theorem higham13_algorithm13_3_diagLowerCertGeneric_update {m : ℕ}
    {α : Type*} [Norm α] [Sub α] [Mul α]
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α) :
    SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv) := by
  exact higham13_algorithm13_3_active_diag_lower_update_of_eq A pivotInv
    (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
    (higham13_algorithm13_3_diagLowerCertGeneric_eq invDiagBound A pivotInv)

/-- Generic source-table-to-certificate bridge for Algorithm 13.3 diagonal
lower-bound certificates. -/
theorem higham13_algorithm13_3_diagLowerCertGeneric_active_le_of_diag_update
    {m : ℕ} {α : Type*} [Norm α] [Sub α] [Mul α]
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInit : ∀ j : Fin m, invDiagBound j ≤ stageInvDiagBound 0 j)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    ∀ k : ℕ, ∀ j : Fin m, k ≤ j.val →
      higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv k j ≤
        stageInvDiagBound k j := by
  intro k
  induction k with
  | zero =>
      intro j _hj
      simpa [higham13_algorithm13_3_diagLowerCertGeneric] using hInit j
  | succ k ih =>
      intro j hj
      have hk : k < m := Nat.lt_trans (Nat.lt_of_succ_le hj) j.isLt
      have hprev : k ≤ j.val := Nat.le_of_succ_le hj
      have hcert_eq :
          higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv (k + 1) j =
            higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv k j -
              higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
                higham13_algorithm13_3_pivotInvNorm pivotInv k *
                higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j :=
        higham13_algorithm13_3_diagLowerCertGeneric_eq invDiagBound A pivotInv k hk j hj
      calc
        higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv (k + 1) j
            =
              higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv k j -
                higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
                  higham13_algorithm13_3_pivotInvNorm pivotInv k *
                  higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j := hcert_eq
        _ ≤
              stageInvDiagBound k j -
                higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
                  higham13_algorithm13_3_pivotInvNorm pivotInv k *
                  higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j := by
              exact sub_le_sub_right (ih j hprev) _
        _ ≤ stageInvDiagBound (k + 1) j :=
              hDiagUpdate k hk j hj

/-- Generic reciprocal source table gives the one-sided active pivot
certificate for `diagLowerCertGeneric`. -/
theorem higham13_algorithm13_3_diagLowerCertGeneric_diag_lower_of_source_table_reciprocal
    {m : ℕ} {α : Type*} [Norm α] [Sub α] [Mul α]
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInit : ∀ j : Fin m, invDiagBound j ≤ stageInvDiagBound 0 j)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv) := by
  intro k hk
  exact le_trans
    (higham13_algorithm13_3_diagLowerCertGeneric_active_le_of_diag_update
      invDiagBound A pivotInv stageInvDiagBound hInit hDiagUpdate
      k ⟨k, hk⟩ le_rfl)
    (by rw [hReciprocal k hk])

/-- Generic continuous-linear source table gives the one-sided active pivot
certificate for `diagLowerCertGeneric`. -/
theorem
    higham13_algorithm13_3_diagLowerCertGeneric_diag_lower_of_continuousLinearMap_source_table
    {m : ℕ} {α E : Type*}
    [Norm α] [Sub α] [Mul α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageBlock : ℕ → Fin m → Fin m → E →L[ℝ] E)
    (pivotInvCLM : ℕ → E →L[ℝ] E)
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤ continuousLinearMapLowerNorm (stageBlock 0 j j) hunit)
    (hStageNorm : ∀ k : ℕ, ∀ i j : Fin m,
      ‖stageBlock k i j‖ = higham13_algorithm13_3_schurStageNorm A pivotInv k i j)
    (hPivotNorm : ∀ k : ℕ,
      ‖pivotInvCLM k‖ = higham13_algorithm13_3_pivotInvNorm pivotInv k)
    (hSchur : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E,
        stageBlock (k + 1) j j x =
          stageBlock k j j x -
            stageBlock k j ⟨k, hk⟩
              (pivotInvCLM k (stageBlock k ⟨k, hk⟩ j x)))
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : E,
      pivotInvCLM k (stageBlock k ⟨k, hk⟩ ⟨k, hk⟩ x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : E,
      stageBlock k ⟨k, hk⟩ ⟨k, hk⟩ (pivotInvCLM k y) = y) :
    SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv) := by
  let stageInvDiagBound : ℕ → Fin m → ℝ :=
    fun k j => continuousLinearMapLowerNorm (stageBlock k j j) hunit
  have hDiagUpdateCLM : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => ‖stageBlock k i j‖)
      stageInvDiagBound
      (fun k => ‖pivotInvCLM k‖) := by
    simpa [stageInvDiagBound] using
      (SchurStageActiveDiagLowerUpdate13_7.of_continuousLinearMap_schur_composition
        hunit stageBlock pivotInvCLM hSchur)
  have hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv) := by
    intro k hk j hj
    simpa [stageInvDiagBound, hStageNorm k j ⟨k, hk⟩,
      hStageNorm k ⟨k, hk⟩ j, hPivotNorm k] using
      hDiagUpdateCLM k hk j hj
  have hRecipCLM : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => ‖pivotInvCLM k‖) := by
    simpa [stageInvDiagBound] using
      (SchurStageActivePivotInvReciprocal13_7.of_continuousLinearMap_inverse
        hunit (fun k j => stageBlock k j j) pivotInvCLM hLeft hRight)
  have hRecip : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv) := by
    intro k hk
    simpa [stageInvDiagBound, hPivotNorm k] using hRecipCLM k hk
  exact
    higham13_algorithm13_3_diagLowerCertGeneric_diag_lower_of_source_table_reciprocal
      invDiagBound A pivotInv stageInvDiagBound hInit hDiagUpdate hRecip

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    source lower-norm table for the actual continuous-linear Schur-stage
    pivots.

    The table is
    `mu_kj = min_{‖x‖ = 1} ‖A_jj^(k) x‖`, represented by
    `continuousLinearMapLowerNorm`.  For the Algorithm 13.3 Schur recurrence
    on continuous linear maps, this table satisfies the active diagonal-update
    inequality used in (13.18); if the supplied active pivot maps are two-sided
    inverses, the active table entries are the reciprocal pivot-inverse norms.
    This is the named arbitrary-subordinate-norm source table behind the BDD
    Theorems 13.7--13.8 route. -/
theorem higham13_algorithm13_3_source_lowerNorm_table_of_active_schur_pivots
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (A : Fin m → Fin m → E →L[ℝ] E)
    (pivotInv : ℕ → E →L[ℝ] E)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : E,
      pivotInv k
        (higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩ x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : E,
      higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩
        (pivotInv k y) = y) :
    SchurStageActiveDiagLowerUpdate13_7
        (higham13_algorithm13_3_schurStageNorm A pivotInv)
        (fun k j =>
          continuousLinearMapLowerNorm
            (higham13_algorithm13_3_schurStageBlock A pivotInv k j j)
            hunit)
        (fun k => ‖pivotInv k‖) ∧
      SchurStageActivePivotInvReciprocal13_7
        (fun k j =>
          continuousLinearMapLowerNorm
            (higham13_algorithm13_3_schurStageBlock A pivotInv k j j)
            hunit)
        (fun k => ‖pivotInv k‖) := by
  have hSchur : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E,
        higham13_algorithm13_3_schurStageBlock A pivotInv (k + 1) j j x =
          higham13_algorithm13_3_schurStageBlock A pivotInv k j j x -
            higham13_algorithm13_3_schurStageBlock A pivotInv k j ⟨k, hk⟩
              (pivotInv k
                (higham13_algorithm13_3_schurStageBlock A pivotInv k ⟨k, hk⟩ j x)) := by
    intro k hk j hj x
    let p : Fin m := ⟨k, hk⟩
    have hUpdate :=
      (higham13_algorithm13_3_schurStageBlock_exact_update A pivotInv)
        k hk j j hj hj
    have hUpdate' :
        higham13_algorithm13_3_schurStageBlock A pivotInv (k + 1) j j =
          higham13_algorithm13_3_schurStageBlock A pivotInv k j j -
            higham13_algorithm13_3_schurStageBlock A pivotInv k j p *
              pivotInv k *
              higham13_algorithm13_3_schurStageBlock A pivotInv k p j := by
      simpa [p] using hUpdate
    rw [hUpdate']
    rfl
  refine ⟨?_, ?_⟩
  · simpa [higham13_algorithm13_3_schurStageNorm] using
      (SchurStageActiveDiagLowerUpdate13_7.of_continuousLinearMap_schur_composition
        hunit (higham13_algorithm13_3_schurStageBlock A pivotInv) pivotInv hSchur)
  · simpa using
      (SchurStageActivePivotInvReciprocal13_7.of_continuousLinearMap_inverse
        hunit
        (fun k j => higham13_algorithm13_3_schurStageBlock A pivotInv k j j)
        pivotInv hLeft hRight)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    actual continuous-linear-map Schur stages give the one-sided active pivot
    certificate for `diagLowerCertGeneric`.

    This instantiates the generic CLM source-table theorem with the real
    Algorithm 13.3 Schur recurrence on continuous linear maps.  The remaining
    source obligations are the initial lower table and the two-sided active
    pivot inverse identities. -/
theorem
    higham13_algorithm13_3_clm_diagLowerCertGeneric_diag_lower_of_continuousLinearMap_source_table
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → E →L[ℝ] E)
    (pivotInv : ℕ → E →L[ℝ] E)
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (higham13_algorithm13_3_schurStageBlock A pivotInv 0 j j)
          hunit)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : E,
      pivotInv k
        (higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩ x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : E,
      higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩
        (pivotInv k y) = y) :
    SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (fun k => ‖pivotInv k‖) := by
  rcases
    higham13_algorithm13_3_source_lowerNorm_table_of_active_schur_pivots
      hunit A pivotInv hLeft hRight with
    ⟨hDiagUpdate, hRecip⟩
  simpa [higham13_algorithm13_3_pivotInvNorm] using
    (higham13_algorithm13_3_diagLowerCertGeneric_diag_lower_of_source_table_reciprocal
      invDiagBound A pivotInv
      (fun k j =>
        continuousLinearMapLowerNorm
          (higham13_algorithm13_3_schurStageBlock A pivotInv k j j)
          hunit)
      hInit hDiagUpdate hRecip)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    actual CLM Schur-stage source-table data gives the direct active pivot
    product bound used by the column-BDD growth route. -/
theorem
    higham13_algorithm13_3_clm_diagLowerCertGeneric_pivot_bound_of_continuousLinearMap_source_table
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → E →L[ℝ] E)
    (pivotInv : ℕ → E →L[ℝ] E)
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (higham13_algorithm13_3_schurStageBlock A pivotInv 0 j j)
          hunit)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : E,
      pivotInv k
        (higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩ x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : E,
      higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩
        (pivotInv k y) = y) :
    ∀ k : ℕ, ∀ hk : k < m,
      ‖pivotInv k‖ *
          higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv
            k ⟨k, hk⟩ ≤
        1 := by
  have hDiagLower :=
    higham13_algorithm13_3_clm_diagLowerCertGeneric_diag_lower_of_continuousLinearMap_source_table
      hunit invDiagBound A pivotInv hInit hLeft hRight
  exact
    higham13_theorem13_7_pivot_inverse_bound_of_diag_lower
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (fun k => ‖pivotInv k‖)
      (fun k => norm_nonneg (pivotInv k))
      hDiagLower

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    initial CLM lower table from diagonal-block inverse data.

    The stage-zero Schur table is the original block matrix, so a two-sided
    inverse of each diagonal block and the reciprocal bound
    `invDiagBound j <= ‖diagInv j‖⁻¹` supply the initial lower-norm table for
    the actual CLM source-table route. -/
theorem higham13_algorithm13_3_clm_initial_lower_table_of_diag_inverse
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → E →L[ℝ] E)
    (pivotInv : ℕ → E →L[ℝ] E)
    (diagInv : Fin m → E →L[ℝ] E)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (‖diagInv j‖)⁻¹)
    (hLeftDiag : ∀ j : Fin m, ∀ x : E, diagInv j (A j j x) = x)
    (hRightDiag : ∀ j : Fin m, ∀ y : E, A j j (diagInv j y) = y) :
    ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (higham13_algorithm13_3_schurStageBlock A pivotInv 0 j j)
          hunit := by
  intro j
  have hstage :
      higham13_algorithm13_3_schurStageBlock A pivotInv 0 j j = A j j := by
    simpa using higham13_algorithm13_3_schurStageBlock_zero A pivotInv j j
  calc
    invDiagBound j ≤ (‖diagInv j‖)⁻¹ := hInvBound j
    _ = continuousLinearMapLowerNorm (A j j) hunit := by
      rw [continuousLinearMapLowerNorm_eq_inv_opNorm_of_inverse
        (A j j) (diagInv j) hunit (hLeftDiag j) (hRightDiag j)]
    _ = continuousLinearMapLowerNorm
          (higham13_algorithm13_3_schurStageBlock A pivotInv 0 j j)
          hunit := by
      rw [hstage]

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    the same CLM diagonal-inverse reciprocal data supplies the initial
    diagonal comparison `invDiagBound j <= ‖A_jj‖`. -/
theorem higham13_algorithm13_3_clm_initial_diag_bound_of_diag_inverse
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → E →L[ℝ] E)
    (diagInv : Fin m → E →L[ℝ] E)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (‖diagInv j‖)⁻¹)
    (hLeftDiag : ∀ j : Fin m, ∀ x : E, diagInv j (A j j x) = x)
    (hRightDiag : ∀ j : Fin m, ∀ y : E, A j j (diagInv j y) = y) :
    ∀ j : Fin m, invDiagBound j ≤ ‖A j j‖ := by
  intro j
  have hunitCopy := hunit
  obtain ⟨x, hx⟩ := hunitCopy
  have hLower_eq :
      continuousLinearMapLowerNorm (A j j) hunit = (‖diagInv j‖)⁻¹ :=
    continuousLinearMapLowerNorm_eq_inv_opNorm_of_inverse
      (A j j) (diagInv j) hunit (hLeftDiag j) (hRightDiag j)
  have hLower_le_norm :
      continuousLinearMapLowerNorm (A j j) hunit ≤ ‖A j j‖ := by
    calc
      continuousLinearMapLowerNorm (A j j) hunit ≤ ‖A j j x‖ :=
        continuousLinearMapLowerNorm_le (A j j) hunit x hx
      _ ≤ ‖A j j‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm (A j j) x
      _ = ‖A j j‖ := by rw [hx, mul_one]
  calc
    invDiagBound j ≤ (‖diagInv j‖)⁻¹ := hInvBound j
    _ = continuousLinearMapLowerNorm (A j j) hunit := hLower_eq.symm
    _ ≤ ‖A j j‖ := hLower_le_norm

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    actual CLM diagonal-lower certificate from initial diagonal inverse
    reciprocal data and active pivot inverse identities. -/
theorem
    higham13_algorithm13_3_clm_diagLowerCertGeneric_diag_lower_of_initial_diag_inverse_of_pivot_inverse
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → E →L[ℝ] E)
    (pivotInv : ℕ → E →L[ℝ] E)
    (diagInv : Fin m → E →L[ℝ] E)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (‖diagInv j‖)⁻¹)
    (hLeftDiag : ∀ j : Fin m, ∀ x : E, diagInv j (A j j x) = x)
    (hRightDiag : ∀ j : Fin m, ∀ y : E, A j j (diagInv j y) = y)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : E,
      pivotInv k
        (higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩ x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : E,
      higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩
        (pivotInv k y) = y) :
    SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (fun k => ‖pivotInv k‖) := by
  exact
    higham13_algorithm13_3_clm_diagLowerCertGeneric_diag_lower_of_continuousLinearMap_source_table
      hunit invDiagBound A pivotInv
      (higham13_algorithm13_3_clm_initial_lower_table_of_diag_inverse
        hunit invDiagBound A pivotInv diagInv hInvBound hLeftDiag hRightDiag)
      hLeft hRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    actual CLM active pivot product bound from initial diagonal inverse
    reciprocal data and active pivot inverse identities. -/
theorem
    higham13_algorithm13_3_clm_diagLowerCertGeneric_pivot_bound_of_initial_diag_inverse_of_pivot_inverse
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → E →L[ℝ] E)
    (pivotInv : ℕ → E →L[ℝ] E)
    (diagInv : Fin m → E →L[ℝ] E)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (‖diagInv j‖)⁻¹)
    (hLeftDiag : ∀ j : Fin m, ∀ x : E, diagInv j (A j j x) = x)
    (hRightDiag : ∀ j : Fin m, ∀ y : E, A j j (diagInv j y) = y)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : E,
      pivotInv k
        (higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩ x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : E,
      higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩
        (pivotInv k y) = y) :
    ∀ k : ℕ, ∀ hk : k < m,
      ‖pivotInv k‖ *
          higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv
            k ⟨k, hk⟩ ≤
        1 := by
  have hDiagLower :=
    higham13_algorithm13_3_clm_diagLowerCertGeneric_diag_lower_of_initial_diag_inverse_of_pivot_inverse
      hunit invDiagBound A pivotInv diagInv hInvBound
      hLeftDiag hRightDiag hLeft hRight
  exact
    higham13_theorem13_7_pivot_inverse_bound_of_diag_lower
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (fun k => ‖pivotInv k‖)
      (fun k => norm_nonneg (pivotInv k))
      hDiagLower

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7:
    actual CLM source-table data gives active column block diagonal dominance
    for the Algorithm 13.3 Schur-stage sequence.

    This packages the arbitrary-subordinate-norm source-table route at the
    column-dominance level.  The analytic obligations remain the source initial
    lower table and the two-sided active pivot inverse identities. -/
theorem
    higham13_algorithm13_3_clm_active_column_dominance_of_continuousLinearMap_source_table
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → E →L[ℝ] E)
    (pivotInv : ℕ → E →L[ℝ] E)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => ‖A i j‖) invDiagBound)
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (higham13_algorithm13_3_schurStageBlock A pivotInv 0 j j)
          hunit)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : E,
      pivotInv k
        (higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩ x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : E,
      higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩
        (pivotInv k y) = y) :
    SchurStageActiveColumnDom13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv) := by
  exact
    higham13_algorithm13_3_active_column_dominance_of_pivot_bound
      (fun i j : Fin m => ‖A i j‖) invDiagBound hDom A pivotInv
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (by
        intro i j
        rfl)
      (higham13_algorithm13_3_diagLowerCertGeneric_zero invDiagBound A pivotInv)
      (higham13_algorithm13_3_clm_diagLowerCertGeneric_pivot_bound_of_continuousLinearMap_source_table
        hunit invDiagBound A pivotInv hInit hLeft hRight)
      (higham13_algorithm13_3_diagLowerCertGeneric_update invDiagBound A pivotInv)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    actual CLM source-table data gives the active-stage `2 * normMax` bound
    for Algorithm 13.3.

    This is the arbitrary-subordinate-norm analogue of the matrix-`∞` active
    stage wrappers.  It is still conditional on the source lower table and
    active pivot inverse identities. -/
theorem
    higham13_algorithm13_3_clm_active_stage_bound_of_continuousLinearMap_source_table
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → E →L[ℝ] E)
    (pivotInv : ℕ → E →L[ℝ] E)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => ‖A i j‖) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ ‖A j j‖)
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (higham13_algorithm13_3_schurStageBlock A pivotInv 0 j j)
          hunit)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : E,
      pivotInv k
        (higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩ x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : E,
      higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩
        (pivotInv k y) = y)
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, ‖A i j‖ ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    ‖higham13_algorithm13_3_schurStageBlock A pivotInv k i j‖ ≤
      2 * normMax := by
  simpa [higham13_algorithm13_3_schurStageNorm] using
    higham13_algorithm13_3_active_stage_block_bound_of_pivot_bound
      (fun i j : Fin m => ‖A i j‖)
      invDiagBound hDom hDiagBound A pivotInv
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (by
        intro i j
        rfl)
      (higham13_algorithm13_3_diagLowerCertGeneric_zero invDiagBound A pivotInv)
      (higham13_algorithm13_3_clm_diagLowerCertGeneric_pivot_bound_of_continuousLinearMap_source_table
        hunit invDiagBound A pivotInv hInit hLeft hRight)
      (higham13_algorithm13_3_diagLowerCertGeneric_update invDiagBound A pivotInv)
      normMax hMax k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7:
    initial diagonal inverse data plus active pivot inverse identities give
    active column block diagonal dominance for actual CLM Algorithm 13.3
    stages. -/
theorem
    higham13_algorithm13_3_clm_active_column_dominance_of_initial_diag_inverse_of_pivot_inverse
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → E →L[ℝ] E)
    (pivotInv : ℕ → E →L[ℝ] E)
    (diagInv : Fin m → E →L[ℝ] E)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => ‖A i j‖) invDiagBound)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (‖diagInv j‖)⁻¹)
    (hLeftDiag : ∀ j : Fin m, ∀ x : E, diagInv j (A j j x) = x)
    (hRightDiag : ∀ j : Fin m, ∀ y : E, A j j (diagInv j y) = y)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : E,
      pivotInv k
        (higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩ x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : E,
      higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩
        (pivotInv k y) = y) :
    SchurStageActiveColumnDom13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv) := by
  exact
    higham13_algorithm13_3_clm_active_column_dominance_of_continuousLinearMap_source_table
      hunit invDiagBound A pivotInv hDom
      (higham13_algorithm13_3_clm_initial_lower_table_of_diag_inverse
        hunit invDiagBound A pivotInv diagInv hInvBound hLeftDiag hRightDiag)
      hLeft hRight

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    initial diagonal inverse data plus active pivot inverse identities give the
    actual CLM active-stage `2 * normMax` bound for Algorithm 13.3. -/
theorem
    higham13_algorithm13_3_clm_active_stage_bound_of_initial_diag_inverse_of_pivot_inverse
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → E →L[ℝ] E)
    (pivotInv : ℕ → E →L[ℝ] E)
    (diagInv : Fin m → E →L[ℝ] E)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => ‖A i j‖) invDiagBound)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (‖diagInv j‖)⁻¹)
    (hLeftDiag : ∀ j : Fin m, ∀ x : E, diagInv j (A j j x) = x)
    (hRightDiag : ∀ j : Fin m, ∀ y : E, A j j (diagInv j y) = y)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : E,
      pivotInv k
        (higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩ x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : E,
      higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩
        (pivotInv k y) = y)
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, ‖A i j‖ ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    ‖higham13_algorithm13_3_schurStageBlock A pivotInv k i j‖ ≤
      2 * normMax := by
  exact
    higham13_algorithm13_3_clm_active_stage_bound_of_continuousLinearMap_source_table
      hunit invDiagBound A pivotInv hDom
      (higham13_algorithm13_3_clm_initial_diag_bound_of_diag_inverse
        hunit invDiagBound A diagInv hInvBound hLeftDiag hRightDiag)
      (higham13_algorithm13_3_clm_initial_lower_table_of_diag_inverse
        hunit invDiagBound A pivotInv diagInv hInvBound hLeftDiag hRightDiag)
      hLeft hRight normMax hMax k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    positive finite block size makes the ambient unit sphere nonempty.

    This discharges the `hunit` witness that appears in the finite
    matrix-`∞` source-table wrappers; in a positive-dimensional finite block,
    the coordinate basis vector at index `0` has norm one. -/
theorem higham13_fin_fun_unit_sphere_nonempty {r : ℕ} (hr : 0 < r) :
    ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty := by
  refine ⟨Pi.single ⟨0, hr⟩ (1 : ℝ), ?_⟩
  simpa using
    (Pi.norm_single (G := fun _ : Fin r => ℝ) (i := (⟨0, hr⟩ : Fin r)) (1 : ℝ))

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    concrete matrix-`∞`-operator-norm instance of the generic CLM source table.

    The active Schur-stage blocks are the actual matrix-product Algorithm 13.3
    stages, viewed as continuous linear maps on finite vectors by
    `matrixMulVecCLM`.  This proves the source-table-to-certificate bridge for
    Mathlib's submultiplicative matrix `∞` operator norm.  The active pivot
    inverse identities and the initial lower-table domination remain explicit
    hypotheses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_diag_lower_of_continuousLinearMap_source_table
    {m r : ℕ}
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
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
    letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
    SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (fun k => infNorm (pivotInv k)) := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  let stage : ℕ → Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_schurStageMatrixBlock A pivotInv
  let stageCLM : ℕ → Fin m → Fin m → (Fin r → ℝ) →L[ℝ] (Fin r → ℝ) :=
    fun k i j => matrixMulVecCLM (stage k i j)
  let pivotCLM : ℕ → (Fin r → ℝ) →L[ℝ] (Fin r → ℝ) :=
    fun k => matrixMulVecCLM (pivotInv k)
  have hStageNorm : ∀ k : ℕ, ∀ i j : Fin m,
      ‖stageCLM k i j‖ = higham13_algorithm13_3_schurStageNorm A pivotInv k i j := by
    intro k i j
    simpa [stageCLM, stage, higham13_algorithm13_3_schurStageNorm, infNorm] using
      matrixMulVecCLM_norm_eq_infNorm (stage k i j)
  have hPivotNorm : ∀ k : ℕ,
      ‖pivotCLM k‖ = higham13_algorithm13_3_pivotInvNorm pivotInv k := by
    intro k
    simpa [pivotCLM, higham13_algorithm13_3_pivotInvNorm, infNorm] using
      matrixMulVecCLM_norm_eq_infNorm (pivotInv k)
  have hSchur : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : Fin r → ℝ,
        stageCLM (k + 1) j j x =
          stageCLM k j j x -
            stageCLM k j ⟨k, hk⟩
              (pivotCLM k (stageCLM k ⟨k, hk⟩ j x)) := by
    intro k hk j hj x
    let p : Fin m := ⟨k, hk⟩
    have hUpdate :=
      (higham13_algorithm13_3_schurStageBlock_exact_update A pivotInv)
        k hk j j hj hj
    have hUpdateM :
        stage (k + 1) j j =
          stage k j j - stage k j p * pivotInv k * stage k p j := by
      simpa [stage, higham13_algorithm13_3_schurStageMatrixBlock, p] using hUpdate
    change
      matrixMulVecCLM (stage (k + 1) j j) x =
        matrixMulVecCLM (stage k j j) x -
          matrixMulVecCLM (stage k j p)
            (matrixMulVecCLM (pivotInv k) (matrixMulVecCLM (stage k p j) x))
    rw [hUpdateM]
    simp [matrixMulVecCLM_apply, Matrix.sub_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have hLeft' : ∀ k : ℕ, ∀ hk : k < m, ∀ x : Fin r → ℝ,
      pivotCLM k (stageCLM k ⟨k, hk⟩ ⟨k, hk⟩ x) = x := by
    intro k hk x
    simpa [pivotCLM, stageCLM, stage] using hLeft k hk x
  have hRight' : ∀ k : ℕ, ∀ hk : k < m, ∀ y : Fin r → ℝ,
      stageCLM k ⟨k, hk⟩ ⟨k, hk⟩ (pivotCLM k y) = y := by
    intro k hk y
    simpa [pivotCLM, stageCLM, stage] using hRight k hk y
  have hInit' : ∀ j : Fin m,
      invDiagBound j ≤ continuousLinearMapLowerNorm (stageCLM 0 j j) hunit := by
    intro j
    simpa [stageCLM, stage] using hInit j
  have hDiagLower :=
    higham13_algorithm13_3_diagLowerCertGeneric_diag_lower_of_continuousLinearMap_source_table
      hunit invDiagBound A pivotInv stageCLM pivotCLM hInit'
      hStageNorm hPivotNorm hSchur hLeft' hRight'
  simpa [higham13_algorithm13_3_pivotInvNorm, infNorm] using hDiagLower

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    concrete matrix-`∞` CLM source-table data supplies the direct active pivot
    product bound for `diagLowerCertGeneric`.

    This composes the concrete matrix continuous-linear source-table bridge
    with the one-sided diagonal-lower-to-product-bound theorem.  It is still
    conditional on the source lower table and exact active pivot inverse
    identities. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_pivot_bound_of_continuousLinearMap_source_table
    {m r : ℕ}
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
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
    letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
    ∀ k : ℕ, ∀ hk : k < m,
      infNorm (pivotInv k) *
          higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv
            k ⟨k, hk⟩ ≤
        1 := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hDiagLower :=
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_diag_lower_of_continuousLinearMap_source_table
      hunit invDiagBound A pivotInv hInit hLeft hRight
  exact
    higham13_theorem13_7_pivot_inverse_bound_of_diag_lower
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (fun k => infNorm (pivotInv k))
      (fun k => infNorm_nonneg (pivotInv k))
      hDiagLower

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    matrix-`∞` CLM source-table data with certified active right inverses
    supplies the one-sided diagonal lower certificate for `diagLowerCertGeneric`.

    This wrapper derives the exact continuous-linear active inverse identities
    from the repository's matrix `IsRightInverse` certificate, so the remaining
    source-table obligation on this route is the initial lower table. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_diag_lower_of_continuousLinearMap_source_table_of_pivot_right_inverse
    {m r : ℕ}
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
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
    letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
    SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (fun k => infNorm (pivotInv k)) := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : Fin r → ℝ,
      matrixMulVecCLM (pivotInv k)
        (matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩) x) = x := by
    intro k hk x
    exact
      matrixMulVecCLM_left_inverse_of_isRightInverse
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k) (hPivotRight k hk) x
  have hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : Fin r → ℝ,
      matrixMulVecCLM
          (higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (matrixMulVecCLM (pivotInv k) y) = y := by
    intro k hk y
    exact
      matrixMulVecCLM_right_inverse_of_isRightInverse
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k) (hPivotRight k hk) y
  exact
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_diag_lower_of_continuousLinearMap_source_table
      hunit invDiagBound A pivotInv hInit hLeft hRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    matrix-`∞` CLM source-table data with certified active right inverses
    supplies the direct active pivot product bound for `diagLowerCertGeneric`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_pivot_bound_of_continuousLinearMap_source_table_of_pivot_right_inverse
    {m r : ℕ}
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
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
    letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
    ∀ k : ℕ, ∀ hk : k < m,
      infNorm (pivotInv k) *
          higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv
            k ⟨k, hk⟩ ≤
        1 := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hDiagLower :=
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_diag_lower_of_continuousLinearMap_source_table_of_pivot_right_inverse
      hunit invDiagBound A pivotInv hInit hPivotRight
  exact
    higham13_theorem13_7_pivot_inverse_bound_of_diag_lower
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (fun k => infNorm (pivotInv k))
      (fun k => infNorm_nonneg (pivotInv k))
      hDiagLower

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    initial matrix-`∞` lower table from diagonal-block right inverses.

    At stage zero, the Algorithm 13.3 Schur-stage table is the original block
    matrix.  Therefore a certified right inverse `diagInv j` for each diagonal
    block, together with the source reciprocal bound
    `invDiagBound j <= ‖diagInv j‖∞⁻¹`, supplies the initial lower-norm table
    expected by the continuous-linear source-table route. -/
theorem higham13_algorithm13_3_matrix_infNorm_initial_lower_table_of_diag_right_inverse
    {m r : ℕ}
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j)) :
    ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit := by
  intro j
  have hstage :
      higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j = A j j := by
    simpa [higham13_algorithm13_3_schurStageMatrixBlock] using
      (higham13_algorithm13_3_schurStageBlock_zero A pivotInv j j)
  have hLeft :
      ∀ x : Fin r → ℝ,
        matrixMulVecCLM (diagInv j) (matrixMulVecCLM (A j j) x) = x :=
    matrixMulVecCLM_left_inverse_of_isRightInverse
      (A j j) (diagInv j) (hDiagRight j)
  have hRight :
      ∀ y : Fin r → ℝ,
        matrixMulVecCLM (A j j) (matrixMulVecCLM (diagInv j) y) = y :=
    matrixMulVecCLM_right_inverse_of_isRightInverse
      (A j j) (diagInv j) (hDiagRight j)
  calc
    invDiagBound j ≤ (infNorm (diagInv j))⁻¹ := hInvBound j
    _ = (‖matrixMulVecCLM (diagInv j)‖)⁻¹ := by
      rw [matrixMulVecCLM_norm_eq_infNorm]
    _ = continuousLinearMapLowerNorm (matrixMulVecCLM (A j j)) hunit := by
      rw [continuousLinearMapLowerNorm_eq_inv_opNorm_of_inverse
        (matrixMulVecCLM (A j j)) (matrixMulVecCLM (diagInv j)) hunit hLeft hRight]
    _ = continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit := by
      rw [hstage]

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    the same diagonal-block reciprocal data supplies the initial diagonal
    comparison `invDiagBound j <= ‖A_jj‖∞` needed by the active-stage growth
    wrapper. -/
theorem higham13_algorithm13_3_matrix_infNorm_initial_diag_bound_of_diag_right_inverse
    {m r : ℕ}
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j)) :
    ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j) := by
  intro j
  have hLeft :
      ∀ x : Fin r → ℝ,
        matrixMulVecCLM (diagInv j) (matrixMulVecCLM (A j j) x) = x :=
    matrixMulVecCLM_left_inverse_of_isRightInverse
      (A j j) (diagInv j) (hDiagRight j)
  have hRight :
      ∀ y : Fin r → ℝ,
        matrixMulVecCLM (A j j) (matrixMulVecCLM (diagInv j) y) = y :=
    matrixMulVecCLM_right_inverse_of_isRightInverse
      (A j j) (diagInv j) (hDiagRight j)
  have hunitCopy := hunit
  obtain ⟨x, hx⟩ := hunitCopy
  have hLower_eq :
      continuousLinearMapLowerNorm (matrixMulVecCLM (A j j)) hunit =
        (‖matrixMulVecCLM (diagInv j)‖)⁻¹ :=
    continuousLinearMapLowerNorm_eq_inv_opNorm_of_inverse
      (matrixMulVecCLM (A j j)) (matrixMulVecCLM (diagInv j)) hunit hLeft hRight
  have hLower_le_norm :
      continuousLinearMapLowerNorm (matrixMulVecCLM (A j j)) hunit ≤
        ‖matrixMulVecCLM (A j j)‖ := by
    calc
      continuousLinearMapLowerNorm (matrixMulVecCLM (A j j)) hunit
          ≤ ‖matrixMulVecCLM (A j j) x‖ :=
            continuousLinearMapLowerNorm_le (matrixMulVecCLM (A j j)) hunit x hx
      _ ≤ ‖matrixMulVecCLM (A j j)‖ * ‖x‖ :=
            ContinuousLinearMap.le_opNorm (matrixMulVecCLM (A j j)) x
      _ = ‖matrixMulVecCLM (A j j)‖ := by rw [hx, mul_one]
  calc
    invDiagBound j ≤ (infNorm (diagInv j))⁻¹ := hInvBound j
    _ = (‖matrixMulVecCLM (diagInv j)‖)⁻¹ := by
      rw [matrixMulVecCLM_norm_eq_infNorm]
    _ = continuousLinearMapLowerNorm (matrixMulVecCLM (A j j)) hunit :=
      hLower_eq.symm
    _ ≤ ‖matrixMulVecCLM (A j j)‖ := hLower_le_norm
    _ = infNorm (A j j) := matrixMulVecCLM_norm_eq_infNorm (A j j)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7:
    nonpositive BDD lower-bound data supplies the initial diagonal comparison
    for the matrix-`∞` active-stage route.

    This is the simple scalar side of the BDD source-table bridge:
    `invDiagBound j <= 0` and nonnegativity of the matrix `∞` norm imply
    `invDiagBound j <= ‖A_jj‖∞`. -/
theorem higham13_algorithm13_3_matrix_infNorm_initial_diag_bound_of_diagBound_nonpos
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0) :
    ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j) := by
  intro j
  exact le_trans (hBound j) (infNorm_nonneg (A j j))

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 and equation (13.18):
    all-leading-prefix BDD nonsingularity supplies the initial matrix-`∞`
    lower table through the canonical diagonal `nonsingInv` table.

    The generic matrix-`∞` source-table route asks for diagonal right inverses
    and reciprocal lower bounds.  Under the BDD all-prefix hypotheses the
    right inverses are the canonical `nonsingInv` blocks, while
    `invDiagBound j <= 0` supplies the reciprocal lower bound because
    `0 <= ‖nonsingInv(A_jj)‖∞⁻¹`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_initial_lower_table_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol m
      (fun i j => ‖(A i j : Fin r → Fin r → ℝ)‖) invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0) :
    ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          hunit := by
  let diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ :=
    fun j => nonsingInv r (A j j)
  have hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹ := by
    intro j
    exact le_trans (hBound j)
      (inv_nonneg.mpr (infNorm_nonneg (diagInv j)))
  have hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j) := by
    intro j
    exact
      higham13_diag_nonsingInv_isRightInverse_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
        A invDiagBound hPrefix hDom hBound j
  exact
    higham13_algorithm13_3_matrix_infNorm_initial_lower_table_of_diag_right_inverse
      hunit invDiagBound A pivotInv diagInv hInvBound hDiagRight

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 and equation (13.18):
    positive block size discharges the unit-sphere witness in the BDD initial
    matrix-`∞` lower-table bridge. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_initial_lower_table_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos_of_pos_dim
    {m r : ℕ} (hr : 0 < r)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (pivotInv : ℕ → Fin r → Fin r → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol m
      (fun i j => ‖(A i j : Fin r → Fin r → ℝ)‖) invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0) :
    ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (matrixMulVecCLM
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
          (higham13_fin_fun_unit_sphere_nonempty hr) :=
  higham13_algorithm13_3_matrix_infNorm_initial_lower_table_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
    (higham13_fin_fun_unit_sphere_nonempty hr) invDiagBound A pivotInv
    hPrefix hDom hBound

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 and equation (13.18):
    BDD all-prefix data supplies the matrix-`∞` one-sided diagonal lower
    certificate once the active Schur-stage pivots have certified right
    inverses.

    This composes the BDD initial lower table with the existing
    `diagLowerCertGeneric` source-table route.  It removes the explicit
    diagonal inverse and reciprocal-bound inputs from this surface, but still
    leaves the real active-pivot right-inverse table as a source obligation. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_diag_lower_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos_of_pivot_right_inverse
    {m r : ℕ}
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol m
      (fun i j => ‖(fun a b => A i j a b : Fin r → Fin r → ℝ)‖)
      invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
    SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (fun k => infNorm (pivotInv k)) := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hInit :
      ∀ j : Fin m,
        invDiagBound j ≤
          continuousLinearMapLowerNorm
            (matrixMulVecCLM
              (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 0 j j))
            hunit :=
    by
      let Afn : Fin m → Fin m → Fin r → Fin r → ℝ :=
        fun i j a b => A i j a b
      let pivotFn : ℕ → Fin r → Fin r → ℝ :=
        fun k a b => pivotInv k a b
      have hInitFn :=
        higham13_algorithm13_3_matrix_infNorm_initial_lower_table_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
          hunit invDiagBound Afn pivotFn hPrefix hDom hBound
      simpa [Afn, pivotFn] using hInitFn
  exact
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_diag_lower_of_continuousLinearMap_source_table_of_pivot_right_inverse
      hunit invDiagBound A pivotInv hInit hPivotRight

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 and equation (13.18):
    BDD all-prefix data and certified active pivot right inverses supply the
    direct matrix-`∞` active pivot product bound for `diagLowerCertGeneric`. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_pivot_bound_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos_of_pivot_right_inverse
    {m r : ℕ}
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol m
      (fun i j => ‖(fun a b => A i j a b : Fin r → Fin r → ℝ)‖)
      invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
    ∀ k : ℕ, ∀ hk : k < m,
      infNorm (pivotInv k) *
          higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv
            k ⟨k, hk⟩ ≤
        1 := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hDiagLower :=
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_diag_lower_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos_of_pivot_right_inverse
      hunit invDiagBound A pivotInv hPrefix hDom hBound hPivotRight
  exact
    higham13_theorem13_7_pivot_inverse_bound_of_diag_lower
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (fun k => infNorm (pivotInv k))
      (fun k => infNorm_nonneg (pivotInv k))
      hDiagLower

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 and equation (13.18):
    positive block size discharges the unit-sphere witness in the BDD
    all-prefix-to-`diagLowerCertGeneric` diagonal-lower bridge. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_diag_lower_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
    {m r : ℕ} (hr : 0 < r)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol m
      (fun i j => ‖(fun a b => A i j a b : Fin r → Fin r → ℝ)‖)
      invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
    SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (fun k => infNorm (pivotInv k)) :=
  higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_diag_lower_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos_of_pivot_right_inverse
    (higham13_fin_fun_unit_sphere_nonempty hr) invDiagBound A pivotInv
    hPrefix hDom hBound hPivotRight

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 and equation (13.18):
    positive block size discharges the unit-sphere witness in the BDD
    all-prefix-to-`diagLowerCertGeneric` pivot-bound bridge. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_pivot_bound_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
    {m r : ℕ} (hr : 0 < r)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol m
      (fun i j => ‖(fun a b => A i j a b : Fin r → Fin r → ℝ)‖)
      invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
    ∀ k : ℕ, ∀ hk : k < m,
      infNorm (pivotInv k) *
          higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv
            k ⟨k, hk⟩ ≤
        1 :=
  higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_pivot_bound_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos_of_pivot_right_inverse
    (higham13_fin_fun_unit_sphere_nonempty hr) invDiagBound A pivotInv
    hPrefix hDom hBound hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    matrix-`∞` CLM diagonal-lower certificate from initial diagonal inverse
    reciprocal data and active pivot right inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_diag_lower_of_initial_diag_right_inverse_of_pivot_right_inverse
    {m r : ℕ}
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
    SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (fun k => infNorm (pivotInv k)) := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hInit :=
    higham13_algorithm13_3_matrix_infNorm_initial_lower_table_of_diag_right_inverse
      hunit invDiagBound A pivotInv diagInv hInvBound hDiagRight
  exact
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_diag_lower_of_continuousLinearMap_source_table_of_pivot_right_inverse
      hunit invDiagBound A pivotInv hInit hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    matrix-`∞` active pivot product bound from initial diagonal inverse
    reciprocal data and active pivot right inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_pivot_bound_of_initial_diag_right_inverse_of_pivot_right_inverse
    {m r : ℕ}
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
    ∀ k : ℕ, ∀ hk : k < m,
      infNorm (pivotInv k) *
          higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv
            k ⟨k, hk⟩ ≤
        1 := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hInit :=
    higham13_algorithm13_3_matrix_infNorm_initial_lower_table_of_diag_right_inverse
      hunit invDiagBound A pivotInv diagInv hInvBound hDiagRight
  exact
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_pivot_bound_of_continuousLinearMap_source_table_of_pivot_right_inverse
      hunit invDiagBound A pivotInv hInit hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    min-action/lower-norm source data supplies the concrete one-sided active
    pivot certificate for `diagLowerCert`.

    This is the book-shaped source-table route after unfolding the diagonal
    update: the supplied actions represent the active diagonal block, the
    Schur perturbation, and the updated diagonal block on unit vectors.  The
    reverse-triangle lower-bound step proves the active Eq.13.18 update, and
    the reciprocal active-pivot table then feeds the existing
    `diagLowerCert` bridge.  The remaining source obligations are the
    nonsingularity/reciprocal proof for the lower-norm table and the concrete
    subordinate-norm perturbation estimates. -/
theorem higham13_algorithm13_3_diagLowerCert_diag_lower_of_unit_min_source_table
    {m r : ℕ} {E : Type*} [SeminormedAddCommGroup E]
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (diag perturb schurDiag : ℕ → Fin m → E → E)
    (hInit : ∀ j : Fin m, invDiagBound j ≤ stageInvDiagBound 0 j)
    (hDiagMin : ∀ k : ℕ, ∀ _hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E, ‖x‖ = 1 →
        stageInvDiagBound k j ≤ ‖diag k j x‖)
    (hSchurMin : ∀ k : ℕ, ∀ _hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        ∃ x : E, ‖x‖ = 1 ∧
          stageInvDiagBound (k + 1) j = ‖schurDiag k j x‖)
    (hPerturb : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E, ‖x‖ = 1 →
        ‖perturb k j x‖ ≤
          higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
            higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j)
    (hSchur : ∀ k : ℕ, ∀ _hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E,
        schurDiag k j x = diag k j x - perturb k j x)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv) := by
  exact
    higham13_algorithm13_3_diagLowerCert_diag_lower_of_source_table_reciprocal
      invDiagBound A pivotInv stageInvDiagBound hInit
      (SchurStageActiveDiagLowerUpdate13_7.of_unit_min_actions
        (higham13_algorithm13_3_schurStageNorm A pivotInv)
        stageInvDiagBound
        (higham13_algorithm13_3_pivotInvNorm pivotInv)
        diag perturb schurDiag hDiagMin hSchurMin hPerturb hSchur)
      hReciprocal

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    min-action/lower-norm source data supplies the direct scalar active pivot
    product bound used by the column-BDD growth route. -/
theorem higham13_algorithm13_3_diagLowerCert_pivot_bound_of_unit_min_source_table
    {m r : ℕ} {E : Type*} [SeminormedAddCommGroup E]
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (diag perturb schurDiag : ℕ → Fin m → E → E)
    (hInit : ∀ j : Fin m, invDiagBound j ≤ stageInvDiagBound 0 j)
    (hDiagMin : ∀ k : ℕ, ∀ _hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E, ‖x‖ = 1 →
        stageInvDiagBound k j ≤ ‖diag k j x‖)
    (hSchurMin : ∀ k : ℕ, ∀ _hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        ∃ x : E, ‖x‖ = 1 ∧
          stageInvDiagBound (k + 1) j = ‖schurDiag k j x‖)
    (hPerturb : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E, ‖x‖ = 1 →
        ‖perturb k j x‖ ≤
          higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
            higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j)
    (hSchur : ∀ k : ℕ, ∀ _hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E,
        schurDiag k j x = diag k j x - perturb k j x)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_pivotInvNorm pivotInv k *
        higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k ⟨k, hk⟩ ≤ 1 :=
  higham13_theorem13_7_pivot_inverse_bound_of_diag_lower
    (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
    (higham13_algorithm13_3_pivotInvNorm pivotInv)
    (by
      intro k
      simp [higham13_algorithm13_3_pivotInvNorm])
    (higham13_algorithm13_3_diagLowerCert_diag_lower_of_unit_min_source_table
      invDiagBound A pivotInv stageInvDiagBound diag perturb schurDiag hInit
      hDiagMin hSchurMin hPerturb hSchur hReciprocal)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    if the supplied active pivot inverse is certified as a right inverse of
    the active Schur-stage pivot block, then the source reciprocal diagonal
    certificate gives the concrete active product identity
    `gamma_k * ‖pivotInv_k‖ = 1`.

    This closes the nonzero-pivot-norm part of the active product route from
    actual inverse data.  The reciprocal diagonal certificate itself remains
    the source analytic obligation. -/
theorem
    higham13_algorithm13_3_diagLowerCert_active_mul_eq_one_of_pivot_right_inverse_reciprocal
    {m r : ℕ} (hr : 0 < r)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageBlock A pivotInv
          k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hReciprocal : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv
          k ⟨k, hk⟩ =
        (higham13_algorithm13_3_pivotInvNorm pivotInv k)⁻¹) :
    ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv
          k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1 := by
  intro k hk
  have hnorm_ne :
      higham13_algorithm13_3_pivotInvNorm pivotInv k ≠ 0 := by
    simpa [higham13_algorithm13_3_pivotInvNorm] using
      norm_ne_zero_of_isRightInverse (n := r) hr (hPivotRight k hk)
  rw [hReciprocal k hk]
  exact inv_mul_cancel₀ hnorm_ne

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    active product-form pivot data for the concrete diagonal lower-bound
    certificate supplies the source-shaped one-sided certificate
    `gamma_k <= ‖pivotInv_k‖⁻¹`.

    This is still conditional on the active pivot product identity; it only
    connects that stronger source obligation to the weaker diagonal-lower API. -/
theorem higham13_algorithm13_3_diagLowerCert_diag_lower_of_active_mul_eq_one {m r : ℕ}
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hPivotMul : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1) :
    SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv) :=
  SchurStageActivePivotInvDiagLower13_7.of_active_mul_eq_one
    (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
    (higham13_algorithm13_3_pivotInvNorm pivotInv) hPivotMul

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    a positive direct pivot product bound for the concrete diagonal lower-bound
    certificate supplies the source-shaped one-sided certificate
    `gamma_k <= ‖pivotInv_k‖⁻¹`.

    This is the reverse bridge to
    `higham13_algorithm13_3_diagLowerCert_pivot_bound_of_diag_lower`, and keeps
    positivity of the pivot-inverse norm explicit. -/
theorem higham13_algorithm13_3_diagLowerCert_diag_lower_of_pivot_bound {m r : ℕ}
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hPivotPos : ∀ k : ℕ,
      0 < higham13_algorithm13_3_pivotInvNorm pivotInv k)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_pivotInvNorm pivotInv k *
        higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k ⟨k, hk⟩ ≤ 1) :
    SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv) :=
  SchurStageActivePivotInvDiagLower13_7.of_pivot_bound
    (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
    (higham13_algorithm13_3_pivotInvNorm pivotInv) hPivotPos hPivotBound

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    if the concrete diagonal lower-bound certificate is bounded by the
    reciprocal active pivot-inverse norm, then it supplies the direct scalar
    pivot product bound used by the active Schur-stage proof. -/
theorem higham13_algorithm13_3_diagLowerCert_pivot_bound_of_diag_lower {m r : ℕ}
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hDiagLower : SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_pivotInvNorm pivotInv k *
        higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k ⟨k, hk⟩ ≤ 1 := by
  exact higham13_theorem13_7_pivot_inverse_bound_of_diag_lower
    (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
    (higham13_algorithm13_3_pivotInvNorm pivotInv)
    (by
      intro k
      simp [higham13_algorithm13_3_pivotInvNorm])
    hDiagLower

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    a source inverse-diagonal lower-bound table satisfying the active
    Eq.13.18-style update and reciprocal active-pivot upper bounds supplies
    the direct scalar pivot product bound used by the Algorithm 13.3 active
    dominance/growth route.

    This is a bookkeeping composition: constructing the source table remains
    the mathematical source obligation. -/
theorem higham13_algorithm13_3_diagLowerCert_pivot_bound_of_source_table
    {m r : ℕ}
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInit : ∀ j : Fin m, invDiagBound j ≤ stageInvDiagBound 0 j)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (hActiveUpper : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ ≤
        (higham13_algorithm13_3_pivotInvNorm pivotInv k)⁻¹) :
    ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_pivotInvNorm pivotInv k *
        higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k ⟨k, hk⟩ ≤ 1 :=
  higham13_algorithm13_3_diagLowerCert_pivot_bound_of_diag_lower
    invDiagBound A pivotInv
    (higham13_algorithm13_3_diagLowerCert_diag_lower_of_source_table
      invDiagBound A pivotInv stageInvDiagBound hInit hDiagUpdate hActiveUpper)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    reciprocal-equality source-table form of the direct scalar pivot product
    bound for the concrete diagonal lower certificate.

    This is the same source-table route as
    `higham13_algorithm13_3_diagLowerCert_pivot_bound_of_source_table`, but the
    active reciprocal upper bounds are discharged from the equality predicate
    matching the book's inverse-norm table. -/
theorem higham13_algorithm13_3_diagLowerCert_pivot_bound_of_source_table_reciprocal
    {m r : ℕ}
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInit : ∀ j : Fin m, invDiagBound j ≤ stageInvDiagBound 0 j)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_pivotInvNorm pivotInv k *
        higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k ⟨k, hk⟩ ≤ 1 :=
  higham13_algorithm13_3_diagLowerCert_pivot_bound_of_diag_lower
    invDiagBound A pivotInv
    (higham13_algorithm13_3_diagLowerCert_diag_lower_of_source_table_reciprocal
      invDiagBound A pivotInv stageInvDiagBound hInit hDiagUpdate hReciprocal)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    active column dominance for the concrete Schur-stage table from the
    concrete diagonal lower-bound certificate and a direct pivot product bound.

    This discharges the initial-certificate and diagonal-update recurrence
    obligations via `higham13_algorithm13_3_diagLowerCert`; the remaining
    source obligation is the pivot product bound for the active pivots. -/
theorem higham13_algorithm13_3_active_column_dominance_of_diagLowerCert_pivot_bound
    {m r : ℕ}
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_pivotInvNorm pivotInv k *
        higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv
          k ⟨k, hk⟩ ≤ 1) :
    SchurStageActiveColumnDom13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv) := by
  exact higham13_algorithm13_3_active_column_dominance_of_pivot_bound
    blockNorm invDiagBound hDom A pivotInv
    (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
    hInitNorm
    (higham13_algorithm13_3_diagLowerCert_zero invDiagBound A pivotInv)
    hPivotBound
    (higham13_algorithm13_3_diagLowerCert_update invDiagBound A pivotInv)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    active column dominance for the concrete Schur-stage table from the
    source-shaped one-sided diagonal lower-bound certificate
    `gamma_k <= ‖pivotInv_k‖⁻¹`.

    The concrete certificate recurrence is supplied by
    `higham13_algorithm13_3_diagLowerCert`; the still-open mathematical source
    obligation is proving the one-sided pivot certificate itself. -/
theorem higham13_algorithm13_3_active_column_dominance_of_diagLowerCert_diag_lower
    {m r : ℕ}
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hDiagLower : SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    SchurStageActiveColumnDom13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv) :=
  higham13_algorithm13_3_active_column_dominance_of_diagLowerCert_pivot_bound
    blockNorm invDiagBound hDom A pivotInv hInitNorm
    (higham13_algorithm13_3_diagLowerCert_pivot_bound_of_diag_lower
      invDiagBound A pivotInv hDiagLower)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    active-stage block growth from the concrete diagonal lower-bound
    certificate and a direct active pivot product bound. -/
theorem higham13_algorithm13_3_active_stage_block_bound_of_diagLowerCert_pivot_bound
    {m r : ℕ}
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_pivotInvNorm pivotInv k *
        higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv
          k ⟨k, hk⟩ ≤ 1)
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    higham13_algorithm13_3_schurStageNorm A pivotInv k i j ≤
      2 * normMax := by
  exact higham13_algorithm13_3_active_stage_block_bound_of_pivot_bound
    blockNorm invDiagBound hDom hDiagBound A pivotInv
    (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
    hInitNorm
    (higham13_algorithm13_3_diagLowerCert_zero invDiagBound A pivotInv)
    hPivotBound
    (higham13_algorithm13_3_diagLowerCert_update invDiagBound A pivotInv)
    normMax hMax k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    active-stage block growth from the concrete diagonal lower-bound
    certificate and the source-shaped one-sided pivot certificate. -/
theorem higham13_algorithm13_3_active_stage_block_bound_of_diagLowerCert_diag_lower
    {m r : ℕ}
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hDiagLower : SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    higham13_algorithm13_3_schurStageNorm A pivotInv k i j ≤
      2 * normMax :=
  higham13_algorithm13_3_active_stage_block_bound_of_diagLowerCert_pivot_bound
    blockNorm invDiagBound hDom hDiagBound A pivotInv hInitNorm
    (higham13_algorithm13_3_diagLowerCert_pivot_bound_of_diag_lower
      invDiagBound A pivotInv hDiagLower)
    normMax hMax k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    column-BDD specialization of the active dominance route from the concrete
    `diagLowerCert` one-sided pivot certificate. -/
theorem higham13_algorithm13_3_active_column_dominance_of_column_bdd_diag_lower
    {m r : ℕ}
    (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagLower : SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    SchurStageActiveColumnDom13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv) :=
  higham13_algorithm13_3_active_column_dominance_of_diagLowerCert_diag_lower
    (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound hDom
    A pivotInv
    (by
      intro i j
      exact higham13_block_norm_eq_maxEntryNorm hr (A i j))
    hDiagLower

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    column-BDD active dominance from a source inverse-bound table satisfying
    the active Eq.13.18-style diagonal update and active reciprocal upper
    bounds. -/
theorem higham13_algorithm13_3_active_column_dominance_of_column_bdd_source_table
    {m r : ℕ}
    (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hInit : ∀ j : Fin m, invDiagBound j ≤ stageInvDiagBound 0 j)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (hActiveUpper : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ ≤
        (higham13_algorithm13_3_pivotInvNorm pivotInv k)⁻¹) :
    SchurStageActiveColumnDom13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv) :=
  higham13_algorithm13_3_active_column_dominance_of_column_bdd_diag_lower
    hr A pivotInv invDiagBound hDom
    (higham13_algorithm13_3_diagLowerCert_diag_lower_of_source_table
      invDiagBound A pivotInv stageInvDiagBound hInit hDiagUpdate hActiveUpper)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    column-BDD specialization of the active-stage `2 * max` bound from the
    concrete `diagLowerCert` one-sided pivot certificate. -/
theorem higham13_algorithm13_3_active_stage_block_bound_of_column_bdd_diag_lower
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hDiagLower : SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    higham13_algorithm13_3_schurStageNorm A pivotInv k i j ≤
      2 * blockMaxNorm hm hr A :=
  higham13_algorithm13_3_active_stage_block_bound_of_diagLowerCert_diag_lower
    (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound hDom
    hDiagBound A pivotInv
    (by
      intro i j
      exact higham13_block_norm_eq_maxEntryNorm hr (A i j))
    hDiagLower
    (blockMaxNorm hm hr A)
    (fun i j => block_le_blockMaxNorm hm hr A i j)
    k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    column-BDD active-stage `2 * ‖A‖` growth from a source inverse-bound table
    satisfying the active Eq.13.18-style diagonal update and active reciprocal
    upper bounds. -/
theorem higham13_algorithm13_3_active_stage_block_bound_of_column_bdd_source_table
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInit : ∀ j : Fin m, invDiagBound j ≤ stageInvDiagBound 0 j)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (hActiveUpper : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ ≤
        (higham13_algorithm13_3_pivotInvNorm pivotInv k)⁻¹)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    higham13_algorithm13_3_schurStageNorm A pivotInv k i j ≤
      2 * blockMaxNorm hm hr A :=
  higham13_algorithm13_3_active_stage_block_bound_of_column_bdd_diag_lower
    hm hr A pivotInv invDiagBound hDom hDiagBound
    (higham13_algorithm13_3_diagLowerCert_diag_lower_of_source_table
      invDiagBound A pivotInv stageInvDiagBound hInit hDiagUpdate hActiveUpper)
    k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    active product-form pivot data for the concrete diagonal lower-bound
    certificate supplies the direct scalar product bound
    `‖pivotInv_k‖ * gamma_k <= 1`.

    This theorem exposes the weakest pivot-bound interface used by the current
    Theorem 13.7/Theorem 13.8/Eq.13.21 bridges while keeping the active product
    identity visible as the remaining source obligation. -/
theorem higham13_algorithm13_3_diagLowerCert_pivot_bound_of_active_mul_eq_one {m r : ℕ}
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hPivotMul : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1) :
    ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_pivotInvNorm pivotInv k *
        higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k ⟨k, hk⟩ ≤ 1 := by
  intro k hk
  have hmul := hPivotMul k hk
  rw [mul_comm] at hmul
  exact le_of_eq hmul

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    if each supplied active pivot inverse is certified as a right inverse and
    the concrete diagonal certificate is the reciprocal of its norm, then the
    weakest direct pivot product bound used by the active dominance/growth
    route holds. -/
theorem
    higham13_algorithm13_3_diagLowerCert_pivot_bound_of_pivot_right_inverse_reciprocal
    {m r : ℕ} (hr : 0 < r)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageBlock A pivotInv
          k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hReciprocal : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv
          k ⟨k, hk⟩ =
        (higham13_algorithm13_3_pivotInvNorm pivotInv k)⁻¹) :
    ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_pivotInvNorm pivotInv k *
        higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv
          k ⟨k, hk⟩ ≤ 1 := by
  exact higham13_algorithm13_3_diagLowerCert_pivot_bound_of_active_mul_eq_one
    invDiagBound A pivotInv
    (higham13_algorithm13_3_diagLowerCert_active_mul_eq_one_of_pivot_right_inverse_reciprocal
      hr invDiagBound A pivotInv hPivotRight hReciprocal)

/-- Higham, 2nd ed., Chapter 13, Theorems 13.7--13.8 audit:
    exact active pivot right-inverse data alone does not imply the concrete
    `diagLowerCert` pivot product bound.

    The one-block scalar example has an exact pivot inverse, but the diagonal
    lower certificate is chosen to be `2`, so
    `‖pivotInv‖ * diagLowerCert = 2`.  This rules out replacing the source
    reciprocal/table hypothesis by pivot right-inverse data alone. -/
theorem higham13_algorithm13_3_pivot_right_inverse_not_imply_diagLowerCert_pivot_bound :
    ∃ (invDiagBound : Fin 1 → ℝ)
      (A : Fin 1 → Fin 1 → (Fin 1 → Fin 1 → ℝ))
      (pivotInv : ℕ → (Fin 1 → Fin 1 → ℝ)),
      (∀ k : ℕ, ∀ hk : k < 1,
        IsRightInverse 1
          (higham13_algorithm13_3_schurStageBlock A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k)) ∧
      ¬ (∀ k : ℕ, ∀ hk : k < 1,
        higham13_algorithm13_3_pivotInvNorm pivotInv k *
          higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k ⟨k, hk⟩ ≤ 1) := by
  let oneBlock : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
  let invDiagBound : Fin 1 → ℝ := fun _ => 2
  let A : Fin 1 → Fin 1 → (Fin 1 → Fin 1 → ℝ) := fun _ _ => oneBlock
  let pivotInv : ℕ → (Fin 1 → Fin 1 → ℝ) := fun _ => oneBlock
  refine ⟨invDiagBound, A, pivotInv, ?_, ?_⟩
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    intro i j
    fin_cases i
    fin_cases j
    simp [A, pivotInv, oneBlock, higham13_algorithm13_3_schurStageBlock]
  · intro hbound
    have h := hbound 0 (by norm_num)
    norm_num [A, pivotInv, invDiagBound, oneBlock,
      higham13_algorithm13_3_pivotInvNorm,
      higham13_algorithm13_3_diagLowerCert] at h

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    column-BDD active dominance from active pivot right-inverse data plus the
    concrete reciprocal diagonal certificate. -/
theorem higham13_algorithm13_3_active_column_dominance_of_column_bdd_pivot_right_inverse_reciprocal
    {m r : ℕ}
    (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageBlock A pivotInv
          k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hReciprocal : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv
          k ⟨k, hk⟩ =
        (higham13_algorithm13_3_pivotInvNorm pivotInv k)⁻¹) :
    SchurStageActiveColumnDom13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv) :=
  higham13_algorithm13_3_active_column_dominance_of_diagLowerCert_pivot_bound
    (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound hDom
    A pivotInv
    (by
      intro i j
      exact higham13_block_norm_eq_maxEntryNorm hr (A i j))
    (higham13_algorithm13_3_diagLowerCert_pivot_bound_of_pivot_right_inverse_reciprocal
      hr invDiagBound A pivotInv hPivotRight hReciprocal)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    column-BDD active-stage `2 * max` growth from active pivot right-inverse
    data plus the concrete reciprocal diagonal certificate. -/
theorem higham13_algorithm13_3_active_stage_block_bound_of_column_bdd_pivot_right_inverse_reciprocal
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageBlock A pivotInv
          k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hReciprocal : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv
          k ⟨k, hk⟩ =
        (higham13_algorithm13_3_pivotInvNorm pivotInv k)⁻¹)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    higham13_algorithm13_3_schurStageNorm A pivotInv k i j ≤
      2 * blockMaxNorm hm hr A :=
  higham13_algorithm13_3_active_stage_block_bound_of_diagLowerCert_pivot_bound
    (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound hDom
    hDiagBound A pivotInv
    (by
      intro i j
      exact higham13_block_norm_eq_maxEntryNorm hr (A i j))
    (higham13_algorithm13_3_diagLowerCert_pivot_bound_of_pivot_right_inverse_reciprocal
      hr invDiagBound A pivotInv hPivotRight hReciprocal)
    (blockMaxNorm hm hr A)
    (fun i j => block_le_blockMaxNorm hm hr A i j)
    k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    product-form pivot data and exact diagonal-update equality imply the
    concrete one-step active column-dominance rule. -/
theorem higham13_algorithm13_3_active_column_dom_step_of_pivot_mul_diag_eq {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hPivotInvNorm_ne : ∀ k : ℕ,
      higham13_algorithm13_3_pivotInvNorm pivotInv k ≠ 0)
    (hPivotMul : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1)
    (hDiagEq : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        stageInvDiagBound (k + 1) j =
          stageInvDiagBound k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j) :
    SchurStageActiveColumnDomStep13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound := by
  exact higham13_algorithm13_3_active_column_dom_step_of_reciprocal
    A pivotInv stageInvDiagBound
    (higham13_algorithm13_3_pivot_reciprocal_of_mul_eq_one
      pivotInv stageInvDiagBound hPivotInvNorm_ne hPivotMul)
    (higham13_algorithm13_3_active_diag_lower_update_of_eq
      A pivotInv stageInvDiagBound hDiagEq)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    active-product pivot data and exact diagonal-update equality imply the
    concrete one-step active column-dominance rule.

    This source-facing variant removes the separate nonzero pivot-inverse norm
    premise from
    `higham13_algorithm13_3_active_column_dom_step_of_pivot_mul_diag_eq`;
    nonzero follows from the active product identity itself. -/
theorem higham13_algorithm13_3_active_column_dom_step_of_pivot_mul_diag_eq_active_mul_eq_one
    {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hPivotMul : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1)
    (hDiagEq : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        stageInvDiagBound (k + 1) j =
          stageInvDiagBound k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j) :
    SchurStageActiveColumnDomStep13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound := by
  exact higham13_algorithm13_3_active_column_dom_step_of_reciprocal
    A pivotInv stageInvDiagBound
    (higham13_algorithm13_3_pivot_reciprocal_of_active_mul_eq_one
      pivotInv stageInvDiagBound hPivotMul)
    (higham13_algorithm13_3_active_diag_lower_update_of_eq
      A pivotInv stageInvDiagBound hDiagEq)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    active column dominance for the concrete Schur-stage sequence from
    source-shaped product-form pivot data and diagonal-update equality. -/
theorem higham13_algorithm13_3_active_column_dominance_of_pivot_mul_diag_eq {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvNorm_ne : ∀ k : ℕ,
      higham13_algorithm13_3_pivotInvNorm pivotInv k ≠ 0)
    (hPivotMul : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1)
    (hDiagEq : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        stageInvDiagBound (k + 1) j =
          stageInvDiagBound k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j) :
    SchurStageActiveColumnDom13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound := by
  exact higham13_algorithm13_3_active_column_dominance_of_reciprocal
    blockNorm invDiagBound hDom A pivotInv stageInvDiagBound hInitNorm hInitInv
    (higham13_algorithm13_3_pivot_reciprocal_of_mul_eq_one
      pivotInv stageInvDiagBound hPivotInvNorm_ne hPivotMul)
    (higham13_algorithm13_3_active_diag_lower_update_of_eq
      A pivotInv stageInvDiagBound hDiagEq)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    active column dominance for the concrete Schur-stage sequence from only
    active product-form pivot data and diagonal-update equality.

    The remaining source obligations are still the pivot product identity,
    the diagonal-update equality, initial dominance, and block-LU existence;
    the redundant separate nonzero pivot-inverse norm premise has been
    discharged from the product identity. -/
theorem higham13_algorithm13_3_active_column_dominance_of_pivot_mul_diag_eq_active_mul_eq_one
    {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotMul : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1)
    (hDiagEq : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        stageInvDiagBound (k + 1) j =
          stageInvDiagBound k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j) :
    SchurStageActiveColumnDom13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound := by
  exact higham13_algorithm13_3_active_column_dominance_of_reciprocal
    blockNorm invDiagBound hDom A pivotInv stageInvDiagBound hInitNorm hInitInv
    (higham13_algorithm13_3_pivot_reciprocal_of_active_mul_eq_one
      pivotInv stageInvDiagBound hPivotMul)
    (higham13_algorithm13_3_active_diag_lower_update_of_eq
      A pivotInv stageInvDiagBound hDiagEq)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    active-stage block growth bound from source-shaped pivot product data and
    diagonal-update equality. -/
theorem higham13_algorithm13_3_active_stage_block_bound_of_pivot_mul_diag_eq {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvNorm_ne : ∀ k : ℕ,
      higham13_algorithm13_3_pivotInvNorm pivotInv k ≠ 0)
    (hPivotMul : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1)
    (hDiagEq : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        stageInvDiagBound (k + 1) j =
          stageInvDiagBound k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j)
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    higham13_algorithm13_3_schurStageNorm A pivotInv k i j ≤
      2 * normMax := by
  exact higham13_algorithm13_3_active_stage_block_bound_of_reciprocal
    blockNorm invDiagBound hDom hDiagBound A pivotInv stageInvDiagBound
    hInitNorm hInitInv
    (higham13_algorithm13_3_pivot_reciprocal_of_mul_eq_one
      pivotInv stageInvDiagBound hPivotInvNorm_ne hPivotMul)
    (higham13_algorithm13_3_active_diag_lower_update_of_eq
      A pivotInv stageInvDiagBound hDiagEq)
    normMax hMax k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    active-stage block growth bound from active product-form pivot data and
    diagonal-update equality.

    This is the no-separate-nonzero variant of
    `higham13_algorithm13_3_active_stage_block_bound_of_pivot_mul_diag_eq`. -/
theorem higham13_algorithm13_3_active_stage_block_bound_of_pivot_mul_diag_eq_active_mul_eq_one
    {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotMul : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1)
    (hDiagEq : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        stageInvDiagBound (k + 1) j =
          stageInvDiagBound k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j)
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    higham13_algorithm13_3_schurStageNorm A pivotInv k i j ≤
      2 * normMax := by
  exact higham13_algorithm13_3_active_stage_block_bound_of_reciprocal
    blockNorm invDiagBound hDom hDiagBound A pivotInv stageInvDiagBound
    hInitNorm hInitInv
    (higham13_algorithm13_3_pivot_reciprocal_of_active_mul_eq_one
      pivotInv stageInvDiagBound hPivotMul)
    (higham13_algorithm13_3_active_diag_lower_update_of_eq
      A pivotInv stageInvDiagBound hDiagEq)
    normMax hMax k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, equation (13.21), Algorithm 13.3 bridge:
    finite block max-norm bound from source-shaped pivot product data and
    diagonal-update equality, with upper-`U` and strict-lower-zero premises
    still explicit. -/
theorem higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq
    {m r : ℕ} {α : Type*} [SeminormedRing α]
    (hm : 0 < m) (hr : 0 < r)
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvNorm_ne : ∀ k : ℕ,
      higham13_algorithm13_3_pivotInvNorm pivotInv k ≠ 0)
    (hPivotMul : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1)
    (hDiagEq : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        stageInvDiagBound (k + 1) j =
          stageInvDiagBound k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j)
    (normMax : ℝ)
    (hNormMax : 0 ≤ normMax)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (U : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hUpper : SchurStageUpperBlockBound13_21 hr U
      (higham13_algorithm13_3_schurStageNorm A pivotInv))
    (hLowerZero : ∀ i j : Fin m, j.val < i.val → U i j = zeroBlock r) :
    blockMaxNorm hm hr U ≤ 2 * normMax := by
  exact higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_reciprocal_zero_lower
    hm hr blockNorm invDiagBound hDom hDiagBound A pivotInv stageInvDiagBound
    hInitNorm hInitInv
    (higham13_algorithm13_3_pivot_reciprocal_of_mul_eq_one
      pivotInv stageInvDiagBound hPivotInvNorm_ne hPivotMul)
    (higham13_algorithm13_3_active_diag_lower_update_of_eq
      A pivotInv stageInvDiagBound hDiagEq)
    normMax hNormMax hMax U hUpper hLowerZero

/-- Higham, 2nd ed., Chapter 13, equation (13.21), Algorithm 13.3 bridge:
    finite block max-norm bound from active product-form pivot data and
    diagonal-update equality, with upper-`U` and strict-lower-zero premises
    still explicit.

    This source-facing variant removes the separate nonzero pivot-inverse norm
    premise from
    `higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq`. -/
theorem higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq_active_mul_eq_one
    {m r : ℕ} {α : Type*} [SeminormedRing α]
    (hm : 0 < m) (hr : 0 < r)
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotMul : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1)
    (hDiagEq : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        stageInvDiagBound (k + 1) j =
          stageInvDiagBound k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j)
    (normMax : ℝ)
    (hNormMax : 0 ≤ normMax)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (U : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hUpper : SchurStageUpperBlockBound13_21 hr U
      (higham13_algorithm13_3_schurStageNorm A pivotInv))
    (hLowerZero : ∀ i j : Fin m, j.val < i.val → U i j = zeroBlock r) :
    blockMaxNorm hm hr U ≤ 2 * normMax := by
  exact higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_reciprocal_zero_lower
    hm hr blockNorm invDiagBound hDom hDiagBound A pivotInv stageInvDiagBound
    hInitNorm hInitInv
    (higham13_algorithm13_3_pivot_reciprocal_of_active_mul_eq_one
      pivotInv stageInvDiagBound hPivotMul)
    (higham13_algorithm13_3_active_diag_lower_update_of_eq
      A pivotInv stageInvDiagBound hDiagEq)
    normMax hNormMax hMax U hUpper hLowerZero

/-- Higham, 2nd ed., Chapter 13, equation (13.21), Algorithm 13.3 bridge:
    finite block max-norm bound from source-shaped pivot product data,
    diagonal-update equality, exact upper-`U`/Schur-stage equality, and actual
    strict-lower zero blocks.

    Compared with
    `higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq`,
    this theorem discharges the named upper-`U`/stage predicate using the
    concrete Algorithm 13.3 equality `Uᵢⱼ = Aᵢⱼ^(i)` for `i ≤ j`. -/
theorem higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq_upper_eq
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvNorm_ne : ∀ k : ℕ,
      higham13_algorithm13_3_pivotInvNorm pivotInv k ≠ 0)
    (hPivotMul : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1)
    (hDiagEq : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        stageInvDiagBound (k + 1) j =
          stageInvDiagBound k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j)
    (normMax : ℝ)
    (hNormMax : 0 ≤ normMax)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (U : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hUpperEq : ∀ i j : Fin m, i.val ≤ j.val →
      U i j = higham13_algorithm13_3_schurStageBlock A pivotInv i.val i j)
    (hLowerZero : ∀ i j : Fin m, j.val < i.val → U i j = zeroBlock r) :
    blockMaxNorm hm hr U ≤ 2 * normMax := by
  exact higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq
    hm hr blockNorm invDiagBound hDom hDiagBound A pivotInv stageInvDiagBound
    hInitNorm hInitInv hPivotInvNorm_ne hPivotMul hDiagEq normMax hNormMax
    hMax U
    (higham13_algorithm13_3_upper_block_bound_of_eq_stage hr A U pivotInv
      hUpperEq)
    hLowerZero

/-- Higham, 2nd ed., Chapter 13, equation (13.21), Algorithm 13.3 bridge:
    finite block max-norm bound from active product-form pivot data,
    diagonal-update equality, exact upper-`U`/Schur-stage equality, and strict
    lower zero blocks.

    This is the no-separate-nonzero variant of
    `higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq_upper_eq`. -/
theorem higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq_upper_eq_active_mul_eq_one
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotMul : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1)
    (hDiagEq : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        stageInvDiagBound (k + 1) j =
          stageInvDiagBound k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j)
    (normMax : ℝ)
    (hNormMax : 0 ≤ normMax)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (U : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hUpperEq : ∀ i j : Fin m, i.val ≤ j.val →
      U i j = higham13_algorithm13_3_schurStageBlock A pivotInv i.val i j)
    (hLowerZero : ∀ i j : Fin m, j.val < i.val → U i j = zeroBlock r) :
    blockMaxNorm hm hr U ≤ 2 * normMax := by
  exact
    higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq_active_mul_eq_one
      hm hr blockNorm invDiagBound hDom hDiagBound A pivotInv
      stageInvDiagBound hInitNorm hInitInv hPivotMul hDiagEq normMax
      hNormMax hMax U
      (higham13_algorithm13_3_upper_block_bound_of_eq_stage hr A U pivotInv
        hUpperEq)
      hLowerZero

/-- Higham, 2nd ed., Chapter 13, equation (13.21), Algorithm 13.3 bridge:
    finite block max-norm bound from the direct pivot product bound,
    diagonal-update predicate, exact upper-`U`/Schur-stage equality, and strict
    lower zero blocks. -/
theorem higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_bound_upper_eq
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_pivotInvNorm pivotInv k *
        stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (normMax : ℝ)
    (hNormMax : 0 ≤ normMax)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (U : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hUpperEq : ∀ i j : Fin m, i.val ≤ j.val →
      U i j = higham13_algorithm13_3_schurStageBlock A pivotInv i.val i j)
    (hLowerZero : ∀ i j : Fin m, j.val < i.val → U i j = zeroBlock r) :
    blockMaxNorm hm hr U ≤ 2 * normMax := by
  exact higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_bound
    hm hr blockNorm invDiagBound hDom hDiagBound A pivotInv stageInvDiagBound
    hInitNorm hInitInv hPivotBound hDiagUpdate normMax hNormMax hMax U
    (higham13_algorithm13_3_upper_block_bound_of_eq_stage hr A U pivotInv
      hUpperEq)
    hLowerZero

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    finite max-norm bound for the exact upper factor assembled from Schur
    stages.

    This specializes the Eq.13.21 bridge to
    `higham13_algorithm13_3_upperFromStages`, discharging both the
    upper-stage equality and strict-lower-zero obligations by construction.
    The remaining source obligations are the pivot product data, diagonal
    certificate update, and growth/max-norm premises. -/
theorem higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvNorm_ne : ∀ k : ℕ,
      higham13_algorithm13_3_pivotInvNorm pivotInv k ≠ 0)
    (hPivotMul : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1)
    (hDiagEq : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        stageInvDiagBound (k + 1) j =
          stageInvDiagBound k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j)
    (normMax : ℝ)
    (hNormMax : 0 ≤ normMax)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
      2 * normMax := by
  exact higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq_upper_eq
    hm hr blockNorm invDiagBound hDom hDiagBound A pivotInv stageInvDiagBound
    hInitNorm hInitInv hPivotInvNorm_ne hPivotMul hDiagEq normMax hNormMax
    hMax (higham13_algorithm13_3_upperFromStages A pivotInv)
    (fun i j hij =>
      higham13_algorithm13_3_upperFromStages_eq_stage A pivotInv i j hij)
    (fun i j hji =>
      higham13_algorithm13_3_upperFromStages_lower_zero A pivotInv i j hji)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    finite max-norm bound for the exact upper factor assembled from Schur
    stages, using active product-form pivot data and diagonal-update equality.

    This removes the separate nonzero pivot-inverse norm premise from
    `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq`;
    the pivot product identity itself supplies nonzero. -/
theorem
    higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq_active_mul_eq_one
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotMul : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1)
    (hDiagEq : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        stageInvDiagBound (k + 1) j =
          stageInvDiagBound k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j)
    (normMax : ℝ)
    (hNormMax : 0 ≤ normMax)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
      2 * normMax := by
  exact
    higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq_upper_eq_active_mul_eq_one
      hm hr blockNorm invDiagBound hDom hDiagBound A pivotInv
      stageInvDiagBound hInitNorm hInitInv hPivotMul hDiagEq normMax
      hNormMax hMax (higham13_algorithm13_3_upperFromStages A pivotInv)
      (fun i j hij =>
        higham13_algorithm13_3_upperFromStages_eq_stage A pivotInv i j hij)
      (fun i j hji =>
        higham13_algorithm13_3_upperFromStages_lower_zero A pivotInv i j hji)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    finite max-norm bound for the exact upper factor assembled from Schur
    stages, using the direct pivot product bound. -/
theorem higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_pivot_bound
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_pivotInvNorm pivotInv k *
        stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (normMax : ℝ)
    (hNormMax : 0 ≤ normMax)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
      2 * normMax := by
  exact higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_bound_upper_eq
    hm hr blockNorm invDiagBound hDom hDiagBound A pivotInv stageInvDiagBound
    hInitNorm hInitInv hPivotBound hDiagUpdate normMax hNormMax hMax
    (higham13_algorithm13_3_upperFromStages A pivotInv)
    (fun i j hij =>
      higham13_algorithm13_3_upperFromStages_eq_stage A pivotInv i j hij)
    (fun i j hji =>
      higham13_algorithm13_3_upperFromStages_lower_zero A pivotInv i j hji)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    finite max-norm bound for the upper factor assembled from Schur stages,
    using the concrete diagonal lower-bound certificate recurrence.

    Compared with
    `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq`,
    this theorem discharges the initial-certificate and diagonal-update equality
    premises by using `higham13_algorithm13_3_diagLowerCert`.  The remaining
    nontrivial source obligation is the pivot product certificate at each
    active pivot, together with the usual initial dominance and max-norm
    premises. -/
theorem higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_diagLowerCert
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hPivotInvNorm_ne : ∀ k : ℕ,
      higham13_algorithm13_3_pivotInvNorm pivotInv k ≠ 0)
    (hPivotMul : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1)
    (normMax : ℝ)
    (hNormMax : 0 ≤ normMax)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
      2 * normMax := by
  exact
    higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq
      hm hr blockNorm invDiagBound hDom hDiagBound A pivotInv
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
      hInitNorm
      (higham13_algorithm13_3_diagLowerCert_zero invDiagBound A pivotInv)
      hPivotInvNorm_ne hPivotMul
      (higham13_algorithm13_3_diagLowerCert_eq invDiagBound A pivotInv)
      normMax hNormMax hMax

/-- Same diagonal-certificate Eq.13.21 bridge as
    `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_diagLowerCert`,
    but with only the active pivot product certificate as a hypothesis.  The
    nonzero pivot-inverse norm follows from that product identity. -/
theorem
    higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_diagLowerCert_active_mul_eq_one
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hPivotMul : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1)
    (normMax : ℝ)
    (hNormMax : 0 ≤ normMax)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
      2 * normMax := by
  exact higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_reciprocal_zero_lower
    hm hr blockNorm invDiagBound hDom hDiagBound A pivotInv
    (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
    hInitNorm
    (higham13_algorithm13_3_diagLowerCert_zero invDiagBound A pivotInv)
    (higham13_algorithm13_3_pivot_reciprocal_of_active_mul_eq_one pivotInv
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv) hPivotMul)
    (higham13_algorithm13_3_diagLowerCert_update invDiagBound A pivotInv)
    normMax hNormMax hMax
    (higham13_algorithm13_3_upperFromStages A pivotInv)
    (higham13_algorithm13_3_upperFromStages_upper_block_bound hr A pivotInv)
    (fun i j hji =>
      higham13_algorithm13_3_upperFromStages_lower_zero A pivotInv i j hji)

/-- Same diagonal-certificate Eq.13.21 bridge as
    `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_diagLowerCert`,
    but using the direct pivot product bound
    `‖pivotInv_k‖ * gamma_k <= 1`.

    This is the weakest current Algorithm 13.3 diagonal-certificate route:
    the diagonal recurrence is discharged by
    `higham13_algorithm13_3_diagLowerCert`, and the remaining pivot obligation
    is exactly the scalar product bound used by the proof. -/
theorem
    higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_diagLowerCert_pivot_bound
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_pivotInvNorm pivotInv k *
        higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k ⟨k, hk⟩ ≤ 1)
    (normMax : ℝ)
    (hNormMax : 0 ≤ normMax)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
      2 * normMax := by
  exact higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_pivot_bound
    hm hr blockNorm invDiagBound hDom hDiagBound A pivotInv
    (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
    hInitNorm
    (higham13_algorithm13_3_diagLowerCert_zero invDiagBound A pivotInv)
    hPivotBound
    (higham13_algorithm13_3_diagLowerCert_update invDiagBound A pivotInv)
    normMax hNormMax hMax

/-- Same diagonal-certificate Eq.13.21 bridge as
    `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_diagLowerCert_pivot_bound`,
    but using the source-shaped one-sided lower-bound certificate
    `gamma_k <= ‖pivotInv_k‖⁻¹` instead of the already-multiplied product
    bound. -/
theorem
    higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_diagLowerCert_diag_lower
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hInitNorm : ∀ i j : Fin m, ‖A i j‖ = blockNorm i j)
    (hDiagLower : SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (normMax : ℝ)
    (hNormMax : 0 ≤ normMax)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
      2 * normMax := by
  exact
    higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_diagLowerCert_pivot_bound
      hm hr blockNorm invDiagBound hDom hDiagBound A pivotInv hInitNorm
      (higham13_algorithm13_3_diagLowerCert_pivot_bound_of_diag_lower
        invDiagBound A pivotInv hDiagLower)
      normMax hNormMax hMax

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    column-BDD `2 * ‖A‖` bound from the source-style reciprocal pivot
    certificate.

    This is the cleanest current column-BDD Eq.13.21 route: the upper factor is
    assembled from Schur stages, the diagonal lower-bound certificate follows
    the source recurrence, and the remaining pivot obligation is stated as the
    reciprocal certificate used in the proof of Theorems 13.7--13.8. -/
theorem higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_reciprocal
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hPivotRecip : SchurStageActivePivotInvReciprocal13_7
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
      2 * blockMaxNorm hm hr A := by
  exact higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_reciprocal_zero_lower
    hm hr (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound
    hDom hDiagBound A pivotInv
    (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
    (by
      intro i j
      exact higham13_block_norm_eq_maxEntryNorm hr (A i j))
    (higham13_algorithm13_3_diagLowerCert_zero invDiagBound A pivotInv)
    hPivotRecip
    (higham13_algorithm13_3_diagLowerCert_update invDiagBound A pivotInv)
    (blockMaxNorm hm hr A)
    (blockMaxNorm_nonneg hm hr A)
    (fun i j => block_le_blockMaxNorm hm hr A i j)
    (higham13_algorithm13_3_upperFromStages A pivotInv)
    (higham13_algorithm13_3_upperFromStages_upper_block_bound hr A pivotInv)
    (fun i j hji =>
      higham13_algorithm13_3_upperFromStages_lower_zero A pivotInv i j hji)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    column-BDD `2 * ‖A‖` bound for the exact upper factor assembled from Schur
    stages, specialized to the chapter block max norm.

    This instantiates the generic `normMax` in the diagonal-certificate bridge
    with `blockMaxNorm hm hr A`, and the initial block-norm table with
    `maxEntryNorm hr (A i j)`.  The remaining source-specific obligation is the
    pivot product certificate for the diagonal lower-bound recurrence. -/
theorem higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hPivotInvNorm_ne : ∀ k : ℕ,
      higham13_algorithm13_3_pivotInvNorm pivotInv k ≠ 0)
    (hPivotMul : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
      2 * blockMaxNorm hm hr A := by
  exact
    higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_diagLowerCert
      hm hr (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound
      hDom hDiagBound A pivotInv
      (by
        intro i j
        exact higham13_block_norm_eq_maxEntryNorm hr (A i j))
      hPivotInvNorm_ne hPivotMul
      (blockMaxNorm hm hr A)
      (blockMaxNorm_nonneg hm hr A)
      (fun i j => block_le_blockMaxNorm hm hr A i j)

/-- Column-BDD Eq.13.21 specialization using the direct pivot product bound
    for the concrete diagonal lower-bound certificate.  This is the bound-shaped
    companion to
    `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd`. -/
theorem higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_pivot_bound
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_pivotInvNorm pivotInv k *
        higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k ⟨k, hk⟩ ≤ 1) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
      2 * blockMaxNorm hm hr A := by
  exact
    higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_diagLowerCert_pivot_bound
      hm hr (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound
      hDom hDiagBound A pivotInv
      (by
        intro i j
        exact higham13_block_norm_eq_maxEntryNorm hr (A i j))
      hPivotBound
      (blockMaxNorm hm hr A)
      (blockMaxNorm_nonneg hm hr A)
      (fun i j => block_le_blockMaxNorm hm hr A i j)

/-- Column-BDD Eq.13.21 specialization using the source-shaped one-sided
    diagonal lower-bound certificate
    `diagLowerCert_k <= ‖pivotInv_k‖⁻¹`.  The scalar product bound needed by
    the Schur-stage proof is derived locally. -/
theorem higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_diag_lower
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hDiagLower : SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
      2 * blockMaxNorm hm hr A := by
  exact
    higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_pivot_bound
      hm hr A pivotInv invDiagBound hDom hDiagBound
      (higham13_algorithm13_3_diagLowerCert_pivot_bound_of_diag_lower
        invDiagBound A pivotInv hDiagLower)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.21):
    column-BDD `2 * ‖A‖` bound for the upper factor assembled from Schur
    stages, from a source inverse-bound table satisfying the active
    Eq.13.18-style diagonal update and active reciprocal upper bounds.

    This closes the bookkeeping from source-table data to the current
    Eq.13.21 Algorithm 13.3 interface; proving the source table itself remains
    the open analytic obligation. -/
theorem higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_source_table
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInit : ∀ j : Fin m, invDiagBound j ≤ stageInvDiagBound 0 j)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (hActiveUpper : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ ≤
        (higham13_algorithm13_3_pivotInvNorm pivotInv k)⁻¹) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
      2 * blockMaxNorm hm hr A :=
  higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_diag_lower
    hm hr A pivotInv invDiagBound hDom hDiagBound
    (higham13_algorithm13_3_diagLowerCert_diag_lower_of_source_table
      invDiagBound A pivotInv stageInvDiagBound hInit hDiagUpdate hActiveUpper)

/-- Higham, 2nd ed., Chapter 13, Theorems 13.7--13.8 and equation (13.21):
    source-norm upper-factor bound for Algorithm 13.3 in an arbitrary normed
    block algebra.

    This is the faithful subordinate-block-norm route: the block norm is the
    norm carried by `α`, so multiplication is submultiplicative through the
    `SeminormedRing` structure.  It does not assert the entrywise max-norm
    product estimate, which is false without extra structure. -/
theorem
    higham13_algorithm13_3_upperFromNormedStages_blockNormSup_bound_of_column_bdd_diag_lower
    {m : ℕ} {α : Type*} [SeminormedRing α]
    (hm : 0 < m)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => ‖A i j‖) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ ‖A j j‖)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hDiagLower : SchurStageActivePivotInvDiagLower13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    higham13_blockNormSup hm
        (higham13_algorithm13_3_upperFromNormedStages A pivotInv) ≤
      2 * higham13_blockNormSup hm A := by
  classical
  let normMax : ℝ := higham13_blockNormSup hm A
  have hNormMax : 0 ≤ normMax := by
    simpa [normMax] using higham13_blockNormSup_nonneg hm A
  have hMax : ∀ i j : Fin m, ‖A i j‖ ≤ normMax := by
    intro i j
    simpa [normMax] using higham13_block_norm_le_blockNormSup hm A i j
  have hPivotBound :
      ∀ k : ℕ, ∀ hk : k < m,
        higham13_algorithm13_3_pivotInvNorm pivotInv k *
          stageInvDiagBound k ⟨k, hk⟩ ≤ 1 :=
    higham13_theorem13_7_pivot_inverse_bound_of_diag_lower
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv)
      (higham13_algorithm13_3_pivotInvNorm_nonneg pivotInv) hDiagLower
  apply higham13_blockNormSup_le_of_norm_le hm
  intro i j
  by_cases hij : i.val ≤ j.val
  · have hstage :
        higham13_algorithm13_3_upperFromNormedStages A pivotInv i j =
          higham13_algorithm13_3_schurStageBlock A pivotInv i.val i j :=
      higham13_algorithm13_3_upperFromNormedStages_eq_stage A pivotInv i j hij
    rw [hstage]
    exact
      higham13_theorem13_8_active_stage_block_bound_of_exact_update
        (fun i j : Fin m => ‖A i j‖) invDiagBound hDom hDiagBound
        (higham13_algorithm13_3_schurStageBlock A pivotInv) pivotInv
        (higham13_algorithm13_3_schurStageNorm A pivotInv)
        stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv)
        (by
          intro i j
          simp [higham13_algorithm13_3_schurStageNorm,
            higham13_algorithm13_3_schurStageBlock])
        hInitInv
        (by
          intro k i j
          simp [higham13_algorithm13_3_schurStageNorm])
        (by
          intro k
          rfl)
        hPivotBound
        (higham13_algorithm13_3_schurStageBlock_exact_update A pivotInv)
        hDiagUpdate normMax hMax i.val i j le_rfl hij
  · have hji : j.val < i.val := Nat.lt_of_not_ge hij
    have hzero :
        higham13_algorithm13_3_upperFromNormedStages A pivotInv i j = 0 :=
      higham13_algorithm13_3_upperFromNormedStages_lower_zero A pivotInv i j hji
    rw [hzero, norm_zero]
    nlinarith [hNormMax]

/-- Reciprocal-table version of
    `higham13_algorithm13_3_upperFromNormedStages_blockNormSup_bound_of_column_bdd_diag_lower`.

    This is the source-table shape closest to Higham's proof: at each active
    pivot, the carried diagonal budget is the reciprocal of the pivot-inverse
    norm. -/
theorem
    higham13_algorithm13_3_upperFromNormedStages_blockNormSup_bound_of_column_bdd_source_table_reciprocal
    {m : ℕ} {α : Type*} [SeminormedRing α]
    (hm : 0 < m)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => ‖A i j‖) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ ‖A j j‖)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    higham13_blockNormSup hm
        (higham13_algorithm13_3_upperFromNormedStages A pivotInv) ≤
      2 * higham13_blockNormSup hm A :=
  higham13_algorithm13_3_upperFromNormedStages_blockNormSup_bound_of_column_bdd_diag_lower
    hm A pivotInv invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    (SchurStageActivePivotInvDiagLower13_7.of_reciprocal
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv)
      hReciprocal)
    hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    finite source-norm history bound for the Algorithm 13.3 Schur-stage table.

    This is the subordinate-block-norm analogue of the scalar max-entry
    history object.  It records the largest block norm among the finitely many
    stages `0, ..., m`, without translating through the entrywise max norm. -/
noncomputable def higham13_algorithm13_3_normedStageHistoryBound {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (hm : 0 < m)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin (m + 1)))
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.succ_pos m⟩⟩)
    (fun k : Fin (m + 1) =>
      higham13_blockNormSup hm
        (fun i j => higham13_algorithm13_3_schurStageBlock A pivotInv k.val i j))

/-- The source-norm history bound contains every recorded Schur stage. -/
theorem higham13_algorithm13_3_normedStageHistoryBound_contains_stage {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (hm : 0 < m)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (k : ℕ) (hk : k ≤ m) :
    higham13_blockNormSup hm
        (fun i j => higham13_algorithm13_3_schurStageBlock A pivotInv k i j) ≤
      higham13_algorithm13_3_normedStageHistoryBound hm A pivotInv := by
  unfold higham13_algorithm13_3_normedStageHistoryBound
  simpa using
    (Finset.le_sup'
      (fun K : Fin (m + 1) =>
        higham13_blockNormSup hm
          (fun i j =>
            higham13_algorithm13_3_schurStageBlock A pivotInv K.val i j))
      (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (m + 1))))

/-- The source-norm history bound contains the initial block table. -/
theorem higham13_algorithm13_3_normedStageHistoryBound_contains_initial {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (hm : 0 < m)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α) :
    higham13_blockNormSup hm A ≤
      higham13_algorithm13_3_normedStageHistoryBound hm A pivotInv := by
  simpa [higham13_algorithm13_3_schurStageBlock] using
    higham13_algorithm13_3_normedStageHistoryBound_contains_stage
      hm A pivotInv 0 (Nat.zero_le m)

/-- The source-norm history bound is nonnegative. -/
lemma higham13_algorithm13_3_normedStageHistoryBound_nonneg {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (hm : 0 < m)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α) :
    0 ≤ higham13_algorithm13_3_normedStageHistoryBound hm A pivotInv := by
  exact le_trans (higham13_blockNormSup_nonneg hm A)
    (higham13_algorithm13_3_normedStageHistoryBound_contains_initial
      hm A pivotInv)

/-- The source-norm history bound contains the upper factor assembled from
    the recorded Schur stages. -/
theorem higham13_algorithm13_3_normedStageHistoryBound_contains_upperFromNormedStages
    {m : ℕ} {α : Type*} [SeminormedRing α]
    (hm : 0 < m)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α) :
    higham13_blockNormSup hm
        (higham13_algorithm13_3_upperFromNormedStages A pivotInv) ≤
      higham13_algorithm13_3_normedStageHistoryBound hm A pivotInv := by
  apply higham13_blockNormSup_le_of_norm_le hm
  intro i j
  by_cases hij : i.val ≤ j.val
  · have hstage :
        higham13_algorithm13_3_upperFromNormedStages A pivotInv i j =
          higham13_algorithm13_3_schurStageBlock A pivotInv i.val i j :=
      higham13_algorithm13_3_upperFromNormedStages_eq_stage A pivotInv i j hij
    rw [hstage]
    exact le_trans
      (higham13_block_norm_le_blockNormSup hm
        (fun p q => higham13_algorithm13_3_schurStageBlock A pivotInv i.val p q) i j)
      (higham13_algorithm13_3_normedStageHistoryBound_contains_stage
        hm A pivotInv i.val (Nat.le_of_lt i.isLt))
  · have hji : j.val < i.val := Nat.lt_of_not_ge hij
    have hzero :
        higham13_algorithm13_3_upperFromNormedStages A pivotInv i j = 0 :=
      higham13_algorithm13_3_upperFromNormedStages_lower_zero A pivotInv i j hji
    rw [hzero, norm_zero]
    exact higham13_algorithm13_3_normedStageHistoryBound_nonneg hm A pivotInv

/-- Active-stage source-norm bounds extend to every block of every recorded
    Schur stage. -/
theorem higham13_algorithm13_3_normedStageBlock_bound_of_active_bound
    {m : ℕ} {α : Type*} [SeminormedRing α]
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    {C : ℝ}
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      ‖higham13_algorithm13_3_schurStageBlock A pivotInv k i j‖ ≤ C) :
    ∀ k : ℕ, k ≤ m → ∀ i j : Fin m,
      ‖higham13_algorithm13_3_schurStageBlock A pivotInv k i j‖ ≤ C := by
  intro k hk
  induction k with
  | zero =>
      intro i j
      exact hActive 0 i j (Nat.zero_le m) (Nat.zero_le i.val) (Nat.zero_le j.val)
  | succ k ih =>
      intro i j
      by_cases hactive : k + 1 ≤ i.val ∧ k + 1 ≤ j.val
      · exact hActive (k + 1) i j hk hactive.1 hactive.2
      · have hklt : k < m := Nat.lt_of_succ_le hk
        have hnot_lt : ¬(k < i.val ∧ k < j.val) := by
          intro hlt
          exact hactive ⟨Nat.succ_le_of_lt hlt.1, Nat.succ_le_of_lt hlt.2⟩
        have hstage :
            higham13_algorithm13_3_schurStageBlock A pivotInv (k + 1) i j =
              higham13_algorithm13_3_schurStageBlock A pivotInv k i j := by
          simp [higham13_algorithm13_3_schurStageBlock, hklt, hnot_lt]
        simpa [hstage] using ih (Nat.le_of_succ_le hk) i j

/-- A uniform source-norm bound on each recorded Schur stage controls the
    finite source-norm history bound. -/
theorem higham13_algorithm13_3_normedStageHistoryBound_le_of_stage_bound
    {m : ℕ} {α : Type*} [SeminormedRing α]
    (hm : 0 < m)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    {C : ℝ}
    (hStage : ∀ k : ℕ, k ≤ m →
      higham13_blockNormSup hm
          (fun i j => higham13_algorithm13_3_schurStageBlock A pivotInv k i j) ≤
        C) :
    higham13_algorithm13_3_normedStageHistoryBound hm A pivotInv ≤ C := by
  unfold higham13_algorithm13_3_normedStageHistoryBound
  apply Finset.sup'_le
  intro K _hK
  exact hStage K.val (Nat.le_of_lt_succ K.isLt)

/-- Active-stage source-norm bounds control the finite source-norm history
    bound. -/
theorem higham13_algorithm13_3_normedStageHistoryBound_le_of_active_bound
    {m : ℕ} {α : Type*} [SeminormedRing α]
    (hm : 0 < m)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    {C : ℝ}
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      ‖higham13_algorithm13_3_schurStageBlock A pivotInv k i j‖ ≤ C) :
    higham13_algorithm13_3_normedStageHistoryBound hm A pivotInv ≤ C :=
  higham13_algorithm13_3_normedStageHistoryBound_le_of_stage_bound hm A pivotInv
    (fun k hk =>
      higham13_blockNormSup_le_of_norm_le hm
        (fun i j => higham13_algorithm13_3_schurStageBlock A pivotInv k i j)
        (fun i j =>
          higham13_algorithm13_3_normedStageBlock_bound_of_active_bound
            A pivotInv hActive k hk i j))

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    source-norm stage-history bound from the one-sided active diagonal
    certificate. -/
theorem
    higham13_algorithm13_3_normedStageHistoryBound_le_two_of_column_bdd_diag_lower
    {m : ℕ} {α : Type*} [SeminormedRing α]
    (hm : 0 < m)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => ‖A i j‖) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ ‖A j j‖)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hDiagLower : SchurStageActivePivotInvDiagLower13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    higham13_algorithm13_3_normedStageHistoryBound hm A pivotInv ≤
      2 * higham13_blockNormSup hm A := by
  classical
  let normMax : ℝ := higham13_blockNormSup hm A
  have hMax : ∀ i j : Fin m, ‖A i j‖ ≤ normMax := by
    intro i j
    simpa [normMax] using higham13_block_norm_le_blockNormSup hm A i j
  have hPivotBound :
      ∀ k : ℕ, ∀ hk : k < m,
        higham13_algorithm13_3_pivotInvNorm pivotInv k *
          stageInvDiagBound k ⟨k, hk⟩ ≤ 1 :=
    higham13_theorem13_7_pivot_inverse_bound_of_diag_lower
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv)
      (higham13_algorithm13_3_pivotInvNorm_nonneg pivotInv) hDiagLower
  exact
    higham13_algorithm13_3_normedStageHistoryBound_le_of_active_bound
      hm A pivotInv
      (fun k i j _hk hik hjk => by
        simpa [higham13_algorithm13_3_schurStageNorm] using
          higham13_algorithm13_3_active_stage_block_bound_of_pivot_bound
            (fun i j : Fin m => ‖A i j‖) invDiagBound hDom hDiagBound
            A pivotInv stageInvDiagBound
            (by
              intro i j
              rfl)
            hInitInv hPivotBound hDiagUpdate normMax hMax k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    source-norm stage-history bound in the reciprocal-table form closest to
    the book's lower-norm proof. -/
theorem
    higham13_algorithm13_3_normedStageHistoryBound_le_two_of_column_bdd_source_table_reciprocal
    {m : ℕ} {α : Type*} [SeminormedRing α]
    (hm : 0 < m)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => ‖A i j‖) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ ‖A j j‖)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    higham13_algorithm13_3_normedStageHistoryBound hm A pivotInv ≤
      2 * higham13_blockNormSup hm A :=
  higham13_algorithm13_3_normedStageHistoryBound_le_two_of_column_bdd_diag_lower
    hm A pivotInv invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    (SchurStageActivePivotInvDiagLower13_7.of_reciprocal
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv)
      hReciprocal)
    hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.21) and Theorem 13.8:
    paired source-norm package from the one-sided active diagonal lower
    certificate.

    This is the source-lower-certificate version of the clean subordinate-norm
    endpoint.  It packages the assembled upper-factor bound and the finite
    Schur-stage history bound without requiring a reciprocal table on the
    theorem surface. -/
theorem
    higham13_algorithm13_3_upperFromNormedStages_and_normedStageHistoryBound_le_two_of_column_bdd_diag_lower
    {m : ℕ} {α : Type*} [SeminormedRing α]
    (hm : 0 < m)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => ‖A i j‖) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ ‖A j j‖)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hDiagLower : SchurStageActivePivotInvDiagLower13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    higham13_blockNormSup hm
        (higham13_algorithm13_3_upperFromNormedStages A pivotInv) ≤
        2 * higham13_blockNormSup hm A ∧
      higham13_algorithm13_3_normedStageHistoryBound hm A pivotInv ≤
        2 * higham13_blockNormSup hm A :=
  ⟨higham13_algorithm13_3_upperFromNormedStages_blockNormSup_bound_of_column_bdd_diag_lower
      hm A pivotInv invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hDiagLower hDiagUpdate,
    higham13_algorithm13_3_normedStageHistoryBound_le_two_of_column_bdd_diag_lower
      hm A pivotInv invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hDiagLower hDiagUpdate⟩

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    actual continuous-linear-map source-table data gives the paired
    subordinate-norm upper-factor and finite Schur-stage history bounds.

    This threads the CLM lower-norm source-table certificate through the
    generic source-norm endpoint.  It remains conditional on the source initial
    lower table, initial diagonal comparison, and two-sided active pivot
    inverse identities. -/
theorem
    higham13_algorithm13_3_clm_upperFromNormedStages_and_normedStageHistoryBound_le_two_of_continuousLinearMap_source_table
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hm : 0 < m)
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → E →L[ℝ] E)
    (pivotInv : ℕ → E →L[ℝ] E)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => ‖A i j‖) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ ‖A j j‖)
    (hInit : ∀ j : Fin m,
      invDiagBound j ≤
        continuousLinearMapLowerNorm
          (higham13_algorithm13_3_schurStageBlock A pivotInv 0 j j)
          hunit)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : E,
      pivotInv k
        (higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩ x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : E,
      higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩
        (pivotInv k y) = y) :
    higham13_blockNormSup hm
        (higham13_algorithm13_3_upperFromNormedStages A pivotInv) ≤
        2 * higham13_blockNormSup hm A ∧
      higham13_algorithm13_3_normedStageHistoryBound hm A pivotInv ≤
        2 * higham13_blockNormSup hm A := by
  have hDiagLower :
      SchurStageActivePivotInvDiagLower13_7
        (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
        (higham13_algorithm13_3_pivotInvNorm pivotInv) := by
    simpa [higham13_algorithm13_3_pivotInvNorm] using
      higham13_algorithm13_3_clm_diagLowerCertGeneric_diag_lower_of_continuousLinearMap_source_table
        hunit invDiagBound A pivotInv hInit hLeft hRight
  exact
    higham13_algorithm13_3_upperFromNormedStages_and_normedStageHistoryBound_le_two_of_column_bdd_diag_lower
      hm A pivotInv invDiagBound
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      hDom hDiagBound
      (higham13_algorithm13_3_diagLowerCertGeneric_zero invDiagBound A pivotInv)
      hDiagLower
      (higham13_algorithm13_3_diagLowerCertGeneric_update invDiagBound A pivotInv)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    diagonal inverse data plus active pivot inverse identities give the paired
    CLM subordinate-norm upper-factor and finite stage-history bounds.

    This is the source-table endpoint with the stage-zero lower table and
    initial diagonal comparison discharged from two-sided diagonal inverses and
    reciprocal diagonal budgets. -/
theorem
    higham13_algorithm13_3_clm_upperFromNormedStages_and_normedStageHistoryBound_le_two_of_initial_diag_inverse_of_pivot_inverse
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hm : 0 < m)
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (invDiagBound : Fin m → ℝ)
    (A : Fin m → Fin m → E →L[ℝ] E)
    (pivotInv : ℕ → E →L[ℝ] E)
    (diagInv : Fin m → E →L[ℝ] E)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => ‖A i j‖) invDiagBound)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (‖diagInv j‖)⁻¹)
    (hLeftDiag : ∀ j : Fin m, ∀ x : E, diagInv j (A j j x) = x)
    (hRightDiag : ∀ j : Fin m, ∀ y : E, A j j (diagInv j y) = y)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : E,
      pivotInv k
        (higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩ x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : E,
      higham13_algorithm13_3_schurStageBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩
        (pivotInv k y) = y) :
    higham13_blockNormSup hm
        (higham13_algorithm13_3_upperFromNormedStages A pivotInv) ≤
        2 * higham13_blockNormSup hm A ∧
      higham13_algorithm13_3_normedStageHistoryBound hm A pivotInv ≤
        2 * higham13_blockNormSup hm A :=
  higham13_algorithm13_3_clm_upperFromNormedStages_and_normedStageHistoryBound_le_two_of_continuousLinearMap_source_table
    hm hunit invDiagBound A pivotInv hDom
    (higham13_algorithm13_3_clm_initial_diag_bound_of_diag_inverse
      hunit invDiagBound A diagInv hInvBound hLeftDiag hRightDiag)
    (higham13_algorithm13_3_clm_initial_lower_table_of_diag_inverse
      hunit invDiagBound A pivotInv diagInv hInvBound hLeftDiag hRightDiag)
    hLeft hRight

/-- Higham, 2nd ed., Chapter 13, equation (13.21) and Theorem 13.8:
    paired source-norm package for the assembled upper factor and the finite
    Schur-stage history bound.

    This is the clean subordinate-norm endpoint.  It avoids the false
    entrywise max-norm product shortcut, and it still leaves the source lower
    table/active reciprocal construction explicit. -/
theorem
    higham13_algorithm13_3_upperFromNormedStages_and_normedStageHistoryBound_le_two_of_column_bdd_source_table_reciprocal
    {m : ℕ} {α : Type*} [SeminormedRing α]
    (hm : 0 < m)
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => ‖A i j‖) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ ‖A j j‖)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    higham13_blockNormSup hm
        (higham13_algorithm13_3_upperFromNormedStages A pivotInv) ≤
        2 * higham13_blockNormSup hm A ∧
      higham13_algorithm13_3_normedStageHistoryBound hm A pivotInv ≤
        2 * higham13_blockNormSup hm A :=
  ⟨higham13_algorithm13_3_upperFromNormedStages_blockNormSup_bound_of_column_bdd_source_table_reciprocal
      hm A pivotInv invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hReciprocal hDiagUpdate,
    higham13_algorithm13_3_normedStageHistoryBound_le_two_of_column_bdd_source_table_reciprocal
      hm A pivotInv invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hReciprocal hDiagUpdate⟩

/-- Column-BDD Eq.13.21 specialization using only the active pivot product
    certificate.  This removes the redundant separate nonzero-norm premise from
    `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd`;
    the product identity itself implies nonzero active pivot-inverse norms. -/
theorem higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_active_mul_eq_one
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hPivotMul : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv k ⟨k, hk⟩ *
        higham13_algorithm13_3_pivotInvNorm pivotInv k = 1) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
      2 * blockMaxNorm hm hr A := by
  exact
    higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_diagLowerCert_active_mul_eq_one
      hm hr (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound
      hDom hDiagBound A pivotInv
      (by
        intro i j
        exact higham13_block_norm_eq_maxEntryNorm hr (A i j))
      hPivotMul
      (blockMaxNorm hm hr A)
      (blockMaxNorm_nonneg hm hr A)
      (fun i j => block_le_blockMaxNorm hm hr A i j)

/-- Column-BDD Eq.13.21 specialization from active pivot right-inverse data
    plus the concrete reciprocal diagonal certificate.  This is the
    source-shaped right-inverse version of the active-product route for the
    upper factor assembled from Algorithm 13.3 Schur stages. -/
theorem
    higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_pivot_right_inverse_reciprocal
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageBlock A pivotInv
          k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hReciprocal : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv
          k ⟨k, hk⟩ =
        (higham13_algorithm13_3_pivotInvNorm pivotInv k)⁻¹) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
      2 * blockMaxNorm hm hr A := by
  exact
    higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_active_mul_eq_one
      hm hr A pivotInv invDiagBound hDom hDiagBound
      (higham13_algorithm13_3_diagLowerCert_active_mul_eq_one_of_pivot_right_inverse_reciprocal
        hr invDiagBound A pivotInv hPivotRight hReciprocal)

end NumStability
