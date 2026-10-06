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
import NumStability.Source.Higham.Chapter13.Problem04.BlockInverseBounds
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStages
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis

/-!
# Source.Higham.Chapter13.Problem04.MatrixStageHistory

This module formalizes the source-facing Chapter 13 statements for
`Problem04.MatrixStageHistory`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Matrix-product stage-history bound for the source-faithful Algorithm 13.3
    Schur-stage table. -/
noncomputable def higham13_algorithm13_3_matrixStageHistoryBound {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin (m + 1)))
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.succ_pos m⟩⟩)
    (fun K : Fin (m + 1) =>
      blockMaxNorm hm hr
        (fun i j => higham13_algorithm13_3_schurStageMatrixBlock A pivotInv K.val i j))

/-- Matrix-`∞` analogue of the finite matrix-product stage-history bound for
    the source-faithful Algorithm 13.3 Schur-stage table. -/
noncomputable def higham13_algorithm13_3_matrixStageHistoryInfBound {m r : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin (m + 1)))
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.succ_pos m⟩⟩)
    (fun K : Fin (m + 1) =>
      blockInfNorm hm
        (fun i j => higham13_algorithm13_3_schurStageMatrixBlock A pivotInv K.val i j))

theorem higham13_algorithm13_3_matrixStageHistoryBound_contains_stage {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (k : ℕ) (hk : k ≤ m) :
    blockMaxNorm hm hr
        (fun i j => higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
      higham13_algorithm13_3_matrixStageHistoryBound hm hr A pivotInv := by
  unfold higham13_algorithm13_3_matrixStageHistoryBound
  simpa using
    (Finset.le_sup'
      (fun K : Fin (m + 1) =>
        blockMaxNorm hm hr
          (fun i j =>
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv K.val i j))
      (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (m + 1))))

theorem higham13_algorithm13_3_matrixStageHistoryBound_contains_initial {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    blockMaxNorm hm hr A ≤
      higham13_algorithm13_3_matrixStageHistoryBound hm hr A pivotInv := by
  simpa [higham13_algorithm13_3_schurStageMatrixBlock,
    higham13_algorithm13_3_schurStageBlock] using
    higham13_algorithm13_3_matrixStageHistoryBound_contains_stage
      hm hr A pivotInv 0 (Nat.zero_le m)

lemma higham13_algorithm13_3_matrixStageHistoryBound_nonneg {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    0 ≤ higham13_algorithm13_3_matrixStageHistoryBound hm hr A pivotInv := by
  exact le_trans (blockMaxNorm_nonneg hm hr A)
    (higham13_algorithm13_3_matrixStageHistoryBound_contains_initial
      hm hr A pivotInv)

theorem higham13_algorithm13_3_matrixStageHistoryInfBound_contains_stage {m r : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (k : ℕ) (hk : k ≤ m) :
    blockInfNorm hm
        (fun i j => higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
      higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv := by
  unfold higham13_algorithm13_3_matrixStageHistoryInfBound
  simpa using
    (Finset.le_sup'
      (fun K : Fin (m + 1) =>
        blockInfNorm hm
          (fun i j =>
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv K.val i j))
      (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (m + 1))))

theorem higham13_algorithm13_3_matrixStageHistoryInfBound_contains_initial
    {m r : ℕ} (hm : 0 < m)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    blockInfNorm hm A ≤
      higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv := by
  simpa [higham13_algorithm13_3_schurStageMatrixBlock,
    higham13_algorithm13_3_schurStageBlock] using
    higham13_algorithm13_3_matrixStageHistoryInfBound_contains_stage
      hm A pivotInv 0 (Nat.zero_le m)

lemma higham13_algorithm13_3_matrixStageHistoryInfBound_nonneg {m r : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    0 ≤ higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv := by
  exact le_trans (blockInfNorm_nonneg hm A)
    (higham13_algorithm13_3_matrixStageHistoryInfBound_contains_initial
      hm A pivotInv)

theorem higham13_algorithm13_3_matrixStageHistoryBound_contains_upperFromMatrixStages
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    blockMaxNorm hm hr
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      higham13_algorithm13_3_matrixStageHistoryBound hm hr A pivotInv := by
  apply blockMaxNorm_le_of_entry_abs_le
  intro i j s t
  by_cases hij : i.val ≤ j.val
  · exact le_trans
      (by
        simpa [higham13_algorithm13_3_upperFromMatrixStages, hij] using
          block_entry_abs_le_blockMaxNorm hm hr
            (fun p q =>
              higham13_algorithm13_3_schurStageMatrixBlock A pivotInv i.val p q)
            i j s t)
      (higham13_algorithm13_3_matrixStageHistoryBound_contains_stage
        hm hr A pivotInv i.val (Nat.le_of_lt i.isLt))
  · have hzero :
        higham13_algorithm13_3_upperFromMatrixStages A pivotInv i j = 0 := by
      simp [higham13_algorithm13_3_upperFromMatrixStages, hij]
    calc
      |higham13_algorithm13_3_upperFromMatrixStages A pivotInv i j s t| = 0 := by
        simp [hzero]
      _ ≤ higham13_algorithm13_3_matrixStageHistoryBound hm hr A pivotInv :=
        higham13_algorithm13_3_matrixStageHistoryBound_nonneg hm hr A pivotInv

/-- The matrix-`∞` stage-history bound contains the assembled upper factor. -/
theorem higham13_algorithm13_3_matrixStageHistoryInfBound_contains_upperFromMatrixStages
    {m r : ℕ} (hm : 0 < m)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    blockInfNorm hm
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv := by
  apply blockInfNorm_le_of_block_le
  intro i j
  by_cases hij : i.val ≤ j.val
  · exact le_trans
      (by
        rw [higham13_algorithm13_3_upperFromMatrixStages_eq_of_le A pivotInv hij]
        exact
          block_le_blockInfNorm hm
            (fun p q =>
              higham13_algorithm13_3_schurStageMatrixBlock A pivotInv i.val p q)
            i j)
      (higham13_algorithm13_3_matrixStageHistoryInfBound_contains_stage
        hm A pivotInv i.val (Nat.le_of_lt i.isLt))
  · have hji : j.val < i.val := Nat.lt_of_not_ge hij
    exact le_trans
      (infNorm_le_zero_of_eq_zeroBlock
        (higham13_algorithm13_3_upperFromMatrixStages_lower_zero A pivotInv hji))
      (higham13_algorithm13_3_matrixStageHistoryInfBound_nonneg hm A pivotInv)

/-- Constant matrix carrying the source-faithful matrix-product stage-history
    bound. -/
noncomputable def higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
    {N m r : ℕ} (_hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    Fin N → Fin N → ℝ :=
  fun _ _ => higham13_algorithm13_3_matrixStageHistoryBound hm hr A pivotInv

theorem higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_maxEntryNorm
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    maxEntryNorm hN
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr A pivotInv) =
      higham13_algorithm13_3_matrixStageHistoryBound hm hr A pivotInv := by
  let C : ℝ := higham13_algorithm13_3_matrixStageHistoryBound hm hr A pivotInv
  have hC : 0 ≤ C := by
    simpa [C] using higham13_algorithm13_3_matrixStageHistoryBound_nonneg hm hr A pivotInv
  apply le_antisymm
  · have hrect :
        maxEntryNormRect hN hN
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr A pivotInv) ≤
          C := by
      apply maxEntryNormRect_le_of_entry_abs_le
      intro i j
      simp [higham13_algorithm13_3_matrixStageHistoryGrowthMatrix, C, abs_of_nonneg hC]
    simpa [maxEntryNormRect_eq_maxEntryNorm hN, C] using hrect
  · have hentry :=
      entry_le_maxEntryNorm hN
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr A pivotInv)
        (⟨0, hN⟩ : Fin N) (⟨0, hN⟩ : Fin N)
    simpa [higham13_algorithm13_3_matrixStageHistoryGrowthMatrix, C, abs_of_nonneg hC]
      using hentry

theorem higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    blockMaxNorm hm hr A ≤
      maxEntryNorm hN
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr A pivotInv) := by
  rw [higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_maxEntryNorm]
  exact higham13_algorithm13_3_matrixStageHistoryBound_contains_initial hm hr A pivotInv

theorem higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_stage
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (k : ℕ) (hk : k ≤ m) :
    blockMaxNorm hm hr
        (fun i j => higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
      maxEntryNorm hN
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr A pivotInv) := by
  rw [higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_maxEntryNorm]
  exact
    higham13_algorithm13_3_matrixStageHistoryBound_contains_stage
      hm hr A pivotInv k hk

theorem higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_upperFromMatrixStages
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    blockMaxNorm hm hr
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      maxEntryNorm hN
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr A pivotInv) := by
  rw [higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_maxEntryNorm]
  exact
    higham13_algorithm13_3_matrixStageHistoryBound_contains_upperFromMatrixStages
      hm hr A pivotInv

/-- After the first block elimination, the finite matrix-stage history bound
    for the recursive Schur tail is dominated by the full matrix-stage history
    bound.

    This is the history-comparison side of the recursive Problem 13.4 route:
    the shifted tail stage table is a lower-right subtable of the full stage
    table at one later pivot index. -/
theorem higham13_algorithm13_3_matrixStageHistoryBound_tail_le
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    higham13_algorithm13_3_matrixStageHistoryBound hm hr
        (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) ≤
      higham13_algorithm13_3_matrixStageHistoryBound
        (Nat.succ_pos m) hr A pivotInv := by
  unfold higham13_algorithm13_3_matrixStageHistoryBound
  apply Finset.sup'_le
  intro K _hK
  have hstage :
      blockMaxNorm hm hr
          (fun i j =>
            higham13_algorithm13_3_schurStageMatrixBlock
              (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1))
              K.val i j) ≤
        blockMaxNorm (Nat.succ_pos m) hr
          (fun i j =>
            higham13_algorithm13_3_schurStageMatrixBlock
              A pivotInv (K.val + 1) i j) := by
    apply blockMaxNorm_le_of_entry_abs_le
    intro i j s t
    have hshift :=
      higham13_algorithm13_3_schurStageMatrixBlock_tail_shift
        A pivotInv K.val i j
    rw [hshift]
    exact
      block_entry_abs_le_blockMaxNorm (Nat.succ_pos m) hr
        (fun p q =>
          higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv (K.val + 1) p q)
        (Fin.succ i) (Fin.succ j) s t
  exact le_trans hstage
    (Finset.le_sup'
      (fun Kfull : Fin ((m + 1) + 1) =>
        blockMaxNorm (Nat.succ_pos m) hr
          (fun i j =>
            higham13_algorithm13_3_schurStageMatrixBlock
              A pivotInv Kfull.val i j))
      (Finset.mem_univ
        (⟨K.val + 1, Nat.succ_lt_succ K.isLt⟩ :
          Fin ((m + 1) + 1))))

/-- Growth-matrix form of
    `higham13_algorithm13_3_matrixStageHistoryBound_tail_le`.

    Since both history growth matrices are constant nonnegative matrices, their
    max-entry norms are the corresponding finite history bounds. -/
theorem higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_tail_le
    {Ntail Nfull m r : ℕ} (hNtail : 0 < Ntail) (hNfull : 0 < Nfull)
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    maxEntryNorm hNtail
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hNtail hm hr (blockSchur A (pivotInv 0))
          (fun q => pivotInv (q + 1))) ≤
      maxEntryNorm hNfull
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hNfull (Nat.succ_pos m) hr A pivotInv) := by
  rw [higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_maxEntryNorm]
  rw [higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_maxEntryNorm]
  exact higham13_algorithm13_3_matrixStageHistoryBound_tail_le hm hr A pivotInv

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    upper-budget comparison for the recursive Schur tail.

    The tail budget `rho_tail * ||S||_max` is exactly the max-entry norm of the
    shifted tail history object, and the full budget is exactly the max-entry
    norm of the full matrix-stage history object.  The tail-history comparison
    therefore discharges the upper-growth side of transporting a recursive
    Schur-tail budget chain to the full ambient source constants. -/
theorem higham13_eq13_22_tail_upper_budget_le_full_matrix_stage_history_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hTailPos :
      0 < maxEntryNorm (Nat.mul_pos hm hr)
        (blockMatrixFlatFin (blockSchur A (pivotInv 0))))
    (hFullPos :
      0 < maxEntryNorm (Nat.add_pos_left hr (m * r))
        (blockMatrixFirstSplitFlat A)) :
    growthFactorEntry (Nat.mul_pos hm hr)
        (blockMatrixFlatFin (blockSchur A (pivotInv 0)))
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)))
        hTailPos *
        maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin (blockSchur A (pivotInv 0))) ≤
      growthFactorEntry (Nat.add_pos_left hr (m * r))
        (blockMatrixFirstSplitFlat A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.add_pos_left hr (m * r)) (Nat.succ_pos m) hr A pivotInv)
        hFullPos *
        maxEntryNormRect (Nat.add_pos_left hr (m * r))
          (Nat.add_pos_left hr (m * r)) (blockMatrixFirstSplitFlat A) := by
  rw [growthFactorEntry_mul_maxEntryNormRect_eq_maxEntryNorm
    (Nat.mul_pos hm hr)
    (blockMatrixFlatFin (blockSchur A (pivotInv 0)))
    (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      (Nat.mul_pos hm hr) hm hr
      (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)))
    hTailPos]
  rw [growthFactorEntry_mul_maxEntryNormRect_eq_maxEntryNorm
    (Nat.add_pos_left hr (m * r))
    (blockMatrixFirstSplitFlat A)
    (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      (Nat.add_pos_left hr (m * r)) (Nat.succ_pos m) hr A pivotInv)
    hFullPos]
  exact
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_tail_le
      (Nat.mul_pos hm hr) (Nat.add_pos_left hr (m * r)) hm hr A pivotInv

/-- The matrix-stage growth factor is invariant under the first-split versus
    uniform-flat representation of the same block matrix.

    The history growth matrices are constant matrices whose max-entry norm is
    the same finite stage-history bound; the denominators agree by
    `maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin`. -/
theorem growthFactorEntry_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hSplitPos :
      0 < maxEntryNorm (Nat.add_pos_left hr (m * r))
        (blockMatrixFirstSplitFlat A))
    (hFlatPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin A)) :
    growthFactorEntry (Nat.add_pos_left hr (m * r))
        (blockMatrixFirstSplitFlat A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.add_pos_left hr (m * r)) (Nat.succ_pos m) hr A pivotInv)
        hSplitPos =
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr A pivotInv)
        hFlatPos := by
  unfold growthFactorEntry
  rw [higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_maxEntryNorm]
  rw [higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_maxEntryNorm]
  rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin hm hr A]

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    the first-split exact-κ lower budget is bounded by the uniform-flat exact-κ
    lower budget for the same matrix-stage history.

    This removes a representation artifact from the recursive Problem 13.4
    route: a budget proved for the source uniform flattening is large enough
    for the first-split constructor used by the local Schur step. -/
theorem
    higham13_eq13_22_firstSplit_lower_budget_le_flat_matrix_stage_history_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hdetFlat :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0)
    (n : ℕ) :
    let hSplit : 0 < r + m * r := Nat.add_pos_left hr (m * r)
    let hFlat : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hSplitPos : 0 < maxEntryNorm hSplit (blockMatrixFirstSplitFlat A) := by
      rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin hm hr A]
      exact maxEntryNorm_pos_of_det_ne_zero hFlat (blockMatrixFlatFin A) hdetFlat
    let hFlatPos : 0 < maxEntryNorm hFlat (blockMatrixFlatFin A) :=
      maxEntryNorm_pos_of_det_ne_zero hFlat (blockMatrixFlatFin A) hdetFlat
    (n : ℝ) *
        (growthFactorEntry hSplit (blockMatrixFirstSplitFlat A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hSplit (Nat.succ_pos m) hr A pivotInv) hSplitPos) ^ 2 *
        (maxEntryNormRect hSplit hSplit (blockMatrixFirstSplitFlat A) *
          maxEntryNormRect hSplit hSplit
            (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat A))) ≤
      (n : ℝ) *
        (growthFactorEntry hFlat (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hFlat (Nat.succ_pos m) hr A pivotInv) hFlatPos) ^ 2 *
        (maxEntryNormRect hFlat hFlat (blockMatrixFlatFin A) *
          maxEntryNormRect hFlat hFlat
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin A))) := by
  dsimp only
  let hSplit : 0 < r + m * r := Nat.add_pos_left hr (m * r)
  let hFlat : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
  let hFlatPos : 0 < maxEntryNorm hFlat (blockMatrixFlatFin A) :=
    maxEntryNorm_pos_of_det_ne_zero hFlat (blockMatrixFlatFin A) hdetFlat
  let hSplitPos : 0 < maxEntryNorm hSplit (blockMatrixFirstSplitFlat A) := by
    rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin hm hr A]
    exact hFlatPos
  have hRho :
      growthFactorEntry hSplit (blockMatrixFirstSplitFlat A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hSplit (Nat.succ_pos m) hr A pivotInv) hSplitPos =
        growthFactorEntry hFlat (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hFlat (Nat.succ_pos m) hr A pivotInv) hFlatPos :=
    growthFactorEntry_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin
      hm hr A pivotInv hSplitPos hFlatPos
  have hKappa :
      maxEntryNormRect hSplit hSplit (blockMatrixFirstSplitFlat A) *
          maxEntryNormRect hSplit hSplit
            (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat A)) ≤
        maxEntryNormRect hFlat hFlat (blockMatrixFlatFin A) *
          maxEntryNormRect hFlat hFlat
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin A)) := by
    simpa [hSplit, hFlat] using
      maxEntryNormRect_kappa_blockMatrixFirstSplitFlat_le_blockMatrixFlatFin_of_det_ne_zero
        hm hr A
        (det_ne_zero_blockMatrixFirstSplitFlat_of_blockMatrixFlatFin A hdetFlat)
  have hcoef_nonneg :
      0 ≤ (n : ℝ) *
        (growthFactorEntry hFlat (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hFlat (Nat.succ_pos m) hr A pivotInv) hFlatPos) ^ 2 := by
    exact mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)
  calc
    (n : ℝ) *
        (growthFactorEntry hSplit (blockMatrixFirstSplitFlat A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hSplit (Nat.succ_pos m) hr A pivotInv) hSplitPos) ^ 2 *
        (maxEntryNormRect hSplit hSplit (blockMatrixFirstSplitFlat A) *
          maxEntryNormRect hSplit hSplit
            (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat A)))
        =
      (n : ℝ) *
        (growthFactorEntry hFlat (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hFlat (Nat.succ_pos m) hr A pivotInv) hFlatPos) ^ 2 *
        (maxEntryNormRect hSplit hSplit (blockMatrixFirstSplitFlat A) *
          maxEntryNormRect hSplit hSplit
            (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat A))) := by
        rw [hRho]
    _ ≤
      (n : ℝ) *
        (growthFactorEntry hFlat (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hFlat (Nat.succ_pos m) hr A pivotInv) hFlatPos) ^ 2 *
        (maxEntryNormRect hFlat hFlat (blockMatrixFlatFin A) *
          maxEntryNormRect hFlat hFlat
            (nonsingInv ((m + 1) * r) (blockMatrixFlatFin A))) := by
        exact mul_le_mul_of_nonneg_left hKappa hcoef_nonneg

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    the first-split and uniform-flat exact upper budgets coincide for the same
    matrix-stage history. -/
theorem
    higham13_eq13_22_firstSplit_upper_budget_eq_flat_matrix_stage_history_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hFlatPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin A)) :
    let hSplit : 0 < r + m * r := Nat.add_pos_left hr (m * r)
    let hFlat : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let hSplitPos : 0 < maxEntryNorm hSplit (blockMatrixFirstSplitFlat A) := by
      rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin hm hr A]
      exact hFlatPos
    growthFactorEntry hSplit (blockMatrixFirstSplitFlat A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hSplit (Nat.succ_pos m) hr A pivotInv) hSplitPos *
        maxEntryNormRect hSplit hSplit (blockMatrixFirstSplitFlat A) =
      growthFactorEntry hFlat (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hFlat (Nat.succ_pos m) hr A pivotInv) hFlatPos *
        maxEntryNormRect hFlat hFlat (blockMatrixFlatFin A) := by
  dsimp only
  let hSplit : 0 < r + m * r := Nat.add_pos_left hr (m * r)
  let hFlat : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
  let hSplitPos : 0 < maxEntryNorm hSplit (blockMatrixFirstSplitFlat A) := by
    rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin hm hr A]
    exact hFlatPos
  have hRho :
      growthFactorEntry hSplit (blockMatrixFirstSplitFlat A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hSplit (Nat.succ_pos m) hr A pivotInv) hSplitPos =
        growthFactorEntry hFlat (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hFlat (Nat.succ_pos m) hr A pivotInv) hFlatPos :=
    growthFactorEntry_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin
      hm hr A pivotInv hSplitPos hFlatPos
  have hNorm :
      maxEntryNormRect hSplit hSplit (blockMatrixFirstSplitFlat A) =
        maxEntryNormRect hFlat hFlat (blockMatrixFlatFin A) := by
    rw [maxEntryNormRect_eq_maxEntryNorm hSplit]
    rw [maxEntryNormRect_eq_maxEntryNorm hFlat]
    exact maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin hm hr A
  rw [hRho, hNorm]

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    transport a recursive Schur-tail chain to the full ambient budgets once
    the remaining lower/condition scalar comparison is supplied.

    The upper-budget comparison is no longer a hypothesis: it follows from
    `higham13_eq13_22_tail_upper_budget_le_full_matrix_stage_history_exact_kappa`.
    Thus this adapter isolates the genuine remaining recursive Problem 13.4
    obligation to the lower/condition-number budget comparison. -/
theorem
    higham13_eq13_22_tail_chain_to_full_budget_from_lower_comparison_matrix_stage_history_exact_kappa
    {m r : ℕ} (hr : 0 < r)
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hTailPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin (blockSchur A (pivotInv 0))))
    (hFullPos :
      0 < maxEntryNorm (Nat.add_pos_left hr ((m + 1) * r))
        (blockMatrixFirstSplitFlat A))
    (n : ℕ) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNFull : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur A (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur A (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat A
    let Gfull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFull (Nat.succ_pos (m + 1)) hr A pivotInv
    let AinvFull : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) A0
    ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail) ≤
        (n : ℝ) * (growthFactorEntry hNFull A0 Gfull hFullPos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail))
        (growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail)
        m (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFull A0 Gfull hFullPos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull))
        (growthFactorEntry hNFull A0 Gfull hFullPos *
          maxEntryNormRect hNFull hNFull A0)
        m (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) := by
  dsimp only
  intro hLowerBudget hTail
  exact
    Higham13BlockLUBudgetChain.mono hLowerBudget
      (higham13_eq13_22_tail_upper_budget_le_full_matrix_stage_history_exact_kappa
        (Nat.succ_pos m) hr A pivotInv hTailPos hFullPos)
      hTail

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    transport a recursive Schur-tail chain from its local exact-κ budgets to
    the full uniform-flat exact-κ budgets.

    This is the uniform-`blockMatrixFlatFin` companion to
    `higham13_eq13_22_tail_chain_to_full_budget_from_lower_comparison_matrix_stage_history_exact_kappa`.
    The lower comparison is still the genuine source obligation; the
    first-split/flat representation conversion is discharged here from
    determinant nonsingularity. -/
theorem
    higham13_eq13_22_tail_chain_to_flat_budget_from_lower_comparison_matrix_stage_history_exact_kappa_of_det_ne_zero
    {m r : ℕ} (hr : 0 < r)
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hTailPos :
      0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin (blockSchur A (pivotInv 0))))
    (hdetFlat :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (((m + 1) + 1) * r)) (Fin (((m + 1) + 1) * r)) ℝ) ≠ 0)
    (n : ℕ) :
    let hmTail : 0 < m + 1 := Nat.succ_pos m
    let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
    let hNSplit : 0 < r + (m + 1) * r :=
      Nat.add_pos_left hr ((m + 1) * r)
    let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
    let hNFlat : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
    let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      blockMatrixFlatFin (blockSchur A (pivotInv 0))
    let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNTail hmTail hr (blockSchur A (pivotInv 0))
        (fun q => pivotInv (q + 1))
    let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
      nonsingInv ((m + 1) * r) Atail
    let ASplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      blockMatrixFirstSplitFlat A
    let GSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNSplit hmFull hr A pivotInv
    let AinvSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
      nonsingInv (r + (m + 1) * r) ASplit
    let A0 : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      blockMatrixFlatFin A
    let Gflat : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hNFlat hmFull hr A pivotInv
    let AinvFlat : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
      nonsingInv (((m + 1) + 1) * r) A0
    let hFlatPos : 0 < maxEntryNorm hNFlat A0 :=
      maxEntryNorm_pos_of_det_ne_zero hNFlat A0 hdetFlat
    let hSplitPos : 0 < maxEntryNorm hNSplit ASplit := by
      rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin hmTail hr A]
      exact hFlatPos
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
        m (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFlat A0 Gflat hFlatPos) ^ 2 *
          (maxEntryNormRect hNFlat hNFlat A0 *
            maxEntryNormRect hNFlat hNFlat AinvFlat))
        (growthFactorEntry hNFlat A0 Gflat hFlatPos *
          maxEntryNormRect hNFlat hNFlat A0)
        m (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) := by
  dsimp only
  intro hLower hTail
  let hmTail : 0 < m + 1 := Nat.succ_pos m
  let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
  let hNSplit : 0 < r + (m + 1) * r :=
    Nat.add_pos_left hr ((m + 1) * r)
  let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  let hNFlat : 0 < ((m + 1) + 1) * r := Nat.mul_pos hmFull hr
  let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    blockMatrixFlatFin (blockSchur A (pivotInv 0))
  let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      hNTail hmTail hr (blockSchur A (pivotInv 0))
      (fun q => pivotInv (q + 1))
  let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    nonsingInv ((m + 1) * r) Atail
  let ASplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    blockMatrixFirstSplitFlat A
  let GSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      hNSplit hmFull hr A pivotInv
  let AinvSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    nonsingInv (r + (m + 1) * r) ASplit
  let A0 : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    blockMatrixFlatFin A
  let Gflat : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      hNFlat hmFull hr A pivotInv
  let AinvFlat : Fin (((m + 1) + 1) * r) → Fin (((m + 1) + 1) * r) → ℝ :=
    nonsingInv (((m + 1) + 1) * r) A0
  let hFlatPos : 0 < maxEntryNorm hNFlat A0 :=
    maxEntryNorm_pos_of_det_ne_zero hNFlat A0 hdetFlat
  let hSplitPos : 0 < maxEntryNorm hNSplit ASplit := by
    rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin hmTail hr A]
    exact hFlatPos
  have hLowerBridge :
      (n : ℝ) * (growthFactorEntry hNSplit ASplit GSplit hSplitPos) ^ 2 *
          (maxEntryNormRect hNSplit hNSplit ASplit *
            maxEntryNormRect hNSplit hNSplit AinvSplit) ≤
        (n : ℝ) * (growthFactorEntry hNFlat A0 Gflat hFlatPos) ^ 2 *
          (maxEntryNormRect hNFlat hNFlat A0 *
            maxEntryNormRect hNFlat hNFlat AinvFlat) := by
    simpa [hmTail, hNSplit, hmFull, hNFlat, ASplit, GSplit, AinvSplit,
      A0, Gflat, AinvFlat, hSplitPos, hFlatPos] using
      higham13_eq13_22_firstSplit_lower_budget_le_flat_matrix_stage_history_exact_kappa
        hmTail hr A pivotInv hdetFlat n
  have hLowerFlat :
      (n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail) ≤
        (n : ℝ) * (growthFactorEntry hNFlat A0 Gflat hFlatPos) ^ 2 *
          (maxEntryNormRect hNFlat hNFlat A0 *
            maxEntryNormRect hNFlat hNFlat AinvFlat) :=
    le_trans hLower hLowerBridge
  have hUpperSplit :
      growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail ≤
        growthFactorEntry hNSplit ASplit GSplit hSplitPos *
          maxEntryNormRect hNSplit hNSplit ASplit := by
    simpa [hmTail, hNTail, hNSplit, hmFull, Atail, Gtail, ASplit, GSplit,
      hSplitPos] using
      higham13_eq13_22_tail_upper_budget_le_full_matrix_stage_history_exact_kappa
        hmTail hr A pivotInv hTailPos hSplitPos
  have hUpperEq :
      growthFactorEntry hNSplit ASplit GSplit hSplitPos *
          maxEntryNormRect hNSplit hNSplit ASplit =
        growthFactorEntry hNFlat A0 Gflat hFlatPos *
          maxEntryNormRect hNFlat hNFlat A0 := by
    simpa [hmTail, hNSplit, hmFull, hNFlat, ASplit, GSplit, A0, Gflat,
      hSplitPos, hFlatPos] using
      higham13_eq13_22_firstSplit_upper_budget_eq_flat_matrix_stage_history_exact_kappa
        hmTail hr A pivotInv hFlatPos
  have hUpperFlat :
      growthFactorEntry hNTail Atail Gtail hTailPos *
          maxEntryNormRect hNTail hNTail Atail ≤
        growthFactorEntry hNFlat A0 Gflat hFlatPos *
          maxEntryNormRect hNFlat hNFlat A0 := by
    simpa [hUpperEq] using hUpperSplit
  exact
    Higham13BlockLUBudgetChain.mono hLowerFlat hUpperFlat hTail

end NumStability
