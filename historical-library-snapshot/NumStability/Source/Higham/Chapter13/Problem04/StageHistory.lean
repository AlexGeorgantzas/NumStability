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
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Equation21
import NumStability.Source.Higham.Chapter13.Section01.NormConventions
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis

/-!
# Source.Higham.Chapter13.Problem04.StageHistory

This module formalizes the source-facing Chapter 13 statements for
`Problem04.StageHistory`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


-- ============================================================
-- §13.3.1  Problem 13.4 certificate bridges
-- ============================================================

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    finite max-entry history bound for the concrete Schur-stage block table.

    This is a proof object for the recursive growth route: it records the
    largest block max-entry norm among the finitely many concrete stages
    `0, ..., m`.  It is not itself the final recursive LU theorem. -/
noncomputable def higham13_algorithm13_3_stageHistoryBound {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ)) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin (m + 1)))
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.succ_pos m⟩⟩)
    (fun k : Fin (m + 1) =>
      blockMaxNorm hm hr
        (fun i j => higham13_algorithm13_3_schurStageBlock A pivotInv k.val i j))

/-- The finite Algorithm 13.3 stage-history bound contains each recorded stage. -/
theorem higham13_algorithm13_3_stageHistoryBound_contains_stage {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (k : ℕ) (hk : k ≤ m) :
    blockMaxNorm hm hr
        (fun i j => higham13_algorithm13_3_schurStageBlock A pivotInv k i j) ≤
      higham13_algorithm13_3_stageHistoryBound hm hr A pivotInv := by
  unfold higham13_algorithm13_3_stageHistoryBound
  simpa using
    (Finset.le_sup'
      (fun K : Fin (m + 1) =>
        blockMaxNorm hm hr
          (fun i j =>
            higham13_algorithm13_3_schurStageBlock A pivotInv K.val i j))
      (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (m + 1))))

/-- The finite Algorithm 13.3 stage-history bound contains the input block
    matrix, which is stage zero. -/
theorem higham13_algorithm13_3_stageHistoryBound_contains_initial {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ)) :
    blockMaxNorm hm hr A ≤
      higham13_algorithm13_3_stageHistoryBound hm hr A pivotInv := by
  simpa [higham13_algorithm13_3_schurStageBlock] using
    higham13_algorithm13_3_stageHistoryBound_contains_stage
      hm hr A pivotInv 0 (Nat.zero_le m)

/-- The finite Algorithm 13.3 stage-history bound is nonnegative. -/
lemma higham13_algorithm13_3_stageHistoryBound_nonneg {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ)) :
    0 ≤ higham13_algorithm13_3_stageHistoryBound hm hr A pivotInv := by
  exact le_trans (blockMaxNorm_nonneg hm hr A)
    (higham13_algorithm13_3_stageHistoryBound_contains_initial
      hm hr A pivotInv)

/-- The finite Algorithm 13.3 stage-history bound contains the upper factor
    assembled from the recorded stages. -/
theorem higham13_algorithm13_3_stageHistoryBound_contains_upperFromStages
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ)) :
    blockMaxNorm hm hr
        (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
      higham13_algorithm13_3_stageHistoryBound hm hr A pivotInv := by
  apply blockMaxNorm_le_of_entry_abs_le
  intro i j s t
  by_cases hij : i.val ≤ j.val
  · have hentry :
        |higham13_algorithm13_3_schurStageBlock A pivotInv i.val i j s t| ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageBlock A pivotInv i.val i j) :=
      entry_le_maxEntryNorm hr
        (higham13_algorithm13_3_schurStageBlock A pivotInv i.val i j) s t
    have hblock :
        maxEntryNorm hr
            (higham13_algorithm13_3_schurStageBlock A pivotInv i.val i j) ≤
          blockMaxNorm hm hr
            (fun p q =>
              higham13_algorithm13_3_schurStageBlock A pivotInv i.val p q) :=
      block_le_blockMaxNorm hm hr
        (fun p q =>
          higham13_algorithm13_3_schurStageBlock A pivotInv i.val p q) i j
    have hstage :
        blockMaxNorm hm hr
            (fun p q =>
              higham13_algorithm13_3_schurStageBlock A pivotInv i.val p q) ≤
          higham13_algorithm13_3_stageHistoryBound hm hr A pivotInv :=
      higham13_algorithm13_3_stageHistoryBound_contains_stage
        hm hr A pivotInv i.val (Nat.le_of_lt i.isLt)
    calc
      |higham13_algorithm13_3_upperFromStages A pivotInv i j s t|
          = |higham13_algorithm13_3_schurStageBlock A pivotInv i.val i j s t| := by
            simp [higham13_algorithm13_3_upperFromStages, hij]
      _ ≤ maxEntryNorm hr
            (higham13_algorithm13_3_schurStageBlock A pivotInv i.val i j) :=
            hentry
      _ ≤ blockMaxNorm hm hr
            (fun p q =>
              higham13_algorithm13_3_schurStageBlock A pivotInv i.val p q) :=
            hblock
      _ ≤ higham13_algorithm13_3_stageHistoryBound hm hr A pivotInv :=
            hstage
  · have hji : j.val < i.val := Nat.lt_of_not_ge hij
    have hzero :
        higham13_algorithm13_3_upperFromStages A pivotInv i j = zeroBlock r :=
      higham13_algorithm13_3_upperFromStages_lower_zero A pivotInv i j hji
    calc
      |higham13_algorithm13_3_upperFromStages A pivotInv i j s t| = 0 := by
        simp [hzero, zeroBlock]
      _ ≤ higham13_algorithm13_3_stageHistoryBound hm hr A pivotInv :=
        higham13_algorithm13_3_stageHistoryBound_nonneg hm hr A pivotInv

/-- Constant matrix carrying the finite Algorithm 13.3 stage-history bound.

    This gives the max-entry growth-factor API an honest matrix-valued object
    whose norm is exactly the finite stage-history bound. -/
noncomputable def higham13_algorithm13_3_stageHistoryGrowthMatrix
    {N m r : ℕ} (_hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ)) :
    Fin N → Fin N → ℝ :=
  fun _ _ => higham13_algorithm13_3_stageHistoryBound hm hr A pivotInv

/-- The stage-history growth matrix has max-entry norm equal to the finite
    Algorithm 13.3 stage-history bound. -/
theorem higham13_algorithm13_3_stageHistoryGrowthMatrix_maxEntryNorm
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ)) :
    maxEntryNorm hN
        (higham13_algorithm13_3_stageHistoryGrowthMatrix hN hm hr A pivotInv) =
      higham13_algorithm13_3_stageHistoryBound hm hr A pivotInv := by
  let C : ℝ := higham13_algorithm13_3_stageHistoryBound hm hr A pivotInv
  have hC : 0 ≤ C := by
    simpa [C] using higham13_algorithm13_3_stageHistoryBound_nonneg hm hr A pivotInv
  apply le_antisymm
  · have hrect :
        maxEntryNormRect hN hN
            (higham13_algorithm13_3_stageHistoryGrowthMatrix hN hm hr A pivotInv) ≤
          C := by
      apply maxEntryNormRect_le_of_entry_abs_le
      intro i j
      simp [higham13_algorithm13_3_stageHistoryGrowthMatrix, C, abs_of_nonneg hC]
    simpa [maxEntryNormRect_eq_maxEntryNorm hN, C] using hrect
  · have hentry :=
      entry_le_maxEntryNorm hN
        (higham13_algorithm13_3_stageHistoryGrowthMatrix hN hm hr A pivotInv)
        (⟨0, hN⟩ : Fin N) (⟨0, hN⟩ : Fin N)
    simpa [higham13_algorithm13_3_stageHistoryGrowthMatrix, C, abs_of_nonneg hC]
      using hentry

/-- The stage-history growth matrix dominates the input block matrix in the
    chapter block max norm. -/
theorem higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_initial
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ)) :
    blockMaxNorm hm hr A ≤
      maxEntryNorm hN
        (higham13_algorithm13_3_stageHistoryGrowthMatrix hN hm hr A pivotInv) := by
  rw [higham13_algorithm13_3_stageHistoryGrowthMatrix_maxEntryNorm]
  exact higham13_algorithm13_3_stageHistoryBound_contains_initial hm hr A pivotInv

/-- The stage-history growth matrix dominates every recorded concrete
    Algorithm 13.3 Schur stage in the chapter block max norm. -/
theorem higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_stage
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (k : ℕ) (hk : k ≤ m) :
    blockMaxNorm hm hr
        (fun i j => higham13_algorithm13_3_schurStageBlock A pivotInv k i j) ≤
      maxEntryNorm hN
        (higham13_algorithm13_3_stageHistoryGrowthMatrix hN hm hr A pivotInv) := by
  rw [higham13_algorithm13_3_stageHistoryGrowthMatrix_maxEntryNorm]
  exact
    higham13_algorithm13_3_stageHistoryBound_contains_stage
      hm hr A pivotInv k hk

/-- The stage-history growth matrix dominates the Algorithm 13.3 upper factor
    assembled from the recorded stages. -/
theorem higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_upperFromStages
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ)) :
    blockMaxNorm hm hr
        (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
      maxEntryNorm hN
        (higham13_algorithm13_3_stageHistoryGrowthMatrix hN hm hr A pivotInv) := by
  rw [higham13_algorithm13_3_stageHistoryGrowthMatrix_maxEntryNorm]
  exact
    higham13_algorithm13_3_stageHistoryBound_contains_upperFromStages
      hm hr A pivotInv

/-- The finite Algorithm 13.3 stage-history growth matrix dominates the
    ordinary `Fin (m*r)` flattening of the input block matrix. -/
theorem higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_flat_initial
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ)) :
    maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A) ≤
      maxEntryNorm (Nat.mul_pos hm hr)
        (higham13_algorithm13_3_stageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr A pivotInv) := by
  rw [maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm]
  exact
    higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_initial
      (Nat.mul_pos hm hr) hm hr A pivotInv

/-- Any scalar submatrix whose entries are drawn from a recorded Algorithm 13.3
    Schur stage is dominated by the finite stage-history growth matrix. -/
theorem higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_stage_submatrix
    {N m r s : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r) (hs : 0 < s)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (k : ℕ) (hk : k ≤ m)
    (S : Matrix (Fin s) (Fin s) ℝ)
    (rowBlock colBlock : Fin s → Fin m)
    (rowLocal colLocal : Fin s → Fin r)
    (hS : ∀ i j : Fin s,
      S i j =
        higham13_algorithm13_3_schurStageBlock A pivotInv k
          (rowBlock i) (colBlock j) (rowLocal i) (colLocal j)) :
    maxEntryNormRect hs hs S ≤
      maxEntryNorm hN
        (higham13_algorithm13_3_stageHistoryGrowthMatrix hN hm hr A pivotInv) := by
  apply maxEntryNormRect_le_of_entry_abs_le
  intro i j
  rw [hS i j]
  exact le_trans
    (block_entry_abs_le_blockMaxNorm hm hr
      (fun p q =>
        higham13_algorithm13_3_schurStageBlock A pivotInv k p q)
      (rowBlock i) (colBlock j) (rowLocal i) (colLocal j))
    (higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_stage
      hN hm hr A pivotInv k hk)

/-- Tail block table of a recorded Algorithm 13.3 Schur stage, with an
    arbitrary source-to-full-block-index embedding for the tail. -/
noncomputable def higham13_algorithm13_3_schurStageTailBlock
    {m r b : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (k : ℕ) (tail : Fin b → Fin m) :
    Fin b → Fin b → (Fin r → Fin r → ℝ) :=
  fun i j => higham13_algorithm13_3_schurStageBlock A pivotInv k (tail i) (tail j)

@[simp] theorem higham13_algorithm13_3_schurStageTailBlock_apply
    {m r b : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (k : ℕ) (tail : Fin b → Fin m)
    (i j : Fin b) :
    higham13_algorithm13_3_schurStageTailBlock A pivotInv k tail i j =
      higham13_algorithm13_3_schurStageBlock A pivotInv k (tail i) (tail j) := rfl

/-- The finite Algorithm 13.3 stage-history growth matrix dominates the
    standard scalar flattening of any block tail cut out of a recorded stage. -/
theorem higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_flat_stage_tail
    {N m r b : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r) (hb : 0 < b)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (k : ℕ) (hk : k ≤ m)
    (tail : Fin b → Fin m) :
    maxEntryNorm (Nat.mul_pos hb hr)
        (blockMatrixFlatFin
          (higham13_algorithm13_3_schurStageTailBlock A pivotInv k tail)) ≤
      maxEntryNorm hN
        (higham13_algorithm13_3_stageHistoryGrowthMatrix hN hm hr A pivotInv) := by
  rw [maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm hb hr]
  exact le_trans
    (blockMaxNorm_le_of_entry_abs_le hb hr
      (higham13_algorithm13_3_schurStageTailBlock A pivotInv k tail)
      (blockMaxNorm hm hr
        (fun p q => higham13_algorithm13_3_schurStageBlock A pivotInv k p q))
      (by
        intro i j s t
        exact
          block_entry_abs_le_blockMaxNorm hm hr
            (fun p q => higham13_algorithm13_3_schurStageBlock A pivotInv k p q)
            (tail i) (tail j) s t))
    (higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_stage
      hN hm hr A pivotInv k hk)

/-- Active-stage max-entry bounds extend to every block of every recorded
    function-block Schur stage.

    Algorithm 13.3 carries inactive blocks forward, so an active-block theorem
    for each stage bounds the total finite stage table by induction. -/
theorem higham13_algorithm13_3_stageBlock_bound_of_active_bound
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    {C : ℝ}
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageBlock A pivotInv k i j) ≤ C) :
    ∀ k : ℕ, k ≤ m → ∀ i j : Fin m,
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageBlock A pivotInv k i j) ≤ C := by
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

/-- Active-stage max-entry bounds give a block-max bound for one total
    function-block Schur stage. -/
theorem higham13_algorithm13_3_stage_blockMaxNorm_bound_of_active_bound
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    {C : ℝ}
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageBlock A pivotInv k i j) ≤ C)
    (k : ℕ) (hk : k ≤ m) :
    blockMaxNorm hm hr
        (fun i j => higham13_algorithm13_3_schurStageBlock A pivotInv k i j) ≤
      C := by
  apply blockMaxNorm_le_of_entry_abs_le
  intro i j s t
  exact le_trans
    (entry_le_maxEntryNorm hr
      (higham13_algorithm13_3_schurStageBlock A pivotInv k i j) s t)
    (higham13_algorithm13_3_stageBlock_bound_of_active_bound
      hr A pivotInv hActive k hk i j)

/-- A uniform bound on each recorded function-block Schur stage controls the
    finite stage-history bound. -/
theorem higham13_algorithm13_3_stageHistoryBound_le_of_stage_bound
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    {C : ℝ}
    (hStage : ∀ k : ℕ, k ≤ m →
      blockMaxNorm hm hr
          (fun i j => higham13_algorithm13_3_schurStageBlock A pivotInv k i j) ≤
        C) :
    higham13_algorithm13_3_stageHistoryBound hm hr A pivotInv ≤ C := by
  unfold higham13_algorithm13_3_stageHistoryBound
  apply Finset.sup'_le
  intro K _hK
  exact hStage K.val (Nat.le_of_lt_succ K.isLt)

/-- Active-stage max-entry bounds control the max-entry norm of the finite
    function-block stage-history growth object. -/
theorem higham13_algorithm13_3_stageHistoryGrowthMatrix_le_of_active_bound
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    {C : ℝ}
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageBlock A pivotInv k i j) ≤ C) :
    maxEntryNorm hN
        (higham13_algorithm13_3_stageHistoryGrowthMatrix hN hm hr A pivotInv) ≤
      C := by
  rw [higham13_algorithm13_3_stageHistoryGrowthMatrix_maxEntryNorm]
  exact
    higham13_algorithm13_3_stageHistoryBound_le_of_stage_bound hm hr A pivotInv
      (fun k hk =>
        higham13_algorithm13_3_stage_blockMaxNorm_bound_of_active_bound
          hm hr A pivotInv hActive k hk)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8 and equation (13.23):
    the function-block stage-history growth object is bounded by `2‖A‖` once
    the active-stage `2‖A‖` theorem has been proved for every active block. -/
theorem higham13_algorithm13_3_stageHistoryGrowthMatrix_le_two_of_active_stage_bound
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageBlock A pivotInv k i j) ≤
          2 * blockMaxNorm hm hr A) :
    maxEntryNorm hN
        (higham13_algorithm13_3_stageHistoryGrowthMatrix hN hm hr A pivotInv) ≤
      2 * blockMaxNorm hm hr A :=
  higham13_algorithm13_3_stageHistoryGrowthMatrix_le_of_active_bound
    hN hm hr A pivotInv hActive

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    active-stage `2‖A‖` bounds imply `ρ_n <= 2` for the finite function-block
    stage-history growth factor. -/
theorem higham13_algorithm13_3_stageHistoryGrowthFactor_le_two_of_active_stage_bound
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageBlock A pivotInv k i j) ≤
          2 * blockMaxNorm hm hr A) :
    growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
        (higham13_algorithm13_3_stageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
      2 := by
  exact
    growthFactorEntry_le_of_maxEntryNorm_le_mul (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
      (higham13_algorithm13_3_stageHistoryGrowthMatrix
        (Nat.mul_pos hm hr) hm hr A pivotInv)
      hApos
      (by
        rw [maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm hm hr A]
        exact
          higham13_algorithm13_3_stageHistoryGrowthMatrix_le_two_of_active_stage_bound
            (Nat.mul_pos hm hr) hm hr A pivotInv hActive)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    direct one-sided-certificate route to the finite function-block
    stage-history norm bound.

    This is the direct-certificate companion to the source-table route: once
    the concrete `diagLowerCert` certificate satisfies
    `gamma_k <= ‖pivotInv_k‖⁻¹` on active pivots, the finite stage-history
    growth matrix is bounded by `2 * ‖A‖` without introducing an auxiliary
    source inverse-bound table. -/
theorem higham13_algorithm13_3_stageHistoryGrowthMatrix_le_two_of_column_bdd_diag_lower
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
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
    maxEntryNorm hN
        (higham13_algorithm13_3_stageHistoryGrowthMatrix hN hm hr A pivotInv) ≤
      2 * blockMaxNorm hm hr A :=
  higham13_algorithm13_3_stageHistoryGrowthMatrix_le_two_of_active_stage_bound
    hN hm hr A pivotInv
    (fun k i j _hk hik hjk =>
      by
        simpa [higham13_algorithm13_3_schurStageNorm,
          higham13_block_norm_eq_maxEntryNorm hr
            (higham13_algorithm13_3_schurStageBlock A pivotInv k i j)] using
          higham13_algorithm13_3_active_stage_block_bound_of_column_bdd_diag_lower
            hm hr A pivotInv invDiagBound hDom hDiagBound hDiagLower
            k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    direct one-sided-certificate route to `rho <= 2` for the finite
    function-block stage-history growth factor. -/
theorem higham13_algorithm13_3_stageHistoryGrowthFactor_le_two_of_column_bdd_diag_lower
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hDiagLower : SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
        (higham13_algorithm13_3_stageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
      2 := by
  exact
    growthFactorEntry_le_of_maxEntryNorm_le_mul
      (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
      (higham13_algorithm13_3_stageHistoryGrowthMatrix
        (Nat.mul_pos hm hr) hm hr A pivotInv)
      hApos
      (by
        rw [maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm hm hr A]
        exact
          higham13_algorithm13_3_stageHistoryGrowthMatrix_le_two_of_column_bdd_diag_lower
            (Nat.mul_pos hm hr) hm hr A pivotInv invDiagBound hDom hDiagBound
            hDiagLower)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    direct one-sided-certificate package for both Eq.13.21's assembled
    upper-factor bound and the finite function-block `rho <= 2` consequence.

    This is the direct-certificate analogue of the source-table package:
    the remaining analytic obligation is exactly the concrete active
    one-sided pivot certificate for `diagLowerCert`, not an auxiliary table. -/
theorem
    higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_diag_lower
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hDiagLower : SchurStageActivePivotInvDiagLower13_7
      (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
        2 * blockMaxNorm hm hr A ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_stageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 :=
  ⟨higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_diag_lower
      hm hr A pivotInv invDiagBound hDom hDiagBound hDiagLower,
    higham13_algorithm13_3_stageHistoryGrowthFactor_le_two_of_column_bdd_diag_lower
      hm hr A pivotInv hApos invDiagBound hDom hDiagBound hDiagLower⟩

/-- Higham, 2nd ed., Chapter 13, Theorems 13.7--13.8 and Eq.13.21:
    continuous-linear lower-norm source table for both the assembled
    upper-factor bound and the finite function-block `rho <= 2` consequence.

    This composes the arbitrary-norm lower-norm source-table construction with
    the direct one-sided active pivot certificate package.  The remaining
    analytic inputs are the column block diagonal dominance hypothesis, the
    initial diagonal lower table, and the two-sided active pivot inverse
    identities for the chosen continuous-linear model. -/
theorem
    higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_continuousLinearMap_source_table
    {m r : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (stageBlock : ℕ → Fin m → Fin m → E →L[ℝ] E)
    (pivotInvCLM : ℕ → E →L[ℝ] E)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j))
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
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
        2 * blockMaxNorm hm hr A ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_stageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 := by
  have hDiagLower :
      SchurStageActivePivotInvDiagLower13_7
        (higham13_algorithm13_3_diagLowerCert invDiagBound A pivotInv)
        (higham13_algorithm13_3_pivotInvNorm pivotInv) :=
    higham13_algorithm13_3_diagLowerCert_diag_lower_of_continuousLinearMap_source_table
      hunit invDiagBound A pivotInv stageBlock pivotInvCLM
      hInit hStageNorm hPivotNorm hSchur hLeft hRight
  exact
    higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_diag_lower
      hm hr A pivotInv hApos invDiagBound hDom hDiagBound hDiagLower

/-- Higham, 2nd ed., Chapter 13, Theorems 13.7--13.8 and Eq.13.21:
    determinant-nonzero form of the continuous-linear lower-norm source-table
    package for the assembled upper-factor bound and finite function-block
    `rho <= 2` consequence. -/
theorem
    higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_continuousLinearMap_source_table_of_det_ne_zero
    {m r : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hm : 0 < m) (hr : 0 < r)
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (invDiagBound : Fin m → ℝ)
    (stageBlock : ℕ → Fin m → Fin m → E →L[ℝ] E)
    (pivotInvCLM : ℕ → E →L[ℝ] E)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j))
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
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
        2 * blockMaxNorm hm hr A ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_stageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet) ≤
        2 := by
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin A) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin A) hdet
  simpa [hN, hApos] using
    higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_continuousLinearMap_source_table
      hm hr hunit A pivotInv hApos invDiagBound stageBlock pivotInvCLM
      hDom hDiagBound hInit hStageNorm hPivotNorm hSchur hLeft hRight

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    finite function-block stage-history norm bound from active pivot
    right-inverse data plus the reciprocal diagonal certificate. -/
theorem
    higham13_algorithm13_3_stageHistoryGrowthMatrix_le_two_of_column_bdd_pivot_right_inverse_reciprocal
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
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
    maxEntryNorm hN
        (higham13_algorithm13_3_stageHistoryGrowthMatrix hN hm hr A pivotInv) ≤
      2 * blockMaxNorm hm hr A :=
  higham13_algorithm13_3_stageHistoryGrowthMatrix_le_two_of_active_stage_bound
    hN hm hr A pivotInv
    (fun k i j _hk hik hjk =>
      by
        simpa [higham13_algorithm13_3_schurStageNorm,
          higham13_block_norm_eq_maxEntryNorm hr
            (higham13_algorithm13_3_schurStageBlock A pivotInv k i j)] using
          higham13_algorithm13_3_active_stage_block_bound_of_column_bdd_pivot_right_inverse_reciprocal
            hm hr A pivotInv invDiagBound hDom hDiagBound
            hPivotRight hReciprocal k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    finite function-block `rho <= 2` consequence from active pivot
    right-inverse data plus the reciprocal diagonal certificate. -/
theorem
    higham13_algorithm13_3_stageHistoryGrowthFactor_le_two_of_column_bdd_pivot_right_inverse_reciprocal
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
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
    growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
        (higham13_algorithm13_3_stageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
      2 := by
  exact
    growthFactorEntry_le_of_maxEntryNorm_le_mul (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
      (higham13_algorithm13_3_stageHistoryGrowthMatrix
        (Nat.mul_pos hm hr) hm hr A pivotInv)
      hApos
      (by
        rw [maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm hm hr A]
        exact
          higham13_algorithm13_3_stageHistoryGrowthMatrix_le_two_of_column_bdd_pivot_right_inverse_reciprocal
            (Nat.mul_pos hm hr) hm hr A pivotInv invDiagBound hDom hDiagBound
            hPivotRight hReciprocal)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    one package for the right-inverse/reciprocal column-BDD route, proving both
    the Eq.13.21 assembled-upper bound and the finite function-block
    `rho <= 2` consequence. -/
theorem
    higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_pivot_right_inverse_reciprocal
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
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
        2 * blockMaxNorm hm hr A ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_stageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 :=
  ⟨higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_pivot_right_inverse_reciprocal
      hm hr A pivotInv invDiagBound hDom hDiagBound hPivotRight hReciprocal,
    higham13_algorithm13_3_stageHistoryGrowthFactor_le_two_of_column_bdd_pivot_right_inverse_reciprocal
      hm hr A pivotInv hApos invDiagBound hDom hDiagBound
      hPivotRight hReciprocal⟩

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    source-table route to the finite function-block stage-history norm bound.

    This is the norm-level companion of
    `higham13_algorithm13_3_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table`.
    It keeps the source inverse-bound table as the only analytic input. -/
theorem higham13_algorithm13_3_stageHistoryGrowthMatrix_le_two_of_column_bdd_source_table
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
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
    maxEntryNorm hN
        (higham13_algorithm13_3_stageHistoryGrowthMatrix hN hm hr A pivotInv) ≤
      2 * blockMaxNorm hm hr A :=
  higham13_algorithm13_3_stageHistoryGrowthMatrix_le_two_of_active_stage_bound
    hN hm hr A pivotInv
    (fun k i j _hk hik hjk =>
      by
        simpa [higham13_algorithm13_3_schurStageNorm,
          higham13_block_norm_eq_maxEntryNorm hr
            (higham13_algorithm13_3_schurStageBlock A pivotInv k i j)] using
          higham13_algorithm13_3_active_stage_block_bound_of_column_bdd_source_table
            hm hr A pivotInv invDiagBound stageInvDiagBound hDom hDiagBound
            hInit hDiagUpdate hActiveUpper k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.23):
    source-table route to `ρ_n <= 2` for the finite function-block
    stage-history growth factor.

    This composes the active Theorem 13.8 column-BDD source-table wrapper with
    the finite stage-history growth-factor bridge.  The source inverse-bound
    table itself remains the visible analytic obligation. -/
theorem higham13_algorithm13_3_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
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
    growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
        (higham13_algorithm13_3_stageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
      2 :=
  higham13_algorithm13_3_stageHistoryGrowthFactor_le_two_of_active_stage_bound
    hm hr A pivotInv hApos
    (fun k i j _hk hik hjk =>
      by
        simpa [higham13_algorithm13_3_schurStageNorm,
          higham13_block_norm_eq_maxEntryNorm hr
            (higham13_algorithm13_3_schurStageBlock A pivotInv k i j)] using
          higham13_algorithm13_3_active_stage_block_bound_of_column_bdd_source_table
            hm hr A pivotInv invDiagBound stageInvDiagBound hDom hDiagBound
            hInit hDiagUpdate hActiveUpper k i j hik hjk)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    one public source-table package for both Eq.13.21's assembled upper-factor
    bound and the finite function-block stage-history `rho <= 2` consequence.

    This is bookkeeping only: the source inverse-bound table and active
    reciprocal upper bounds remain the mathematical source obligation. -/
theorem
    higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
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
        2 * blockMaxNorm hm hr A ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_stageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 :=
  ⟨higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_source_table
      hm hr A pivotInv invDiagBound stageInvDiagBound hDom hDiagBound
      hInit hDiagUpdate hActiveUpper,
    higham13_algorithm13_3_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table
      hm hr A pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
      hInit hDiagUpdate hActiveUpper⟩

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    reciprocal-equality source-table package for Eq.13.21's assembled
    upper-factor bound and the finite function-block `rho <= 2` consequence.

    The source proof naturally identifies the active source-table entries with
    reciprocal pivot-inverse norms.  This wrapper uses that equality to
    discharge the one-sided active-upper premise of the general source-table
    package; proving the table and its Eq.13.18 update remains open. -/
theorem
    higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_reciprocal
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
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
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
        2 * blockMaxNorm hm hr A ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_stageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 :=
  higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table
    hm hr A pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
    hInit hDiagUpdate
    (fun k hk => by
      rw [hReciprocal k hk])

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    determinant-nonzero reciprocal source-table package for Eq.13.21 and the
    finite function-block `rho <= 2` consequence.

    This is the reciprocal-table analogue of
    `higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_of_det_ne_zero`:
    it derives the positive growth-factor denominator from
    `det (blockMatrixFlatFin A) != 0`, while the source inverse-bound table and
    its Eq.13.18 diagonal-update data remain explicit. -/
theorem
    higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_reciprocal_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInit : ∀ j : Fin m, invDiagBound j ≤ stageInvDiagBound 0 j)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv))
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
        2 * blockMaxNorm hm hr A ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_stageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet) ≤
        2 := by
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin A) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin A) hdet
  simpa [hN, hApos] using
    higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_reciprocal
      hm hr A pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
      hInit hDiagUpdate hReciprocal

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    determinant-nonzero source-table package for Eq.13.21 and the finite
    function-block `rho <= 2` consequence.

    This is the source-table package with the growth-factor denominator
    positivity derived from `det(blockMatrixFlatFin A) != 0`; the source
    inverse-bound table and active reciprocal upper bounds remain explicit. -/
theorem
    higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
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
        2 * blockMaxNorm hm hr A ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_stageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet) ≤
        2 := by
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin A) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin A) hdet
  simpa [hN, hApos] using
    higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table
      hm hr A pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
      hInit hDiagUpdate hActiveUpper

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    exact diagonal-update equality form of the paired source-table package.

    This is a source-facing convenience wrapper over
    `higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table`:
    the initial table is given by equality and the active update is given by
    the displayed recurrence, while the active reciprocal upper bounds remain
    the analytic source obligation. -/
theorem
    higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_of_diag_eq
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitEq : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hDiagEq : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        stageInvDiagBound (k + 1) j =
          stageInvDiagBound k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j)
    (hActiveUpper : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ ≤
        (higham13_algorithm13_3_pivotInvNorm pivotInv k)⁻¹) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
        2 * blockMaxNorm hm hr A ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_stageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 :=
  higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table
    hm hr A pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
    (by
      intro j
      rw [hInitEq j])
    (higham13_algorithm13_3_active_diag_lower_update_of_eq
      A pivotInv stageInvDiagBound hDiagEq)
    hActiveUpper

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    determinant-nonzero exact diagonal-update equality form of the paired
    source-table package.

    This removes the separate positive growth-factor denominator hypothesis
    from the exact-update wrapper; the source inverse-bound table data and
    active reciprocal upper bounds remain explicit. -/
theorem
    higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_of_diag_eq_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitEq : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hDiagEq : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        stageInvDiagBound (k + 1) j =
          stageInvDiagBound k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j)
    (hActiveUpper : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ ≤
        (higham13_algorithm13_3_pivotInvNorm pivotInv k)⁻¹) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
        2 * blockMaxNorm hm hr A ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_stageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet) ≤
        2 :=
  higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_of_det_ne_zero
    hm hr A pivotInv invDiagBound stageInvDiagBound hdet hDom hDiagBound
    (by
      intro j
      rw [hInitEq j])
    (higham13_algorithm13_3_active_diag_lower_update_of_eq
      A pivotInv stageInvDiagBound hDiagEq)
    hActiveUpper

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    exact diagonal-update equality plus reciprocal source-table form of the
    paired Eq.13.21/finite-history package.

    This is the book-shaped source-table surface: the initial source table and
    the active Eq.13.18 recurrence are given by equality, and the active pivot
    entries are reciprocal pivot-inverse norms.  The construction of that
    source table remains the open analytic step. -/
theorem
    higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_of_diag_eq_reciprocal
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitEq : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hDiagEq : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        stageInvDiagBound (k + 1) j =
          stageInvDiagBound k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
        2 * blockMaxNorm hm hr A ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_stageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 :=
  higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_reciprocal
    hm hr A pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
    (by
      intro j
      rw [hInitEq j])
    (higham13_algorithm13_3_active_diag_lower_update_of_eq
      A pivotInv stageInvDiagBound hDiagEq)
    hReciprocal

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    determinant-nonzero exact-update reciprocal source-table package.

    This combines the book-shaped exact-update/reciprocal source-table surface
    with determinant-derived positivity for the growth-factor denominator. -/
theorem
    higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_of_diag_eq_reciprocal_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitEq : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hDiagEq : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        stageInvDiagBound (k + 1) j =
          stageInvDiagBound k j -
            higham13_algorithm13_3_schurStageNorm A pivotInv k j ⟨k, hk⟩ *
              higham13_algorithm13_3_pivotInvNorm pivotInv k *
              higham13_algorithm13_3_schurStageNorm A pivotInv k ⟨k, hk⟩ j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (higham13_algorithm13_3_pivotInvNorm pivotInv)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromStages A pivotInv) ≤
        2 * blockMaxNorm hm hr A ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_stageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet) ≤
        2 := by
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin A) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin A) hdet
  simpa [hN, hApos] using
    higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_of_diag_eq_reciprocal
      hm hr A pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
      hInitEq hDiagEq hReciprocal

end NumStability
