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
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.GrowthBounds
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Equation21
import NumStability.Source.Higham.Chapter13.Problem04.ActiveStageBounds
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStages
import NumStability.Source.Higham.Chapter13.Problem04.StageHistory
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis

/-!
# Source.Higham.Chapter13.Problem04.HistoryEnvelope

This module formalizes the source-facing Chapter 13 statements for
`Problem04.HistoryEnvelope`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    a finite local max-entry growth-history envelope.

    This matrix is a local proof object whose max entry is the maximum of the
    initial matrix, the current Schur complement, and a block upper factor.  It
    is not the recursive GE growth theorem; it is the smallest honest local
    object needed to discharge the common containment hypotheses in the local
    Eq.13.22/Eq.13.23 product bridge. -/
noncomputable def higham13_problem13_4_localGrowthEnvelope
    {N s mb rb : ℕ} (hN : 0 < N) (hs : 0 < s) (hmb : 0 < mb) (hrb : 0 < rb)
    (A : Fin N → Fin N → ℝ)
    (S : Matrix (Fin s) (Fin s) ℝ)
    (Ufac : Fin mb → Fin mb → (Fin rb → Fin rb → ℝ)) :
    Fin N → Fin N → ℝ :=
  fun _ _ =>
    max (maxEntryNorm hN A)
      (max (maxEntryNormRect hs hs S) (blockMaxNorm hmb hrb Ufac))

lemma higham13_problem13_4_localGrowthEnvelope_maxEntryNorm
    {N s mb rb : ℕ} (hN : 0 < N) (hs : 0 < s) (hmb : 0 < mb) (hrb : 0 < rb)
    (A : Fin N → Fin N → ℝ)
    (S : Matrix (Fin s) (Fin s) ℝ)
    (Ufac : Fin mb → Fin mb → (Fin rb → Fin rb → ℝ)) :
    maxEntryNorm hN
        (higham13_problem13_4_localGrowthEnvelope hN hs hmb hrb A S Ufac) =
      max (maxEntryNorm hN A)
        (max (maxEntryNormRect hs hs S) (blockMaxNorm hmb hrb Ufac)) := by
  let c : ℝ :=
    max (maxEntryNorm hN A)
      (max (maxEntryNormRect hs hs S) (blockMaxNorm hmb hrb Ufac))
  have hc : 0 ≤ c := by
    exact le_max_of_le_left (maxEntryNorm_nonneg hN A)
  simpa [higham13_problem13_4_localGrowthEnvelope, c] using
    maxEntryNorm_const_nonneg hN c hc

/-- The local growth-history envelope contains the initial matrix. -/
theorem higham13_problem13_4_localGrowthEnvelope_contains_initial
    {N s mb rb : ℕ} (hN : 0 < N) (hs : 0 < s) (hmb : 0 < mb) (hrb : 0 < rb)
    (A : Fin N → Fin N → ℝ)
    (S : Matrix (Fin s) (Fin s) ℝ)
    (Ufac : Fin mb → Fin mb → (Fin rb → Fin rb → ℝ)) :
    maxEntryNorm hN A ≤
      maxEntryNorm hN
        (higham13_problem13_4_localGrowthEnvelope hN hs hmb hrb A S Ufac) := by
  rw [higham13_problem13_4_localGrowthEnvelope_maxEntryNorm]
  exact le_max_left _ _

/-- The local growth-history envelope contains the current Schur complement. -/
theorem higham13_problem13_4_localGrowthEnvelope_contains_schur
    {N s mb rb : ℕ} (hN : 0 < N) (hs : 0 < s) (hmb : 0 < mb) (hrb : 0 < rb)
    (A : Fin N → Fin N → ℝ)
    (S : Matrix (Fin s) (Fin s) ℝ)
    (Ufac : Fin mb → Fin mb → (Fin rb → Fin rb → ℝ)) :
    maxEntryNormRect hs hs S ≤
      maxEntryNorm hN
        (higham13_problem13_4_localGrowthEnvelope hN hs hmb hrb A S Ufac) := by
  rw [higham13_problem13_4_localGrowthEnvelope_maxEntryNorm]
  exact le_trans (le_max_left _ _) (le_max_right _ _)

/-- The local growth-history envelope contains the block upper factor. -/
theorem higham13_problem13_4_localGrowthEnvelope_contains_block_upper
    {N s mb rb : ℕ} (hN : 0 < N) (hs : 0 < s) (hmb : 0 < mb) (hrb : 0 < rb)
    (A : Fin N → Fin N → ℝ)
    (S : Matrix (Fin s) (Fin s) ℝ)
    (Ufac : Fin mb → Fin mb → (Fin rb → Fin rb → ℝ)) :
    blockMaxNorm hmb hrb Ufac ≤
      maxEntryNorm hN
        (higham13_problem13_4_localGrowthEnvelope hN hs hmb hrb A S Ufac) := by
  rw [higham13_problem13_4_localGrowthEnvelope_maxEntryNorm]
  exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- The local growth-history envelope is the least upper bound needed by the
    three local Problem 13.4 containment premises. -/
theorem higham13_problem13_4_localGrowthEnvelope_le_of_bounds
    {N s mb rb : ℕ} (hN : 0 < N) (hs : 0 < s) (hmb : 0 < mb) (hrb : 0 < rb)
    (A G : Fin N → Fin N → ℝ)
    (S : Matrix (Fin s) (Fin s) ℝ)
    (Ufac : Fin mb → Fin mb → (Fin rb → Fin rb → ℝ))
    (hA_le_G : maxEntryNorm hN A ≤ maxEntryNorm hN G)
    (hS_le_G : maxEntryNormRect hs hs S ≤ maxEntryNorm hN G)
    (hU_le_G : blockMaxNorm hmb hrb Ufac ≤ maxEntryNorm hN G) :
    maxEntryNorm hN
        (higham13_problem13_4_localGrowthEnvelope hN hs hmb hrb A S Ufac) ≤
      maxEntryNorm hN G := by
  rw [higham13_problem13_4_localGrowthEnvelope_maxEntryNorm]
  exact max_le hA_le_G (max_le hS_le_G hU_le_G)

/-- The Algorithm 13.3 finite stage-history growth matrix dominates the local
    Problem 13.4 envelope once the local initial matrix and Schur complement
    are known to lie in that stage history.

    The upper-factor containment is discharged here by
    `higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_upperFromStages`;
    the remaining flat/tail obligations stay visible as hypotheses. -/
theorem higham13_problem13_4_localGrowthEnvelope_le_stageHistoryGrowthMatrix_of_initial_schur
    {N m r s : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r) (hs : 0 < s)
    (Aflat : Fin N → Fin N → ℝ)
    (S : Matrix (Fin s) (Fin s) ℝ)
    (Ablk : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (hA_le_hist :
      maxEntryNorm hN Aflat ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_stageHistoryGrowthMatrix hN hm hr Ablk pivotInv))
    (hS_le_hist :
      maxEntryNormRect hs hs S ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_stageHistoryGrowthMatrix hN hm hr Ablk pivotInv)) :
    maxEntryNorm hN
        (higham13_problem13_4_localGrowthEnvelope hN hs hm hr Aflat S
          (higham13_algorithm13_3_upperFromStages Ablk pivotInv)) ≤
      maxEntryNorm hN
        (higham13_algorithm13_3_stageHistoryGrowthMatrix hN hm hr Ablk pivotInv) := by
  exact
    higham13_problem13_4_localGrowthEnvelope_le_of_bounds
      hN hs hm hr Aflat
      (higham13_algorithm13_3_stageHistoryGrowthMatrix hN hm hr Ablk pivotInv)
      S (higham13_algorithm13_3_upperFromStages Ablk pivotInv)
      hA_le_hist hS_le_hist
      (higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_upperFromStages
        hN hm hr Ablk pivotInv)

/-- The finite Algorithm 13.3 stage history dominates the local Problem 13.4
    envelope when the local initial matrix is the standard flattening of the
    block input and the local Schur complement is a scalar submatrix of a
    recorded Schur stage.

    This removes the max-entry bookkeeping from the remaining recursive
    Problem 13.4 task: the only source-specific hypothesis left here is the
    entrywise identification of the local Schur complement with the appropriate
    recorded stage/tail. -/
theorem
    higham13_problem13_4_localGrowthEnvelope_le_stageHistoryGrowthMatrix_of_flat_initial_stage_submatrix
    {m r s : ℕ} (hm : 0 < m) (hr : 0 < r) (hs : 0 < s)
    (Ablk : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (k : ℕ) (hk : k ≤ m)
    (S : Matrix (Fin s) (Fin s) ℝ)
    (rowBlock colBlock : Fin s → Fin m)
    (rowLocal colLocal : Fin s → Fin r)
    (hS : ∀ i j : Fin s,
      S i j =
        higham13_algorithm13_3_schurStageBlock Ablk pivotInv k
          (rowBlock i) (colBlock j) (rowLocal i) (colLocal j)) :
    maxEntryNorm (Nat.mul_pos hm hr)
        (higham13_problem13_4_localGrowthEnvelope (Nat.mul_pos hm hr) hs hm hr
          (blockMatrixFlatFin Ablk) S
          (higham13_algorithm13_3_upperFromStages Ablk pivotInv)) ≤
      maxEntryNorm (Nat.mul_pos hm hr)
        (higham13_algorithm13_3_stageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr Ablk pivotInv) := by
  exact
    higham13_problem13_4_localGrowthEnvelope_le_stageHistoryGrowthMatrix_of_initial_schur
      (Nat.mul_pos hm hr) hm hr hs
      (blockMatrixFlatFin Ablk) S Ablk pivotInv
      (higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_flat_initial
        hm hr Ablk pivotInv)
      (higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_stage_submatrix
        (Nat.mul_pos hm hr) hm hr hs Ablk pivotInv k hk S
        rowBlock colBlock rowLocal colLocal hS)

/-- The finite Algorithm 13.3 stage history dominates the local Problem 13.4
    envelope whose Schur-complement slot is the flattened tail of a recorded
    Schur stage.

    This is the packaged tail version of
    `higham13_problem13_4_localGrowthEnvelope_le_stageHistoryGrowthMatrix_of_flat_initial_stage_submatrix`;
    the remaining recursive source proof is to identify the local Schur
    complement used by the split with this flattened tail table. -/
theorem
    higham13_problem13_4_localGrowthEnvelope_le_stageHistoryGrowthMatrix_of_flat_initial_flat_stage_tail
    {m r b : ℕ} (hm : 0 < m) (hr : 0 < r) (hb : 0 < b)
    (Ablk : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (pivotInv : ℕ → (Fin r → Fin r → ℝ))
    (k : ℕ) (hk : k ≤ m)
    (tail : Fin b → Fin m) :
    maxEntryNorm (Nat.mul_pos hm hr)
        (higham13_problem13_4_localGrowthEnvelope
          (Nat.mul_pos hm hr) (Nat.mul_pos hb hr) hm hr
          (blockMatrixFlatFin Ablk)
          (blockMatrixFlatFin
            (higham13_algorithm13_3_schurStageTailBlock Ablk pivotInv k tail))
          (higham13_algorithm13_3_upperFromStages Ablk pivotInv)) ≤
      maxEntryNorm (Nat.mul_pos hm hr)
        (higham13_algorithm13_3_stageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr Ablk pivotInv) := by
  exact
    higham13_problem13_4_localGrowthEnvelope_le_stageHistoryGrowthMatrix_of_initial_schur
      (Nat.mul_pos hm hr) hm hr (Nat.mul_pos hb hr)
      (blockMatrixFlatFin Ablk)
      (blockMatrixFlatFin
        (higham13_algorithm13_3_schurStageTailBlock Ablk pivotInv k tail))
      Ablk pivotInv
      (higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_flat_initial
        hm hr Ablk pivotInv)
      (higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_flat_stage_tail
        (Nat.mul_pos hm hr) hm hr hb Ablk pivotInv k hk tail)

/-- Matrix-product version of
    `higham13_problem13_4_localGrowthEnvelope_le_stageHistoryGrowthMatrix_of_initial_schur`.

    The upper-factor containment is discharged by the source-faithful
    matrix-stage history. -/
theorem
    higham13_problem13_4_localGrowthEnvelope_le_matrixStageHistoryGrowthMatrix_of_initial_schur
    {N m r s : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r) (hs : 0 < s)
    (Aflat : Fin N → Fin N → ℝ)
    (S : Matrix (Fin s) (Fin s) ℝ)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hA_le_hist :
      maxEntryNorm hN Aflat ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv))
    (hS_le_hist :
      maxEntryNormRect hs hs S ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv)) :
    maxEntryNorm hN
        (higham13_problem13_4_localGrowthEnvelope hN hs hm hr Aflat S
          (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv)) ≤
      maxEntryNorm hN
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv) := by
  exact
    higham13_problem13_4_localGrowthEnvelope_le_of_bounds
      hN hs hm hr Aflat
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv)
      S (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv)
      hA_le_hist hS_le_hist
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_upperFromMatrixStages
        hN hm hr Ablk pivotInv)

/-- Matrix-product stage-history domination of the local Problem 13.4 envelope
    whose Schur slot is a flattened tail of a source-faithful recorded stage. -/
theorem
    higham13_problem13_4_localGrowthEnvelope_le_matrixStageHistoryGrowthMatrix_of_flat_initial_flat_stage_tail
    {m r b : ℕ} (hm : 0 < m) (hr : 0 < r) (hb : 0 < b)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (k : ℕ) (hk : k ≤ m)
    (tail : Fin b → Fin m) :
    maxEntryNorm (Nat.mul_pos hm hr)
        (higham13_problem13_4_localGrowthEnvelope
          (Nat.mul_pos hm hr) (Nat.mul_pos hb hr) hm hr
          (blockMatrixFlatFin Ablk)
          (blockMatrixFlatFin
            (higham13_algorithm13_3_schurStageMatrixTailBlock Ablk pivotInv k tail))
          (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv)) ≤
      maxEntryNorm (Nat.mul_pos hm hr)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr Ablk pivotInv) := by
  exact
    higham13_problem13_4_localGrowthEnvelope_le_matrixStageHistoryGrowthMatrix_of_initial_schur
      (Nat.mul_pos hm hr) hm hr (Nat.mul_pos hb hr)
      (blockMatrixFlatFin Ablk)
      (blockMatrixFlatFin
        (higham13_algorithm13_3_schurStageMatrixTailBlock Ablk pivotInv k tail))
      Ablk pivotInv
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_flat_initial
        hm hr Ablk pivotInv)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_flat_stage_tail
        (Nat.mul_pos hm hr) hm hr hb Ablk pivotInv k hk tail)

/-- One-step source specialization: the matrix-product stage-history growth
    matrix dominates the local Problem 13.4 envelope whose Schur slot is the
    book's first block Schur complement. -/
theorem
    higham13_problem13_4_localGrowthEnvelope_le_matrixStageHistoryGrowthMatrix_of_blockSchur_first_tail
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (A11_inv : Matrix (Fin r) (Fin r) ℝ)
    (hpivot : pivotInv 0 = A11_inv) :
    maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (higham13_problem13_4_localGrowthEnvelope
          (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.mul_pos hm hr)
          (Nat.succ_pos m) hr
          (blockMatrixFlatFin Ablk)
          (blockMatrixFlatFin (blockSchur Ablk A11_inv))
          (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv)) ≤
      maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk pivotInv) := by
  have htail :
      higham13_algorithm13_3_schurStageMatrixTailBlock Ablk pivotInv 1 Fin.succ =
        blockSchur Ablk A11_inv := by
    exact higham13_algorithm13_3_schurStageMatrixBlock_one_tail_eq_blockSchur
      Ablk pivotInv A11_inv hpivot
  rw [← htail]
  exact
    higham13_problem13_4_localGrowthEnvelope_le_matrixStageHistoryGrowthMatrix_of_flat_initial_flat_stage_tail
      (Nat.succ_pos m) hr hm Ablk pivotInv 1 (by omega) Fin.succ

/-- First-split version of
    `higham13_problem13_4_localGrowthEnvelope_le_matrixStageHistoryGrowthMatrix_of_blockSchur_first_tail`.

    The initial matrix is flattened as the two-by-two split
    `r + m*r`, matching the local Schur complement used in equations
    (13.22) and (13.23), while the dominating history still records the
    source-faithful `(m+1)` block Algorithm 13.3 stages. -/
theorem
    higham13_problem13_4_localGrowthEnvelope_le_matrixStageHistoryGrowthMatrix_of_blockSchur_first_split
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (A11_inv : Matrix (Fin r) (Fin r) ℝ)
    (hpivot : pivotInv 0 = A11_inv) :
    maxEntryNorm (Nat.add_pos_left hr (m * r))
        (higham13_problem13_4_localGrowthEnvelope
          (Nat.add_pos_left hr (m * r)) (Nat.mul_pos hm hr)
          (Nat.succ_pos m) hr
          (blockMatrixFirstSplitFlat Ablk)
          (blockMatrixFlatFin (blockSchur Ablk A11_inv))
          (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv)) ≤
      maxEntryNorm (Nat.add_pos_left hr (m * r))
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        (Nat.add_pos_left hr (m * r)) (Nat.succ_pos m) hr Ablk pivotInv) := by
  have htail :
      higham13_algorithm13_3_schurStageMatrixTailBlock Ablk pivotInv 1 Fin.succ =
        blockSchur Ablk A11_inv := by
    exact higham13_algorithm13_3_schurStageMatrixBlock_one_tail_eq_blockSchur
      Ablk pivotInv A11_inv hpivot
  refine
    higham13_problem13_4_localGrowthEnvelope_le_matrixStageHistoryGrowthMatrix_of_initial_schur
      (Nat.add_pos_left hr (m * r)) (Nat.succ_pos m) hr (Nat.mul_pos hm hr)
      (blockMatrixFirstSplitFlat Ablk)
      (blockMatrixFlatFin (blockSchur Ablk A11_inv))
      Ablk pivotInv ?_ ?_
  · exact le_trans
      (maxEntryNorm_blockMatrixFirstSplitFlat_le_blockMaxNorm hm hr Ablk)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
        (Nat.add_pos_left hr (m * r)) (Nat.succ_pos m) hr Ablk pivotInv)
  · have hS :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_flat_stage_tail
        (Nat.add_pos_left hr (m * r)) (Nat.succ_pos m) hr hm
        Ablk pivotInv 1 (by omega) Fin.succ
    rw [htail] at hS
    simpa [maxEntryNormRect_eq_maxEntryNorm (Nat.mul_pos hm hr)] using hS

/-- First-split domination with an explicit positivity witness for
    `r + m*r`.  This avoids later proof-irrelevance churn when the same
    witness is threaded through `growthFactorEntry`. -/
theorem
    higham13_problem13_4_localGrowthEnvelope_le_matrixStageHistoryGrowthMatrix_of_blockSchur_first_split_of_hN
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hN : 0 < r + m * r)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (A11_inv : Matrix (Fin r) (Fin r) ℝ)
    (hpivot : pivotInv 0 = A11_inv) :
    maxEntryNorm hN
        (higham13_problem13_4_localGrowthEnvelope
          hN (Nat.mul_pos hm hr) (Nat.succ_pos m) hr
          (blockMatrixFirstSplitFlat Ablk)
          (blockMatrixFlatFin (blockSchur Ablk A11_inv))
          (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv)) ≤
      maxEntryNorm hN
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos m) hr Ablk pivotInv) := by
  have htail :
      higham13_algorithm13_3_schurStageMatrixTailBlock Ablk pivotInv 1 Fin.succ =
        blockSchur Ablk A11_inv := by
    exact higham13_algorithm13_3_schurStageMatrixBlock_one_tail_eq_blockSchur
      Ablk pivotInv A11_inv hpivot
  refine
    higham13_problem13_4_localGrowthEnvelope_le_matrixStageHistoryGrowthMatrix_of_initial_schur
      hN (Nat.succ_pos m) hr (Nat.mul_pos hm hr)
      (blockMatrixFirstSplitFlat Ablk)
      (blockMatrixFlatFin (blockSchur Ablk A11_inv))
      Ablk pivotInv ?_ ?_
  · exact le_trans
      (maxEntryNorm_blockMatrixFirstSplitFlat_le_blockMaxNorm_of_hN hN hm hr Ablk)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
        hN (Nat.succ_pos m) hr Ablk pivotInv)
  · have hS :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_flat_stage_tail
        hN (Nat.succ_pos m) hr hm Ablk pivotInv 1 (by omega) Fin.succ
    rw [htail] at hS
    simpa [maxEntryNormRect_eq_maxEntryNorm (Nat.mul_pos hm hr)] using hS

end NumStability
