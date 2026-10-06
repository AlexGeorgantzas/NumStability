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
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Equation22
import NumStability.Source.Higham.Chapter13.Problem04.ActiveStageBounds
import NumStability.Source.Higham.Chapter13.Problem04.BlockInverseBounds
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis
import NumStability.Source.Higham.Chapter13.Theorem02.Factorization
import NumStability.Source.Higham.Chapter13.Theorem07.PivotExistence

/-!
# Source.Higham.Chapter13.Problem04.LocalGrowth

This module formalizes the source-facing Chapter 13 statements for
`Problem04.LocalGrowth`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    source local lower-block estimate with the one-growth-factor budget used
    by the text before the ambient Eq.13.22/Eq.13.23 comparison.

    This is the direct lower-left half of Problem 13.4 for a square local
    `2 x 2` partition.  It keeps the local growth factor and local exact-κ
    object visible, instead of immediately enlarging them to the ambient
    `rho^2 * kappa(A)` budget. -/
theorem higham13_problem13_4_single_block_source_lblock_bound_from_local_growth
    {r : ℕ} (hr : 0 < r)
    (A11 A12 A21 A22 P : Matrix (Fin r) (Fin r) ℝ)
    (U : Fin (r + r) → Fin (r + r) → ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)]
    (hpivot : P = ⅟A11)
    (hApos :
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (fun p q : Fin (r + r) =>
          (Matrix.fromBlocks A11 A12 A21 A22)
            (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)))
    (hS_le_U :
      maxEntryNormRect hr hr (A22 - A21 * ⅟A11 * A12) ≤
        maxEntryNorm (Nat.add_pos_left hr r) U) :
    maxEntryNorm hr (A21 * P) ≤
      (r : ℝ) *
        growthFactorEntry (Nat.add_pos_left hr r)
          (fun p q : Fin (r + r) =>
            (Matrix.fromBlocks A11 A12 A21 A22)
              (finSumFinEquiv.symm p) (finSumFinEquiv.symm q))
          U hApos *
        (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (fun p q : Fin (r + r) =>
              (Matrix.fromBlocks A11 A12 A21 A22)
                (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)) *
          maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (nonsingInv (r + r)
              (fun p q : Fin (r + r) =>
                (Matrix.fromBlocks A11 A12 A21 A22)
                  (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)))) := by
  subst P
  let hN : 0 < r + r := Nat.add_pos_left hr r
  let A : Fin (r + r) → Fin (r + r) → ℝ :=
    fun p q =>
      (Matrix.fromBlocks A11 A12 A21 A22)
        (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)
  have hA11_block : A11 =
      fun i j : Fin r =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin r))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin r)) := by
    ext i j
    dsimp [A]
    rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
    simp
  have hA12_block : A12 =
      fun (i : Fin r) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin r))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin r)) := by
    ext i j
    dsimp [A]
    rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
    simp
  have hA21_block : A21 =
      fun (i : Fin r) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin r))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin r)) := by
    ext i j
    dsimp [A]
    rw [finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd]
    simp
  have hA22_block : A22 =
      fun i j : Fin r =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin r))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin r)) := by
    ext i j
    dsimp [A]
    rw [finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_natAdd]
    simp
  have hpair :=
    higham13_problem13_4_maxEntry_bounds_from_source_growthFactorEntry_exact_kappa
      hr hr hN A U A11 A12 A21 A22
      hA11_block hA12_block hA21_block hA22_block
      hApos r le_rfl
      (by simpa [hN, A] using hS_le_U)
  calc
    maxEntryNorm hr ((A21 * ⅟A11 : Matrix (Fin r) (Fin r) ℝ))
        = maxEntryNormRect hr hr ((A21 * ⅟A11 : Matrix (Fin r) (Fin r) ℝ)) := by
          rw [maxEntryNormRect_eq_maxEntryNorm hr]
    _ ≤ (r : ℝ) *
          growthFactorEntry hN A U hApos *
          (maxEntryNormRect hN hN A *
            maxEntryNormRect hN hN (nonsingInv (r + r) A)) :=
          hpair.1
    _ = (r : ℝ) *
          growthFactorEntry (Nat.add_pos_left hr r)
            (fun p q : Fin (r + r) =>
              (Matrix.fromBlocks A11 A12 A21 A22)
                (finSumFinEquiv.symm p) (finSumFinEquiv.symm q))
            U hApos *
          (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
              (fun p q : Fin (r + r) =>
                (Matrix.fromBlocks A11 A12 A21 A22)
                  (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)) *
            maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
              (nonsingInv (r + r)
                (fun p q : Fin (r + r) =>
                  (Matrix.fromBlocks A11 A12 A21 A22)
                    (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)))) := by
          rfl

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    single block multiplier bound from a local two-block growth budget.

    A block multiplier `A₂₁ A₁₁⁻¹` appearing in one Algorithm 13.3 stage is
    the lower-left product in a local `2 × 2` block partition.  This theorem
    applies the source Problem 13.4 lower-left bridge to that local partition
    and then allows the local `ρ²κ(A)` budget to be compared with any ambient
    source budget `C`.

    The comparison hypothesis is intentionally explicit: the theorem closes the
    lower-left multiplier extraction, while the recursive Schur-condition
    propagation that supplies the ambient budget remains a separate source
    obligation. -/
theorem higham13_problem13_4_single_block_multiplier_bound_from_local_growth_budget
    {r : ℕ} (hr : 0 < r)
    (A11 A12 A21 A22 P : Matrix (Fin r) (Fin r) ℝ)
    (U : Fin (r + r) → Fin (r + r) → ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)]
    (hpivot : P = ⅟A11)
    (hApos :
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (fun p q : Fin (r + r) =>
          (Matrix.fromBlocks A11 A12 A21 A22)
            (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)))
    (n : ℕ) (hrn : (r : ℝ) ≤ (n : ℝ))
    (hA_le_U :
      maxEntryNorm (Nat.add_pos_left hr r)
          (fun p q : Fin (r + r) =>
            (Matrix.fromBlocks A11 A12 A21 A22)
              (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)) ≤
        maxEntryNorm (Nat.add_pos_left hr r) U)
    (hS_le_U :
      maxEntryNormRect hr hr (A22 - A21 * ⅟A11 * A12) ≤
        maxEntryNorm (Nat.add_pos_left hr r) U)
    {C : ℝ}
    (hBudget :
      (growthFactorEntry (Nat.add_pos_left hr r)
          (fun p q : Fin (r + r) =>
            (Matrix.fromBlocks A11 A12 A21 A22)
              (finSumFinEquiv.symm p) (finSumFinEquiv.symm q))
          U hApos) ^ 2 *
        (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (fun p q : Fin (r + r) =>
              (Matrix.fromBlocks A11 A12 A21 A22)
                (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)) *
          maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (nonsingInv (r + r)
              (fun p q : Fin (r + r) =>
                (Matrix.fromBlocks A11 A12 A21 A22)
                  (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)))) ≤ C) :
    maxEntryNorm hr (A21 * P) ≤ (n : ℝ) * C := by
  subst P
  let hN : 0 < r + r := Nat.add_pos_left hr r
  let A : Fin (r + r) → Fin (r + r) → ℝ :=
    fun p q =>
      (Matrix.fromBlocks A11 A12 A21 A22)
        (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)
  let localKappa : ℝ :=
    maxEntryNormRect hN hN A *
      maxEntryNormRect hN hN (nonsingInv (r + r) A)
  have hA11_block : A11 =
      fun i j : Fin r =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin r))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin r)) := by
    ext i j
    dsimp [A]
    rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
    simp
  have hA12_block : A12 =
      fun (i : Fin r) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin r))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin r)) := by
    ext i j
    dsimp [A]
    rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
    simp
  have hA21_block : A21 =
      fun (i : Fin r) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin r))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin r)) := by
    ext i j
    dsimp [A]
    rw [finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd]
    simp
  have hA22_block : A22 =
      fun i j : Fin r =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin r))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin r)) := by
    ext i j
    dsimp [A]
    rw [finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_natAdd]
    simp
  have hLocal :
      maxEntryNormRect hr hr ((A21 * ⅟A11 : Matrix (Fin r) (Fin r) ℝ)) ≤
        (n : ℝ) * (growthFactorEntry hN A U hApos) ^ 2 * localKappa := by
    exact
      higham13_problem13_4_L21_eq13_22_premise_from_source_growthFactorEntry_exact_kappa
        hr hr hN A U A11 A12 A21 A22
        hA11_block hA12_block hA21_block hA22_block
        hApos n hrn
        (by simpa [hN, A] using hA_le_U)
        (by simpa [hN, A] using hS_le_U)
  have hBudget' :
      (growthFactorEntry hN A U hApos) ^ 2 * localKappa ≤ C := by
    simpa [hN, A, localKappa] using hBudget
  have hmul :
      (n : ℝ) * ((growthFactorEntry hN A U hApos) ^ 2 * localKappa) ≤
        (n : ℝ) * C :=
    mul_le_mul_of_nonneg_left hBudget' (Nat.cast_nonneg n)
  calc
    maxEntryNorm hr ((A21 * ⅟A11 : Matrix (Fin r) (Fin r) ℝ))
        = maxEntryNormRect hr hr ((A21 * ⅟A11 : Matrix (Fin r) (Fin r) ℝ)) := by
            rw [maxEntryNormRect_eq_maxEntryNorm hr]
    _ ≤ (n : ℝ) * (growthFactorEntry hN A U hApos) ^ 2 * localKappa := hLocal
    _ = (n : ℝ) * ((growthFactorEntry hN A U hApos) ^ 2 * localKappa) := by
          ring
    _ ≤ (n : ℝ) * C := hmul

/-- The local `2 × 2` block matrix seen by one Algorithm 13.3 multiplier.

    For an active lower multiplier in column `j` and row `i`, the local
    Problem 13.4 partition is formed from the stage-`j` blocks
    `(j,j)`, `(j,i)`, `(i,j)`, and `(i,i)`. -/
noncomputable def higham13_algorithm13_3_stageLocalBlockMatrix {m r : ℕ}
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (i j : Fin m) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) ℝ :=
  Matrix.fromBlocks
    (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
    (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j i)
    (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j)
    (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i i)

/-- The scalar `Fin (r+r)` flattening of the local `2 × 2` stage matrix. -/
noncomputable def higham13_algorithm13_3_stageLocalFlatMatrix {m r : ℕ}
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (i j : Fin m) :
    Fin (r + r) → Fin (r + r) → ℝ :=
  fun p q =>
    higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j
      (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)

/-- The local `2 × 2` stage matrix has positive flattened max-entry norm when
    the unflattened block matrix is invertible. -/
theorem higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (i j : Fin m)
    [Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)] :
    0 < maxEntryNorm (Nat.add_pos_left hr r)
      (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) := by
  let M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) ℝ :=
    higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j
  let e : Fin (r + r) ≃ Fin r ⊕ Fin r := finSumFinEquiv.symm
  letI : Invertible (M.submatrix e e) :=
    Matrix.submatrixEquivInvertible M e e
  have hpos := maxEntryNorm_pos_of_invertible (Nat.add_pos_left hr r)
    (M.submatrix e e)
  simpa [higham13_algorithm13_3_stageLocalFlatMatrix, M, e] using hpos

/-- Table form of `higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible`
    for every active lower-multiplier pair. -/
theorem higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hInvFull : ∀ i j : Fin m, j.val < i.val →
      Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)) :
    ∀ i j : Fin m, ∀ _hji : j.val < i.val,
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) := by
  intro i j hji
  letI : Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j) :=
    hInvFull i j hji
  exact higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible
    hr Ablk pivotInv i j

/-- The local Schur complement in the `2 × 2` stage matrix for one multiplier,
    using the `Invertible` inverse of the local pivot block. -/
noncomputable def higham13_algorithm13_3_stageLocalSchurOfInv {m r : ℕ}
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (i j : Fin m)
    [Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)] :
    Matrix (Fin r) (Fin r) ℝ :=
  higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i i -
    higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
      ⅟(higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j) *
      higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j i

/-- The local Schur complement for one Algorithm 13.3 multiplier, written with
    the supplied pivot inverse rather than Mathlib's `⅟`.  This is total for
    all stage pairs and is later identified with `stageLocalSchurOfInv` from a
    right-inverse certificate. -/
noncomputable def higham13_algorithm13_3_stageLocalSchurOfPivot {m r : ℕ}
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (i j : Fin m) :
    Matrix (Fin r) (Fin r) ℝ :=
  higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i i -
    higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
      pivotInv j.val *
      higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j i

theorem higham13_algorithm13_3_stageLocalSchurOfPivot_eq_stageLocalSchurOfInv
    {m r : ℕ}
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (i j : Fin m)
    [Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)]
    (hpivot :
      pivotInv j.val =
        ⅟(higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)) :
    higham13_algorithm13_3_stageLocalSchurOfPivot Ablk pivotInv i j =
      higham13_algorithm13_3_stageLocalSchurOfInv Ablk pivotInv i j := by
  simp [higham13_algorithm13_3_stageLocalSchurOfPivot,
    higham13_algorithm13_3_stageLocalSchurOfInv, hpivot]

/-- Canonical local growth matrix for the `2 × 2` stage partition associated
    with one Algorithm 13.3 multiplier.

    It is the constant matrix whose max-entry norm contains the flattened local
    block matrix and the pivot-written local Schur complement. -/
noncomputable def higham13_algorithm13_3_stageLocalGrowthMatrix {m r : ℕ}
    (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (i j : Fin m) :
    Fin (r + r) → Fin (r + r) → ℝ :=
  fun _ _ =>
    max
      (maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
      (maxEntryNormRect hr hr
        (higham13_algorithm13_3_stageLocalSchurOfPivot Ablk pivotInv i j))

theorem higham13_algorithm13_3_stageLocalGrowthMatrix_contains_initial
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (i j : Fin m) :
    maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) ≤
      maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j) := by
  let c : ℝ :=
    max
      (maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
      (maxEntryNormRect hr hr
        (higham13_algorithm13_3_stageLocalSchurOfPivot Ablk pivotInv i j))
  have hc_nonneg : 0 ≤ c := by
    exact le_trans
      (maxEntryNorm_nonneg (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
      (le_max_left _ _)
  have hc_le :
      c ≤ maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j) := by
    have hentry :=
      entry_le_maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
        (⟨0, Nat.add_pos_left hr r⟩ : Fin (r + r))
        (⟨0, Nat.add_pos_left hr r⟩ : Fin (r + r))
    simpa [higham13_algorithm13_3_stageLocalGrowthMatrix, c, abs_of_nonneg hc_nonneg]
      using hentry
  exact le_trans (le_max_left _ _) hc_le

theorem higham13_algorithm13_3_stageLocalGrowthMatrix_contains_schurOfPivot
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (i j : Fin m) :
    maxEntryNormRect hr hr
        (higham13_algorithm13_3_stageLocalSchurOfPivot Ablk pivotInv i j) ≤
      maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j) := by
  let c : ℝ :=
    max
      (maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
      (maxEntryNormRect hr hr
        (higham13_algorithm13_3_stageLocalSchurOfPivot Ablk pivotInv i j))
  have hc_nonneg : 0 ≤ c := by
    exact le_trans
      (maxEntryNorm_nonneg (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
      (le_max_left _ _)
  have hc_le :
      c ≤ maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j) := by
    have hentry :=
      entry_le_maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
        (⟨0, Nat.add_pos_left hr r⟩ : Fin (r + r))
        (⟨0, Nat.add_pos_left hr r⟩ : Fin (r + r))
    simpa [higham13_algorithm13_3_stageLocalGrowthMatrix, c, abs_of_nonneg hc_nonneg]
      using hentry
  exact le_trans (le_max_right _ _) hc_le

theorem higham13_algorithm13_3_stageLocalGrowthMatrix_contains_schurOfInv
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (i j : Fin m)
    [Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)]
    (hpivot :
      pivotInv j.val =
        ⅟(higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)) :
    maxEntryNormRect hr hr
        (higham13_algorithm13_3_stageLocalSchurOfInv Ablk pivotInv i j) ≤
      maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j) := by
  have h :=
    higham13_algorithm13_3_stageLocalGrowthMatrix_contains_schurOfPivot
      hr Ablk pivotInv i j
  rw [higham13_algorithm13_3_stageLocalSchurOfPivot_eq_stageLocalSchurOfInv
    Ablk pivotInv i j hpivot] at h
  exact h

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 / Problem 13.4:
    source local lower-block estimate for one active matrix-stage multiplier.

    This specializes
    `higham13_problem13_4_single_block_source_lblock_bound_from_local_growth`
    to the `2 x 2` stage partition around an active pair `j < i`.  It proves
    the local lower-block premise consumed by the source-shaped Eq.13.22 and
    Eq.13.23 wrappers from the canonical local growth matrix, provided the
    displayed local growth and local exact-κ quantities are dominated by the
    user-supplied local budgets. -/
theorem higham13_algorithm13_3_source_lblock_bound_from_stageLocalGrowth_le
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (i j : Fin m) (_hji : j.val < i.val)
    (rhoLocal kappaLocal : ℝ)
    [Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)]
    [Invertible (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
      inferInstance)]
    [Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j)]
    (hPivotRight :
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (pivotInv j.val))
    (hLocalApos :
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hRhoLocal_ge :
      growthFactorEntry (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
          (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
          hLocalApos ≤ rhoLocal)
    (hKappaLocal_ge :
      (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (nonsingInv (r + r)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))) ≤
        kappaLocal) :
    maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
          pivotInv j.val) ≤
      (r : ℝ) * rhoLocal * kappaLocal := by
  have hpivot :
      pivotInv j.val =
        ⅟(higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j) :=
    matrix_invOf_eq_of_isRightInverse
      (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
      (pivotInv j.val) hPivotRight
  letI : Invertible
      (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i i -
        higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
          ⅟(higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j) *
          higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j i) := by
    simpa [higham13_algorithm13_3_stageLocalSchurOfInv] using
      (inferInstance :
        Invertible (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
          inferInstance))
  letI : Invertible
      (Matrix.fromBlocks
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j i)
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j)
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i i)) := by
    simpa [higham13_algorithm13_3_stageLocalBlockMatrix] using
      (inferInstance :
        Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j))
  let rho0 : ℝ :=
    growthFactorEntry (Nat.add_pos_left hr r)
      (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
      (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
      hLocalApos
  let kappa0 : ℝ :=
    maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
        (nonsingInv (r + r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
  have hbase :
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rho0 * kappa0 := by
    exact
      higham13_problem13_4_single_block_source_lblock_bound_from_local_growth
        hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j i)
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j)
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i i)
        (pivotInv j.val)
        (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
        hpivot
        (by
          simpa [higham13_algorithm13_3_stageLocalFlatMatrix,
            higham13_algorithm13_3_stageLocalBlockMatrix] using hLocalApos)
        (by
          simpa [higham13_algorithm13_3_stageLocalSchurOfInv] using
            higham13_algorithm13_3_stageLocalGrowthMatrix_contains_schurOfInv
              hr Ablk pivotInv i j hpivot)
  have hrho0_nonneg : 0 ≤ rho0 := by
    simpa [rho0] using
      growthFactorEntry_nonneg (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
        (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
        hLocalApos
  have hkappa0_nonneg : 0 ≤ kappa0 := by
    exact mul_nonneg
      (maxEntryNormRect_nonneg (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
      (maxEntryNormRect_nonneg (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
        (nonsingInv (r + r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)))
  have hrhoLocal_nonneg : 0 ≤ rhoLocal := le_trans hrho0_nonneg (by
    simpa [rho0] using hRhoLocal_ge)
  have hprod : rho0 * kappa0 ≤ rhoLocal * kappaLocal :=
    mul_le_mul (by simpa [rho0] using hRhoLocal_ge)
      (by simpa [kappa0] using hKappaLocal_ge)
      hkappa0_nonneg hrhoLocal_nonneg
  have hscaled : (r : ℝ) * rho0 * kappa0 ≤ (r : ℝ) * rhoLocal * kappaLocal := by
    have h := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg r)
    simpa [mul_assoc] using h
  exact le_trans hbase hscaled

/-- The pivot-written local Schur complement for an active pair is the next
    recorded diagonal block of the source-faithful matrix-product stage table. -/
theorem higham13_algorithm13_3_stageLocalSchurOfPivot_eq_next_diag
    {m r : ℕ}
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (i j : Fin m) (hji : j.val < i.val) :
    higham13_algorithm13_3_stageLocalSchurOfPivot Ablk pivotInv i j =
      higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (j.val + 1) i i := by
  have hjm : j.val < m := Nat.lt_trans hji i.isLt
  have hactive : j.val + 1 ≤ i.val ∧ j.val + 1 ≤ i.val :=
    ⟨Nat.succ_le_of_lt hji, Nat.succ_le_of_lt hji⟩
  simp [higham13_algorithm13_3_stageLocalSchurOfPivot,
    higham13_algorithm13_3_schurStageMatrixBlock,
    higham13_algorithm13_3_schurStageBlock, hjm, hactive]

/-- The scalar flattening of one active local `2 x 2` stage partition is
    contained in the global matrix-stage history. -/
theorem higham13_algorithm13_3_stageLocalFlatMatrix_le_matrixStageHistoryGrowthMatrix
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (i j : Fin m) :
    maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) ≤
      maxEntryNorm (Nat.mul_pos hm hr)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr Ablk pivotInv) := by
  have hStage :
      blockMaxNorm hm hr
          (fun p q => higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val p q) ≤
        maxEntryNorm (Nat.mul_pos hm hr)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_stage
      (Nat.mul_pos hm hr) hm hr Ablk pivotInv j.val (Nat.le_of_lt j.isLt)
  have hrect :
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) ≤
        maxEntryNorm (Nat.mul_pos hm hr)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) := by
    apply maxEntryNormRect_le_of_entry_abs_le
    intro p q
    have hentry :
        |higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j p q| ≤
          blockMaxNorm hm hr
            (fun a b =>
              higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val a b) := by
      rcases hp : finSumFinEquiv.symm p with a | a
      · rcases hq : finSumFinEquiv.symm q with b | b
        · simpa [higham13_algorithm13_3_stageLocalFlatMatrix,
            higham13_algorithm13_3_stageLocalBlockMatrix, hp, hq, Matrix.fromBlocks]
            using
              block_entry_abs_le_blockMaxNorm hm hr
                (fun x y =>
                  higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val x y)
                j j a b
        · simpa [higham13_algorithm13_3_stageLocalFlatMatrix,
            higham13_algorithm13_3_stageLocalBlockMatrix, hp, hq, Matrix.fromBlocks]
            using
              block_entry_abs_le_blockMaxNorm hm hr
                (fun x y =>
                  higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val x y)
                j i a b
      · rcases hq : finSumFinEquiv.symm q with b | b
        · simpa [higham13_algorithm13_3_stageLocalFlatMatrix,
            higham13_algorithm13_3_stageLocalBlockMatrix, hp, hq, Matrix.fromBlocks]
            using
              block_entry_abs_le_blockMaxNorm hm hr
                (fun x y =>
                  higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val x y)
                i j a b
        · simpa [higham13_algorithm13_3_stageLocalFlatMatrix,
            higham13_algorithm13_3_stageLocalBlockMatrix, hp, hq, Matrix.fromBlocks]
            using
              block_entry_abs_le_blockMaxNorm hm hr
                (fun x y =>
                  higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val x y)
                i i a b
    exact le_trans hentry hStage
  simpa [maxEntryNormRect_eq_maxEntryNorm (Nat.add_pos_left hr r)] using hrect

/-- The pivot-written local Schur complement for one active pair is contained
    in the global matrix-stage history. -/
theorem higham13_algorithm13_3_stageLocalSchurOfPivot_le_matrixStageHistoryGrowthMatrix
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (i j : Fin m) (hji : j.val < i.val) :
    maxEntryNormRect hr hr
        (higham13_algorithm13_3_stageLocalSchurOfPivot Ablk pivotInv i j) ≤
      maxEntryNorm (Nat.mul_pos hm hr)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr Ablk pivotInv) := by
  have hjm : j.val < m := Nat.lt_trans hji i.isLt
  have hstage_le :
      blockMaxNorm hm hr
          (fun p q =>
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (j.val + 1) p q) ≤
        maxEntryNorm (Nat.mul_pos hm hr)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr Ablk pivotInv) :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_stage
      (Nat.mul_pos hm hr) hm hr Ablk pivotInv (j.val + 1)
      (Nat.succ_le_of_lt hjm)
  have hblock :
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (j.val + 1) i i) ≤
        blockMaxNorm hm hr
          (fun p q =>
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (j.val + 1) p q) :=
    block_le_blockMaxNorm hm hr
      (fun p q =>
        higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (j.val + 1) p q)
      i i
  have hschur :
      maxEntryNormRect hr hr
          (higham13_algorithm13_3_stageLocalSchurOfPivot Ablk pivotInv i j) =
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv (j.val + 1) i i) := by
    rw [higham13_algorithm13_3_stageLocalSchurOfPivot_eq_next_diag
      Ablk pivotInv i j hji]
    rw [maxEntryNormRect_eq_maxEntryNorm hr]
  rw [hschur]
  exact le_trans hblock hstage_le

theorem higham13_algorithm13_3_stageLocalGrowthMatrix_maxEntryNorm
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (i j : Fin m) :
    maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j) =
      max
        (maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
        (maxEntryNormRect hr hr
          (higham13_algorithm13_3_stageLocalSchurOfPivot Ablk pivotInv i j)) := by
  let c : ℝ :=
    max
      (maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
      (maxEntryNormRect hr hr
        (higham13_algorithm13_3_stageLocalSchurOfPivot Ablk pivotInv i j))
  have hc_nonneg : 0 ≤ c := by
    exact le_trans
      (maxEntryNorm_nonneg (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
      (le_max_left _ _)
  apply le_antisymm
  · have hrect :
        maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j) ≤
          c := by
      apply maxEntryNormRect_le_of_entry_abs_le
      intro p q
      simp [higham13_algorithm13_3_stageLocalGrowthMatrix, c,
        abs_of_nonneg hc_nonneg]
    simpa [maxEntryNormRect_eq_maxEntryNorm (Nat.add_pos_left hr r), c] using hrect
  · have hentry :=
      entry_le_maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
        (⟨0, Nat.add_pos_left hr r⟩ : Fin (r + r))
        (⟨0, Nat.add_pos_left hr r⟩ : Fin (r + r))
    simpa [higham13_algorithm13_3_stageLocalGrowthMatrix, c,
      abs_of_nonneg hc_nonneg] using hentry

/-- The canonical local growth matrix for one active `2 x 2` stage partition is
    dominated by the global matrix-stage history.  This closes the max-entry
    stage-history bookkeeping part of the local-to-global budget comparison;
    the inverse/condition-number comparison remains a separate obligation. -/
theorem higham13_algorithm13_3_stageLocalGrowthMatrix_le_matrixStageHistoryGrowthMatrix
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (i j : Fin m) (hji : j.val < i.val) :
    maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j) ≤
      maxEntryNorm (Nat.mul_pos hm hr)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr Ablk pivotInv) := by
  rw [higham13_algorithm13_3_stageLocalGrowthMatrix_maxEntryNorm]
  exact max_le
    (higham13_algorithm13_3_stageLocalFlatMatrix_le_matrixStageHistoryGrowthMatrix
      hm hr Ablk pivotInv i j)
    (higham13_algorithm13_3_stageLocalSchurOfPivot_le_matrixStageHistoryGrowthMatrix
      hm hr Ablk pivotInv i j hji)

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    source `rhoLocal <= rhoFull` comparison for a canonical active
    stage-local growth factor, reduced to the remaining denominator
    comparison.

    The numerator comparison is supplied by
    `higham13_algorithm13_3_stageLocalGrowthMatrix_le_matrixStageHistoryGrowthMatrix`.
    The explicit `hBase` hypothesis records the source obligation that the
    local `2 x 2` stage denominator is at least the original flattened source
    denominator. -/
theorem higham13_algorithm13_3_stageLocalGrowthFactor_le_matrixStageHistoryGrowthFactor_of_base_le
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (i j : Fin m) (hji : j.val < i.val)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
    (hLocalApos :
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
    (hBase :
      maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk) ≤
        maxEntryNorm (Nat.add_pos_left hr r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)) :
    growthFactorEntry (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
        (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
        hLocalApos ≤
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr Ablk pivotInv) hApos := by
  exact
    growthFactorEntry_le_of_growth_le_of_base_le
      (Nat.add_pos_left hr r) (Nat.mul_pos hm hr)
      (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
      (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
      (blockMatrixFlatFin Ablk)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        (Nat.mul_pos hm hr) hm hr Ablk pivotInv)
      hLocalApos hApos
      (higham13_algorithm13_3_stageLocalGrowthMatrix_le_matrixStageHistoryGrowthMatrix
        hm hr Ablk pivotInv i j hji)
      hBase

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 audit:
    the denominator/base comparison needed to turn the canonical local
    `rhoLocal <= rhoFull` route into an unconditional theorem is false in
    general.

    In this `3 x 3` scalar-block example, the active local pair `(j,i)=(0,1)`
    has positive local denominator `1`, but the flattened input has max-entry
    norm `100` in a block outside that local `2 x 2` stage partition.  Hence
    the comparison `||A||_max <= ||A_local||_max` must be supplied by a
    source-specific argument or replaced by another condition comparison; it
    cannot be discharged from stage-locality alone. -/
theorem higham13_stage_local_base_comparison_counterexample :
    ∃ (Ablk : Fin 3 → Fin 3 → Matrix (Fin 1) (Fin 1) ℝ)
      (pivotInv : ℕ → Matrix (Fin 1) (Fin 1) ℝ) (i j : Fin 3),
      j.val < i.val ∧
        0 < maxEntryNorm (by norm_num : 0 < 1 + 1)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) ∧
        ¬ maxEntryNorm (by norm_num : 0 < 3 * 1) (blockMatrixFlatFin Ablk) ≤
          maxEntryNorm (by norm_num : 0 < 1 + 1)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) := by
  let Ablk : Fin 3 → Fin 3 → Matrix (Fin 1) (Fin 1) ℝ := fun i j _ _ =>
    if i.val = 2 ∧ j.val = 2 then 100
    else if i.val = 0 ∧ j.val = 0 then 1
    else 0
  let pivotInv : ℕ → Matrix (Fin 1) (Fin 1) ℝ := fun _ _ _ => 0
  refine ⟨Ablk, pivotInv, (1 : Fin 3), (0 : Fin 3), by norm_num, ?_, ?_⟩
  · have hLocal :
        maxEntryNorm (by norm_num : 0 < 1 + 1)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv
            (1 : Fin 3) (0 : Fin 3)) = 1 := by
      apply le_antisymm
      · have hrect :
            maxEntryNormRect (by norm_num : 0 < 1 + 1) (by norm_num : 0 < 1 + 1)
              (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv
                (1 : Fin 3) (0 : Fin 3)) ≤ 1 := by
          apply maxEntryNormRect_le_of_entry_abs_le
          intro p q
          rcases hp : finSumFinEquiv.symm p with a | a
          · rcases hq : finSumFinEquiv.symm q with b | b
            · fin_cases a
              fin_cases b
              norm_num [higham13_algorithm13_3_stageLocalFlatMatrix,
                higham13_algorithm13_3_stageLocalBlockMatrix,
                higham13_algorithm13_3_schurStageMatrixBlock,
                higham13_algorithm13_3_schurStageBlock, Ablk, pivotInv,
                Matrix.fromBlocks, hp, hq]
            · fin_cases a
              fin_cases b
              norm_num [higham13_algorithm13_3_stageLocalFlatMatrix,
                higham13_algorithm13_3_stageLocalBlockMatrix,
                higham13_algorithm13_3_schurStageMatrixBlock,
                higham13_algorithm13_3_schurStageBlock, Ablk, pivotInv,
                Matrix.fromBlocks, hp, hq]
          · rcases hq : finSumFinEquiv.symm q with b | b
            · fin_cases a
              fin_cases b
              norm_num [higham13_algorithm13_3_stageLocalFlatMatrix,
                higham13_algorithm13_3_stageLocalBlockMatrix,
                higham13_algorithm13_3_schurStageMatrixBlock,
                higham13_algorithm13_3_schurStageBlock, Ablk, pivotInv,
                Matrix.fromBlocks, hp, hq]
            · fin_cases a
              fin_cases b
              norm_num [higham13_algorithm13_3_stageLocalFlatMatrix,
                higham13_algorithm13_3_stageLocalBlockMatrix,
                higham13_algorithm13_3_schurStageMatrixBlock,
                higham13_algorithm13_3_schurStageBlock, Ablk, pivotInv,
                Matrix.fromBlocks, hp, hq]
        simpa [maxEntryNormRect_eq_maxEntryNorm (by norm_num : 0 < 1 + 1)]
          using hrect
      · have h :=
          entry_le_maxEntryNorm (by norm_num : 0 < 1 + 1)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv
              (1 : Fin 3) (0 : Fin 3))
            (finSumFinEquiv (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Fin 1))
            (finSumFinEquiv (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Fin 1))
        have hentry :
            higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv
                (1 : Fin 3) (0 : Fin 3)
                (finSumFinEquiv (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Fin 1))
                (finSumFinEquiv (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Fin 1)) = 1 := by
          norm_num [higham13_algorithm13_3_stageLocalFlatMatrix,
            higham13_algorithm13_3_stageLocalBlockMatrix,
            higham13_algorithm13_3_schurStageMatrixBlock,
            higham13_algorithm13_3_schurStageBlock, Ablk, pivotInv,
            Matrix.fromBlocks]
        rw [hentry, abs_of_nonneg (by norm_num : 0 ≤ (1 : ℝ))] at h
        exact h
    norm_num [hLocal]
  · have hGlobal :
        maxEntryNorm (by norm_num : 0 < 3 * 1) (blockMatrixFlatFin Ablk) = 100 := by
      apply le_antisymm
      · have hrect :
            maxEntryNormRect (by norm_num : 0 < 3 * 1) (by norm_num : 0 < 3 * 1)
              (blockMatrixFlatFin Ablk) ≤ 100 := by
          apply maxEntryNormRect_le_of_entry_abs_le
          intro p q
          rcases hp : finProdFinEquiv.symm p with ⟨ip, sp⟩
          rcases hq : finProdFinEquiv.symm q with ⟨jq, tq⟩
          fin_cases ip <;> fin_cases jq <;> fin_cases sp <;> fin_cases tq <;>
            norm_num [blockMatrixFlatFin, Ablk, hp, hq]
        simpa [maxEntryNormRect_eq_maxEntryNorm (by norm_num : 0 < 3 * 1)]
          using hrect
      · have h :=
          entry_le_maxEntryNorm (by norm_num : 0 < 3 * 1)
            (blockMatrixFlatFin Ablk)
            (finProdFinEquiv ((2 : Fin 3), (0 : Fin 1)))
            (finProdFinEquiv ((2 : Fin 3), (0 : Fin 1)))
        have hentry :
            blockMatrixFlatFin Ablk
                (finProdFinEquiv ((2 : Fin 3), (0 : Fin 1)))
                (finProdFinEquiv ((2 : Fin 3), (0 : Fin 1))) = 100 := by
          have happly :=
            blockMatrixFlatFin_apply Ablk (2 : Fin 3) (2 : Fin 3)
              (0 : Fin 1) (0 : Fin 1)
          rw [happly]
          norm_num [Ablk]
        rw [hentry, abs_of_nonneg (by norm_num : 0 ≤ (100 : ℝ))] at h
        exact h
    have hLocal :
        maxEntryNorm (by norm_num : 0 < 1 + 1)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv
            (1 : Fin 3) (0 : Fin 3)) = 1 := by
      apply le_antisymm
      · have hrect :
            maxEntryNormRect (by norm_num : 0 < 1 + 1) (by norm_num : 0 < 1 + 1)
              (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv
                (1 : Fin 3) (0 : Fin 3)) ≤ 1 := by
          apply maxEntryNormRect_le_of_entry_abs_le
          intro p q
          rcases hp : finSumFinEquiv.symm p with a | a
          · rcases hq : finSumFinEquiv.symm q with b | b
            · fin_cases a
              fin_cases b
              norm_num [higham13_algorithm13_3_stageLocalFlatMatrix,
                higham13_algorithm13_3_stageLocalBlockMatrix,
                higham13_algorithm13_3_schurStageMatrixBlock,
                higham13_algorithm13_3_schurStageBlock, Ablk, pivotInv,
                Matrix.fromBlocks, hp, hq]
            · fin_cases a
              fin_cases b
              norm_num [higham13_algorithm13_3_stageLocalFlatMatrix,
                higham13_algorithm13_3_stageLocalBlockMatrix,
                higham13_algorithm13_3_schurStageMatrixBlock,
                higham13_algorithm13_3_schurStageBlock, Ablk, pivotInv,
                Matrix.fromBlocks, hp, hq]
          · rcases hq : finSumFinEquiv.symm q with b | b
            · fin_cases a
              fin_cases b
              norm_num [higham13_algorithm13_3_stageLocalFlatMatrix,
                higham13_algorithm13_3_stageLocalBlockMatrix,
                higham13_algorithm13_3_schurStageMatrixBlock,
                higham13_algorithm13_3_schurStageBlock, Ablk, pivotInv,
                Matrix.fromBlocks, hp, hq]
            · fin_cases a
              fin_cases b
              norm_num [higham13_algorithm13_3_stageLocalFlatMatrix,
                higham13_algorithm13_3_stageLocalBlockMatrix,
                higham13_algorithm13_3_schurStageMatrixBlock,
                higham13_algorithm13_3_schurStageBlock, Ablk, pivotInv,
                Matrix.fromBlocks, hp, hq]
        simpa [maxEntryNormRect_eq_maxEntryNorm (by norm_num : 0 < 1 + 1)]
          using hrect
      · have h :=
          entry_le_maxEntryNorm (by norm_num : 0 < 1 + 1)
            (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv
              (1 : Fin 3) (0 : Fin 3))
            (finSumFinEquiv (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Fin 1))
            (finSumFinEquiv (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Fin 1))
        have hentry :
            higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv
                (1 : Fin 3) (0 : Fin 3)
                (finSumFinEquiv (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Fin 1))
                (finSumFinEquiv (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Fin 1)) = 1 := by
          norm_num [higham13_algorithm13_3_stageLocalFlatMatrix,
            higham13_algorithm13_3_stageLocalBlockMatrix,
            higham13_algorithm13_3_schurStageMatrixBlock,
            higham13_algorithm13_3_schurStageBlock, Ablk, pivotInv,
            Matrix.fromBlocks]
        rw [hentry, abs_of_nonneg (by norm_num : 0 ≤ (1 : ℝ))] at h
        exact h
    norm_num [hGlobal, hLocal]

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 audit:
    one-sided containment of a local matrix norm and its inverse norm does not
    imply the cross-multiplied inverse-ratio comparison needed by the recursive
    Eq.13.22/Eq.13.23 budget transport.

    The scalar values `A = 100`, `S = 1`, `Ainv = 1`, `Sinv = 1` satisfy
    `S <= A` and `Sinv <= Ainv`, but fail `Sinv * A <= Ainv * S`. -/
theorem higham13_inverse_ratio_one_sided_containment_counterexample :
    ∃ a s ainv sinv : ℝ,
      0 ≤ a ∧ 0 ≤ s ∧ 0 ≤ ainv ∧ 0 ≤ sinv ∧
        s ≤ a ∧ sinv ≤ ainv ∧ ¬ sinv * a ≤ ainv * s := by
  refine ⟨100, 1, 1, 1, ?_⟩
  norm_num

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 audit:
    the inverse-ratio hypothesis exposed by the recursive Eq.13.22/Eq.13.23
    adapters is strictly stronger than ordinary one-sided containment of a
    local matrix norm and its inverse norm. -/
theorem higham13_inverse_ratio_not_implied_by_one_sided_containment :
    ¬ (∀ a s ainv sinv : ℝ,
      0 ≤ a → 0 ≤ s → 0 ≤ ainv → 0 ≤ sinv →
        s ≤ a → sinv ≤ ainv → sinv * a ≤ ainv * s) := by
  intro h
  rcases higham13_inverse_ratio_one_sided_containment_counterexample with
    ⟨a, s, ainv, sinv, ha, hs, hainv, hsinv, hsa, hsinva, hbad⟩
  exact hbad (h a s ainv sinv ha hs hainv hsinv hsa hsinva)

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 audit:
    even an honest principal-tail inverse relation does not imply the
    cross-multiplied inverse-ratio comparison needed by the recursive
    Eq.13.22/Eq.13.23 tail-transport route.

    The diagonal full matrix `diag(100,1,1)` and its principal tail
    `diag(1,1)` have right-inverse certificates, the tail and tail inverse are
    principal lower-right blocks of the full matrix and full inverse, and the
    ordinary one-sided max-entry containments hold.  Nevertheless
    `||S^{-1}|| ||A|| <= ||A^{-1}|| ||S||` fails. -/
theorem higham13_inverse_ratio_principal_tail_counterexample :
    ∃ A Ainv : Fin 3 → Fin 3 → ℝ,
    ∃ S Sinv : Fin 2 → Fin 2 → ℝ,
      IsRightInverse 3 A Ainv ∧ IsRightInverse 2 S Sinv ∧
        (∀ i j : Fin 2, S i j = A (Fin.succ i) (Fin.succ j)) ∧
        (∀ i j : Fin 2, Sinv i j = Ainv (Fin.succ i) (Fin.succ j)) ∧
        maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) S ≤
          maxEntryNormRect (by norm_num : 0 < 3) (by norm_num : 0 < 3) A ∧
        maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) Sinv ≤
          maxEntryNormRect (by norm_num : 0 < 3) (by norm_num : 0 < 3) Ainv ∧
        ¬ maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) Sinv *
            maxEntryNormRect (by norm_num : 0 < 3) (by norm_num : 0 < 3) A ≤
          maxEntryNormRect (by norm_num : 0 < 3) (by norm_num : 0 < 3) Ainv *
            maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) S := by
  let A : Fin 3 → Fin 3 → ℝ := fun i j =>
    if i = j then
      if i = (0 : Fin 3) then 100 else 1
    else 0
  let Ainv : Fin 3 → Fin 3 → ℝ := fun i j =>
    if i = j then
      if i = (0 : Fin 3) then (1 / 100 : ℝ) else 1
    else 0
  let S : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then 1 else 0
  let Sinv : Fin 2 → Fin 2 → ℝ := S
  have hA_right : IsRightInverse 3 A Ainv := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [A, Ainv]
  have hS_right : IsRightInverse 2 S Sinv := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [S, Sinv]
  have hS_tail : ∀ i j : Fin 2, S i j = A (Fin.succ i) (Fin.succ j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [A, S]
  have hSinv_tail :
      ∀ i j : Fin 2, Sinv i j = Ainv (Fin.succ i) (Fin.succ j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Ainv, S, Sinv]
  have hA_norm :
      maxEntryNormRect (by norm_num : 0 < 3) (by norm_num : 0 < 3) A = 100 := by
    apply le_antisymm
    · apply maxEntryNormRect_le_of_entry_abs_le
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num [A]
    · have h :=
        entry_le_maxEntryNormRect (by norm_num : 0 < 3) (by norm_num : 0 < 3)
          A (0 : Fin 3) (0 : Fin 3)
      norm_num [A] at h
      exact h
  have hAinv_norm :
      maxEntryNormRect (by norm_num : 0 < 3) (by norm_num : 0 < 3) Ainv = 1 := by
    apply le_antisymm
    · apply maxEntryNormRect_le_of_entry_abs_le
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num [Ainv]
    · have h :=
        entry_le_maxEntryNormRect (by norm_num : 0 < 3) (by norm_num : 0 < 3)
          Ainv (1 : Fin 3) (1 : Fin 3)
      norm_num [Ainv] at h
      exact h
  have hS_norm :
      maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) S = 1 := by
    apply le_antisymm
    · apply maxEntryNormRect_le_of_entry_abs_le
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num [S]
    · have h :=
        entry_le_maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2)
          S (0 : Fin 2) (0 : Fin 2)
      norm_num [S] at h
      exact h
  have hSinv_norm :
      maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) Sinv = 1 := by
    simpa [Sinv] using hS_norm
  refine ⟨A, Ainv, S, Sinv, hA_right, hS_right, hS_tail, hSinv_tail, ?_, ?_, ?_⟩
  · rw [hS_norm, hA_norm]
    norm_num
  · rw [hSinv_norm, hAinv_norm]
  · norm_num [hSinv_norm, hA_norm, hAinv_norm, hS_norm]

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 audit:
    a global all-active-suffix inverse-entry table cannot be inferred from
    nonsingularity of the final matrix and the active pivot block alone.

    The matrix `[[1/2, 1], [1, 0]]` has inverse `[[0, 1], [1, -1/2]]`, whose
    max-entry norm is `1`; but the first `1 x 1` active pivot block has inverse
    entry `2`.  Thus the source-table condition bounding every active pivot
    inverse entry by the final inverse max-entry norm is false without an
    additional hypothesis. -/
theorem higham13_problem13_4_all_tail_inverse_entry_bound_counterexample :
    ∃ A Ainv : Fin 2 → Fin 2 → ℝ,
    ∃ P Pinv : Fin 1 → Fin 1 → ℝ,
      IsRightInverse 2 A Ainv ∧ IsLeftInverse 2 A Ainv ∧
        IsRightInverse 1 P Pinv ∧ IsLeftInverse 1 P Pinv ∧
        (∀ i j : Fin 1, P i j = A (0 : Fin 2) (0 : Fin 2)) ∧
        maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) Ainv = 1 ∧
        ¬ (∀ i j : Fin 1,
          |Pinv i j| ≤
            maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) Ainv) := by
  let A : Fin 2 → Fin 2 → ℝ := fun i j =>
    if i = (0 : Fin 2) ∧ j = (0 : Fin 2) then (1 / 2 : ℝ)
    else if i = (0 : Fin 2) ∧ j = (1 : Fin 2) then 1
    else if i = (1 : Fin 2) ∧ j = (0 : Fin 2) then 1
    else 0
  let Ainv : Fin 2 → Fin 2 → ℝ := fun i j =>
    if i = (0 : Fin 2) ∧ j = (0 : Fin 2) then 0
    else if i = (0 : Fin 2) ∧ j = (1 : Fin 2) then 1
    else if i = (1 : Fin 2) ∧ j = (0 : Fin 2) then 1
    else (-1 / 2 : ℝ)
  let P : Fin 1 → Fin 1 → ℝ := fun _ _ => (1 / 2 : ℝ)
  let Pinv : Fin 1 → Fin 1 → ℝ := fun _ _ => 2
  have hA_right : IsRightInverse 2 A Ainv := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, Ainv, Fin.sum_univ_two]
    all_goals rfl
  have hA_left : IsLeftInverse 2 A Ainv := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, Ainv, Fin.sum_univ_two]
    all_goals rfl
  have hP_right : IsRightInverse 1 P Pinv := by
    intro i j
    fin_cases i
    fin_cases j
    norm_num [P, Pinv, Fin.sum_univ_one]
  have hP_left : IsLeftInverse 1 P Pinv := by
    intro i j
    fin_cases i
    fin_cases j
    norm_num [P, Pinv, Fin.sum_univ_one]
  have hP_initial : ∀ i j : Fin 1, P i j = A (0 : Fin 2) (0 : Fin 2) := by
    intro i j
    fin_cases i
    fin_cases j
    norm_num [A, P]
  have hAinv_norm :
      maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) Ainv = 1 := by
    apply le_antisymm
    · apply maxEntryNormRect_le_of_entry_abs_le
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num [Ainv]
    · have h :=
        entry_le_maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2)
          Ainv (0 : Fin 2) (1 : Fin 2)
      simpa [Ainv] using h
  refine ⟨A, Ainv, P, Pinv, hA_right, hA_left, hP_right, hP_left,
    hP_initial, hAinv_norm, ?_⟩
  intro hbound
  have h := hbound (0 : Fin 1) (0 : Fin 1)
  rw [hAinv_norm] at h
  norm_num [Pinv] at h

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 audit:
    the all-active-suffix inverse-entry table also fails when the offending
    pivot block is realized as the canonical stage-zero active suffix of
    Algorithm 13.3.

    This is the source-facing companion to
    `higham13_problem13_4_all_tail_inverse_entry_bound_counterexample`: the
    scalar `2 x 2` witness is packaged as `1 x 1` blocks, its product-index
    flattening agrees with the scalar matrix on all displayed block entries,
    and the canonical active-suffix block at `k = 0`, `q = 0` is exactly the
    pivot block whose inverse entry is too large. -/
theorem higham13_problem13_4_all_tail_inverse_entry_bound_counterexample_activeSuffix :
    ∃ A Ainv : Fin 2 → Fin 2 → ℝ,
    ∃ Ablk : Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1) ℝ,
    ∃ pivotInv : ℕ → Matrix (Fin 1) (Fin 1) ℝ,
    ∃ P Pinv : Fin 1 → Fin 1 → ℝ,
      IsRightInverse 2 A Ainv ∧ IsLeftInverse 2 A Ainv ∧
        IsRightInverse 1 P Pinv ∧ IsLeftInverse 1 P Pinv ∧
        (∀ i j : Fin 2,
          blockMatrixFlatFin Ablk (finProdFinEquiv (i, (0 : Fin 1)))
            (finProdFinEquiv (j, (0 : Fin 1))) = A i j) ∧
        (∀ i j : Fin 1, P i j = A (0 : Fin 2) (0 : Fin 2)) ∧
        (∀ i j s t,
          higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv
              0 0 (by norm_num) i j s t = P s t) ∧
        maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) Ainv = 1 ∧
        ¬ (∀ i j : Fin 1,
          |Pinv i j| ≤
            maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) Ainv) := by
  rcases higham13_problem13_4_all_tail_inverse_entry_bound_counterexample with
    ⟨A, Ainv, P, Pinv, hA_right, hA_left, hP_right, hP_left,
      hP_initial, hAinv_norm, hbad⟩
  let Ablk : Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1) ℝ := fun i j _ _ => A i j
  let pivotInv : ℕ → Matrix (Fin 1) (Fin 1) ℝ := fun _ _ _ => 0
  have hFlat :
      ∀ i j : Fin 2,
        blockMatrixFlatFin Ablk (finProdFinEquiv (i, (0 : Fin 1)))
          (finProdFinEquiv (j, (0 : Fin 1))) = A i j := by
    intro i j
    rw [blockMatrixFlatFin_apply]
  have hActive :
      ∀ i j s t,
        higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv
            0 0 (by norm_num) i j s t = P s t := by
    intro i j s t
    fin_cases i
    fin_cases j
    simpa [Ablk, higham13_algorithm13_3_activeSuffixStageTailBlock,
      higham13_algorithm13_3_activeSuffixTail,
      higham13_algorithm13_3_schurStageMatrixTailBlock,
      higham13_algorithm13_3_schurStageMatrixBlock,
      higham13_algorithm13_3_schurStageBlock] using (hP_initial s t).symm
  exact ⟨A, Ainv, Ablk, pivotInv, P, Pinv, hA_right, hA_left, hP_right,
    hP_left, hFlat, hP_initial, hActive, hAinv_norm, hbad⟩

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 audit:
    the recovered Pro source-statement audit gives a stronger scalar
    counterexample to the all-active-suffix inverse-entry table.

    The `3 x 3` matrix `diag(1, [[1/2, 1], [1, 1/2]])` has successful scalar
    Gaussian elimination pivots `1`, `1/2`, and `-3/2`.  Its inverse has
    entrywise max norm `4/3`, but the one-by-one shorter suffix `[1/2]` inside
    the first Schur tail has inverse entry `2`.  Therefore the old
    all-active-suffix table is false even with successful elimination; the
    source route must stay on full recursively generated Schur tails or add a
    genuine stronger hypothesis. -/
theorem
    higham13_problem13_4_all_tail_inverse_entry_bound_counterexample_successful_scalar_ge :
    ∃ A Ainv : Fin 3 → Fin 3 → ℝ,
    ∃ G Ginv : Fin 2 → Fin 2 → ℝ,
    ∃ T Tinv : Fin 1 → Fin 1 → ℝ,
      IsRightInverse 3 A Ainv ∧ IsLeftInverse 3 A Ainv ∧
        IsRightInverse 2 G Ginv ∧ IsLeftInverse 2 G Ginv ∧
        IsRightInverse 1 T Tinv ∧ IsLeftInverse 1 T Tinv ∧
        (∀ i j : Fin 2, G i j = A (Fin.succ i) (Fin.succ j)) ∧
        (∀ i j : Fin 1, T i j = G (0 : Fin 2) (0 : Fin 2)) ∧
        A (0 : Fin 3) (0 : Fin 3) = 1 ∧
        G (0 : Fin 2) (0 : Fin 2) = (1 / 2 : ℝ) ∧
        G (1 : Fin 2) (1 : Fin 2) -
            G (1 : Fin 2) (0 : Fin 2) *
              (G (0 : Fin 2) (0 : Fin 2))⁻¹ *
              G (0 : Fin 2) (1 : Fin 2) = (-3 / 2 : ℝ) ∧
        maxEntryNormRect (by norm_num : 0 < 3) (by norm_num : 0 < 3) Ainv =
          (4 / 3 : ℝ) ∧
        ¬ (∀ i j : Fin 1,
          |Tinv i j| ≤
            maxEntryNormRect (by norm_num : 0 < 3) (by norm_num : 0 < 3)
              Ainv) := by
  let A : Fin 3 → Fin 3 → ℝ := fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 1, 1 => (1 / 2 : ℝ)
    | 1, 2 => 1
    | 2, 1 => 1
    | 2, 2 => (1 / 2 : ℝ)
    | _, _ => 0
  let Ainv : Fin 3 → Fin 3 → ℝ := fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 1, 1 => (-2 / 3 : ℝ)
    | 1, 2 => (4 / 3 : ℝ)
    | 2, 1 => (4 / 3 : ℝ)
    | 2, 2 => (-2 / 3 : ℝ)
    | _, _ => 0
  let G : Fin 2 → Fin 2 → ℝ := fun i j =>
    match i.val, j.val with
    | 0, 0 => (1 / 2 : ℝ)
    | 0, 1 => 1
    | 1, 0 => 1
    | _, _ => (1 / 2 : ℝ)
  let Ginv : Fin 2 → Fin 2 → ℝ := fun i j =>
    match i.val, j.val with
    | 0, 0 => (-2 / 3 : ℝ)
    | 0, 1 => (4 / 3 : ℝ)
    | 1, 0 => (4 / 3 : ℝ)
    | _, _ => (-2 / 3 : ℝ)
  let T : Fin 1 → Fin 1 → ℝ := fun _ _ => (1 / 2 : ℝ)
  let Tinv : Fin 1 → Fin 1 → ℝ := fun _ _ => 2
  have hzero_add_zero : (0 : ℝ) + 0 = 0 := by ring
  have hA_right : IsRightInverse 3 A Ainv := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, Ainv, Fin.sum_univ_three]
    all_goals first | exact hzero_add_zero | rfl
  have hA_left : IsLeftInverse 3 A Ainv := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, Ainv, Fin.sum_univ_three]
    all_goals first | exact hzero_add_zero | rfl
  have hG_right : IsRightInverse 2 G Ginv := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [G, Ginv, Fin.sum_univ_two]
    all_goals first | exact hzero_add_zero | rfl
  have hG_left : IsLeftInverse 2 G Ginv := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [G, Ginv, Fin.sum_univ_two]
    all_goals first | exact hzero_add_zero | rfl
  have hT_right : IsRightInverse 1 T Tinv := by
    intro i j
    fin_cases i
    fin_cases j
    norm_num [T, Tinv, Fin.sum_univ_one]
  have hT_left : IsLeftInverse 1 T Tinv := by
    intro i j
    fin_cases i
    fin_cases j
    norm_num [T, Tinv, Fin.sum_univ_one]
  have hG_tail : ∀ i j : Fin 2, G i j = A (Fin.succ i) (Fin.succ j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [A, G]
  have hT_suffix : ∀ i j : Fin 1, T i j = G (0 : Fin 2) (0 : Fin 2) := by
    intro i j
    fin_cases i
    fin_cases j
    norm_num [G, T]
  have hA00 : A (0 : Fin 3) (0 : Fin 3) = 1 := by
    norm_num [A]
  have hG00 : G (0 : Fin 2) (0 : Fin 2) = (1 / 2 : ℝ) := by
    norm_num [G]
  have hFinalPivot :
      G (1 : Fin 2) (1 : Fin 2) -
          G (1 : Fin 2) (0 : Fin 2) *
            (G (0 : Fin 2) (0 : Fin 2))⁻¹ *
            G (0 : Fin 2) (1 : Fin 2) = (-3 / 2 : ℝ) := by
    norm_num [G]
  have hAinv_norm :
      maxEntryNormRect (by norm_num : 0 < 3) (by norm_num : 0 < 3) Ainv =
        (4 / 3 : ℝ) := by
    apply le_antisymm
    · apply maxEntryNormRect_le_of_entry_abs_le
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num [Ainv]
    · have h :=
        entry_le_maxEntryNormRect (by norm_num : 0 < 3) (by norm_num : 0 < 3)
          Ainv (1 : Fin 3) (2 : Fin 3)
      have hentry : |Ainv (1 : Fin 3) (2 : Fin 3)| = (4 / 3 : ℝ) := by
        norm_num [Ainv]
      rw [hentry] at h
      exact h
  have hbad :
      ¬ (∀ i j : Fin 1,
          |Tinv i j| ≤
            maxEntryNormRect (by norm_num : 0 < 3) (by norm_num : 0 < 3)
              Ainv) := by
    intro hbound
    have h := hbound (0 : Fin 1) (0 : Fin 1)
    rw [hAinv_norm] at h
    norm_num [Tinv] at h
  exact ⟨A, Ainv, G, Ginv, T, Tinv, hA_right, hA_left, hG_right, hG_left,
    hT_right, hT_left, hG_tail, hT_suffix, hA00, hG00, hFinalPivot,
    hAinv_norm, hbad⟩

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 audit:
    the all-active-suffix inverse-entry table is not rescued merely by the
    initial column block-diagonal-dominance data used in the Theorem 13.8
    mixed route.

    The scalar matrix `[[1, -1], [1, 1]]`, packaged as `1 x 1` blocks, is
    column block diagonally dominant in the matrix-`∞` sense with diagonal
    max-entry lower comparison.  Its full inverse has max-entry norm `1/2`,
    while the canonical stage-zero active pivot block is `[1]`, whose inverse
    entry is `1`.  Hence a source proof of the all-tail table still needs a
    genuinely recursive tail/source comparison or an additional hypothesis;
    BDD-at-the-initial-table alone does not supply it. -/
theorem
    higham13_problem13_4_all_tail_inverse_entry_bound_counterexample_activeSuffix_infNorm_bdd :
    ∃ A Ainv : Fin 2 → Fin 2 → ℝ,
    ∃ Ablk : Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1) ℝ,
    ∃ pivotInv : ℕ → Matrix (Fin 1) (Fin 1) ℝ,
    ∃ invDiagBound : Fin 2 → ℝ,
    ∃ P Pinv : Fin 1 → Fin 1 → ℝ,
      IsRightInverse 2 A Ainv ∧ IsLeftInverse 2 A Ainv ∧
        IsRightInverse 1 P Pinv ∧ IsLeftInverse 1 P Pinv ∧
        IsBlockDiagDomCol 2 (fun i j : Fin 2 => infNorm (Ablk i j)) invDiagBound ∧
        IsBlockDiagDomCol 2
          (fun i j : Fin 2 => maxEntryNorm (by norm_num : 0 < 1) (Ablk i j))
          invDiagBound ∧
        (∀ j : Fin 2,
          invDiagBound j ≤ maxEntryNorm (by norm_num : 0 < 1) (Ablk j j)) ∧
        (∀ i j : Fin 2,
          blockMatrixFlatFin Ablk (finProdFinEquiv (i, (0 : Fin 1)))
            (finProdFinEquiv (j, (0 : Fin 1))) = A i j) ∧
        (∀ i j : Fin 1, P i j = A (0 : Fin 2) (0 : Fin 2)) ∧
        (∀ i j s t,
          higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv
              0 0 (by norm_num) i j s t = P s t) ∧
        maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) Ainv =
          (1 / 2 : ℝ) ∧
        ¬ (∀ i j : Fin 1,
          |Pinv i j| ≤
            maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) Ainv) := by
  let A : Fin 2 → Fin 2 → ℝ := fun i j =>
    if i = (0 : Fin 2) ∧ j = (0 : Fin 2) then 1
    else if i = (0 : Fin 2) ∧ j = (1 : Fin 2) then (-1)
    else if i = (1 : Fin 2) ∧ j = (0 : Fin 2) then 1
    else 1
  let Ainv : Fin 2 → Fin 2 → ℝ := fun i j =>
    if i = (0 : Fin 2) ∧ j = (0 : Fin 2) then (1 / 2 : ℝ)
    else if i = (0 : Fin 2) ∧ j = (1 : Fin 2) then (1 / 2 : ℝ)
    else if i = (1 : Fin 2) ∧ j = (0 : Fin 2) then (-1 / 2 : ℝ)
    else (1 / 2 : ℝ)
  let Ablk : Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1) ℝ := fun i j _ _ => A i j
  let pivotInv : ℕ → Matrix (Fin 1) (Fin 1) ℝ := fun _ _ _ => 0
  let invDiagBound : Fin 2 → ℝ := fun _ => 1
  let P : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
  let Pinv : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
  have hA_right : IsRightInverse 2 A Ainv := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, Ainv, Fin.sum_univ_two]
    all_goals rfl
  have hA_left : IsLeftInverse 2 A Ainv := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, Ainv, Fin.sum_univ_two]
    all_goals rfl
  have hP_right : IsRightInverse 1 P Pinv := by
    intro i j
    fin_cases i
    fin_cases j
    norm_num [P, Pinv, Fin.sum_univ_one]
  have hP_left : IsLeftInverse 1 P Pinv := by
    intro i j
    fin_cases i
    fin_cases j
    norm_num [P, Pinv, Fin.sum_univ_one]
  have hInfNorm_Ablk :
      ∀ i j : Fin 2, infNorm (Ablk i j) = |A i j| := by
    intro i j
    apply le_antisymm
    · apply infNorm_le_of_row_sum_le
      · intro s
        fin_cases s
        simp [Ablk]
      · exact abs_nonneg (A i j)
    · have h := row_sum_le_infNorm (Ablk i j) (0 : Fin 1)
      simpa [Ablk] using h
  have hMaxNorm_Ablk :
      ∀ i j : Fin 2, maxEntryNorm (by norm_num : 0 < 1) (Ablk i j) = |A i j| := by
    intro i j
    apply le_antisymm
    · apply
        (maxEntryNormRect_le_of_entry_abs_le
          (by norm_num : 0 < 1) (by norm_num : 0 < 1) (Ablk i j) |A i j|)
      intro s t
      fin_cases s
      fin_cases t
      simp [Ablk]
    · have h :=
        entry_le_maxEntryNorm (by norm_num : 0 < 1) (Ablk i j) (0 : Fin 1) (0 : Fin 1)
      simpa [Ablk] using h
  have hDomInf :
      IsBlockDiagDomCol 2 (fun i j : Fin 2 => infNorm (Ablk i j)) invDiagBound := by
    intro j
    fin_cases j <;>
      norm_num [IsBlockDiagDomCol, hInfNorm_Ablk, A, invDiagBound, Fin.sum_univ_two]
  have hDomMax :
      IsBlockDiagDomCol 2
        (fun i j : Fin 2 => maxEntryNorm (by norm_num : 0 < 1) (Ablk i j))
        invDiagBound := by
    exact higham13_blockDiagDomCol_maxEntry_of_infNorm
      (by norm_num : 0 < 1) Ablk invDiagBound hDomInf
  have hDiagMax :
      ∀ j : Fin 2,
        invDiagBound j ≤ maxEntryNorm (by norm_num : 0 < 1) (Ablk j j) := by
    intro j
    fin_cases j <;> norm_num [hMaxNorm_Ablk, A, invDiagBound]
  have hFlat :
      ∀ i j : Fin 2,
        blockMatrixFlatFin Ablk (finProdFinEquiv (i, (0 : Fin 1)))
          (finProdFinEquiv (j, (0 : Fin 1))) = A i j := by
    intro i j
    rw [blockMatrixFlatFin_apply]
  have hP_initial : ∀ i j : Fin 1, P i j = A (0 : Fin 2) (0 : Fin 2) := by
    intro i j
    fin_cases i
    fin_cases j
    norm_num [A, P]
  have hActive :
      ∀ i j s t,
        higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv
            0 0 (by norm_num) i j s t = P s t := by
    intro i j s t
    fin_cases i
    fin_cases j
    simpa [Ablk, higham13_algorithm13_3_activeSuffixStageTailBlock,
      higham13_algorithm13_3_activeSuffixTail,
      higham13_algorithm13_3_schurStageMatrixTailBlock,
      higham13_algorithm13_3_schurStageMatrixBlock,
      higham13_algorithm13_3_schurStageBlock] using (hP_initial s t).symm
  have hAinv_norm :
      maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) Ainv =
        (1 / 2 : ℝ) := by
    apply le_antisymm
    · apply maxEntryNormRect_le_of_entry_abs_le
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num [Ainv]
    · have h :=
        entry_le_maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2)
          Ainv (0 : Fin 2) (0 : Fin 2)
      simpa [Ainv] using h
  have hbad :
      ¬ (∀ i j : Fin 1,
          |Pinv i j| ≤
            maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) Ainv) := by
    intro hbound
    have h := hbound (0 : Fin 1) (0 : Fin 1)
    rw [hAinv_norm] at h
    norm_num [Pinv] at h
  exact ⟨A, Ainv, Ablk, pivotInv, invDiagBound, P, Pinv, hA_right, hA_left,
    hP_right, hP_left, hDomInf, hDomMax, hDiagMax, hFlat, hP_initial,
    hActive, hAinv_norm, hbad⟩

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 audit:
    the all-active-suffix inverse-entry table is not rescued by adding the
    all-leading-prefix nonsingularity table to the initial BDD data.

    This strengthens
    `higham13_problem13_4_all_tail_inverse_entry_bound_counterexample_activeSuffix_infNorm_bdd`:
    the same scalar-block witness satisfies the leading-prefix nonsingularity
    certificate used by the recursive BDD route, yet the stage-zero active
    pivot inverse entry is still larger than the final inverse max-entry norm.
    Hence a source proof still needs a recursive tail/source comparison or a
    different hidden hypothesis. -/
theorem
    higham13_problem13_4_all_tail_inverse_entry_bound_counterexample_activeSuffix_infNorm_bdd_leadingPrefixes :
    ∃ A Ainv : Fin 2 → Fin 2 → ℝ,
    ∃ Ablk : Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1) ℝ,
    ∃ pivotInv : ℕ → Matrix (Fin 1) (Fin 1) ℝ,
    ∃ invDiagBound : Fin 2 → ℝ,
    ∃ P Pinv : Fin 1 → Fin 1 → ℝ,
      IsRightInverse 2 A Ainv ∧ IsLeftInverse 2 A Ainv ∧
        IsRightInverse 1 P Pinv ∧ IsLeftInverse 1 P Pinv ∧
        IsBlockDiagDomCol 2 (fun i j : Fin 2 => infNorm (Ablk i j)) invDiagBound ∧
        IsBlockDiagDomCol 2
          (fun i j : Fin 2 => maxEntryNorm (by norm_num : 0 < 1) (Ablk i j))
          invDiagBound ∧
        (∀ j : Fin 2,
          invDiagBound j ≤ maxEntryNorm (by norm_num : 0 < 1) (Ablk j j)) ∧
        (∀ p : ℕ, ∀ hp : p < 2,
          BlockMatrixNonsingular
            (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp)) ∧
        (∀ i j : Fin 2,
          blockMatrixFlatFin Ablk (finProdFinEquiv (i, (0 : Fin 1)))
            (finProdFinEquiv (j, (0 : Fin 1))) = A i j) ∧
        (∀ i j : Fin 1, P i j = A (0 : Fin 2) (0 : Fin 2)) ∧
        (∀ i j s t,
          higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv
              0 0 (by norm_num) i j s t = P s t) ∧
        maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) Ainv =
          (1 / 2 : ℝ) ∧
        ¬ (∀ i j : Fin 1,
          |Pinv i j| ≤
            maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) Ainv) := by
  rcases
      higham13_problem13_4_all_tail_inverse_entry_bound_counterexample_activeSuffix_infNorm_bdd
    with
    ⟨A, Ainv, Ablk, pivotInv, invDiagBound, P, Pinv, hA_right, hA_left,
      hP_right, hP_left, hDomInf, hDomMax, hDiagMax, hFlat, hP_initial,
      hActive, hAinv_norm, hbad⟩
  have hAblk_entry :
      ∀ i j : Fin 2, Ablk i j (0 : Fin 1) (0 : Fin 1) = A i j := by
    intro i j
    calc
      Ablk i j (0 : Fin 1) (0 : Fin 1)
          = blockMatrixFlatFin Ablk (finProdFinEquiv (i, (0 : Fin 1)))
              (finProdFinEquiv (j, (0 : Fin 1))) := by
            exact (blockMatrixFlatFin_apply Ablk i j (0 : Fin 1) (0 : Fin 1)).symm
      _ = A i j := hFlat i j
  have hPrefix :
      ∀ p : ℕ, ∀ hp : p < 2,
        BlockMatrixNonsingular
          (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp) := by
    intro p hp
    cases p with
    | zero =>
        refine ⟨fun _ _ _ _ => Pinv (0 : Fin 1) (0 : Fin 1), ?_⟩
        constructor
        · intro i j s t
          fin_cases i
          fin_cases j
          fin_cases s
          fin_cases t
          have hA00 : Ablk (0 : Fin 2) (0 : Fin 2) (0 : Fin 1) (0 : Fin 1) =
              P (0 : Fin 1) (0 : Fin 1) := by
            rw [hAblk_entry]
            exact (hP_initial (0 : Fin 1) (0 : Fin 1)).symm
          simpa [BlockMatrixTwoSidedInverse, blockMatrixIdentity, idBlock,
            zeroBlock, leadingBlockPrefix13_2, Fin.sum_univ_one, hA00]
            using hP_left (0 : Fin 1) (0 : Fin 1)
        · intro i j s t
          fin_cases i
          fin_cases j
          fin_cases s
          fin_cases t
          have hA00 : Ablk (0 : Fin 2) (0 : Fin 2) (0 : Fin 1) (0 : Fin 1) =
              P (0 : Fin 1) (0 : Fin 1) := by
            rw [hAblk_entry]
            exact (hP_initial (0 : Fin 1) (0 : Fin 1)).symm
          simpa [BlockMatrixTwoSidedInverse, blockMatrixIdentity, idBlock,
            zeroBlock, leadingBlockPrefix13_2, Fin.sum_univ_one, hA00]
            using hP_right (0 : Fin 1) (0 : Fin 1)
    | succ p =>
        have hp0 : p = 0 := by omega
        subst p
        refine ⟨fun i j _ _ => Ainv i j, ?_⟩
        have hPrefixEntry :
            ∀ i j : Fin 2, ∀ s t : Fin 1,
              leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) (0 + 1) hp
                  i j s t = A i j := by
          intro i j s t
          fin_cases i <;> fin_cases j <;> fin_cases s <;> fin_cases t <;>
            simp [leadingBlockPrefix13_2, hAblk_entry]
        have hId :
            ∀ i j : Fin 2, ∀ s t : Fin 1,
              blockMatrixIdentity (0 + 1 + 1) 1 i j s t =
                if i = j then 1 else 0 := by
          intro i j s t
          fin_cases s
          fin_cases t
          by_cases hij : i = j
          · simp [blockMatrixIdentity, idBlock, hij]
          · simp [blockMatrixIdentity, zeroBlock, hij]
        constructor
        · intro i j s t
          calc
            (∑ k : Fin (0 + 1 + 1), ∑ l : Fin 1,
                (fun i j _ _ => Ainv i j) i k s l *
                  leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) (0 + 1) hp
                    k j l t)
                = ∑ k : Fin 2, Ainv i k * A k j := by
                    apply Finset.sum_congr rfl
                    intro k _hk
                    simp [hPrefixEntry]
            _ = if i = j then 1 else 0 := hA_left i j
            _ = blockMatrixIdentity (0 + 1 + 1) 1 i j s t := by
                  rw [hId]
        · intro i j s t
          calc
            (∑ k : Fin (0 + 1 + 1), ∑ l : Fin 1,
                leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) (0 + 1) hp
                    i k s l *
                  (fun i j _ _ => Ainv i j) k j l t)
                = ∑ k : Fin 2, A i k * Ainv k j := by
                    apply Finset.sum_congr rfl
                    intro k _hk
                    simp [hPrefixEntry]
            _ = if i = j then 1 else 0 := hA_right i j
            _ = blockMatrixIdentity (0 + 1 + 1) 1 i j s t := by
                  rw [hId]
  exact ⟨A, Ainv, Ablk, pivotInv, invDiagBound, P, Pinv, hA_right, hA_left,
    hP_right, hP_left, hDomInf, hDomMax, hDiagMax, hPrefix, hFlat,
    hP_initial, hActive, hAinv_norm, hbad⟩

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 audit:
    the all-active-suffix inverse-entry table is not rescued by strengthening
    the initial BDD hypothesis to both row and column dominance.

    The witness is again `[[1, -1], [1, 1]]` in scalar `1 x 1` blocks.  It
    satisfies matrix-`∞` and max-entry row/column BDD tables, the diagonal
    max-entry lower comparison, and the all-leading-prefix nonsingularity
    table.  Its stage-zero active pivot inverse entry is still larger than the
    final inverse max-entry norm, so the source route needs a recursive
    tail/source comparison or a genuinely stronger hidden hypothesis than
    two-sided initial BDD. -/
theorem
    higham13_problem13_4_all_tail_inverse_entry_bound_counterexample_activeSuffix_infNorm_rowCol_bdd_leadingPrefixes :
    ∃ A Ainv : Fin 2 → Fin 2 → ℝ,
    ∃ Ablk : Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1) ℝ,
    ∃ pivotInv : ℕ → Matrix (Fin 1) (Fin 1) ℝ,
    ∃ invDiagBound : Fin 2 → ℝ,
    ∃ P Pinv : Fin 1 → Fin 1 → ℝ,
      IsRightInverse 2 A Ainv ∧ IsLeftInverse 2 A Ainv ∧
        IsRightInverse 1 P Pinv ∧ IsLeftInverse 1 P Pinv ∧
        IsBlockDiagDomCol 2 (fun i j : Fin 2 => infNorm (Ablk i j)) invDiagBound ∧
        IsBlockDiagDomRow 2 (fun i j : Fin 2 => infNorm (Ablk i j)) invDiagBound ∧
        IsBlockDiagDomCol 2
          (fun i j : Fin 2 => maxEntryNorm (by norm_num : 0 < 1) (Ablk i j))
          invDiagBound ∧
        IsBlockDiagDomRow 2
          (fun i j : Fin 2 => maxEntryNorm (by norm_num : 0 < 1) (Ablk i j))
          invDiagBound ∧
        (∀ j : Fin 2,
          invDiagBound j ≤ maxEntryNorm (by norm_num : 0 < 1) (Ablk j j)) ∧
        (∀ p : ℕ, ∀ hp : p < 2,
          BlockMatrixNonsingular
            (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp)) ∧
        (∀ i j : Fin 2,
          blockMatrixFlatFin Ablk (finProdFinEquiv (i, (0 : Fin 1)))
            (finProdFinEquiv (j, (0 : Fin 1))) = A i j) ∧
        (∀ i j : Fin 1, P i j = A (0 : Fin 2) (0 : Fin 2)) ∧
        (∀ i j s t,
          higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv
              0 0 (by norm_num) i j s t = P s t) ∧
        maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) Ainv =
          (1 / 2 : ℝ) ∧
        ¬ (∀ i j : Fin 1,
          |Pinv i j| ≤
            maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) Ainv) := by
  let A : Fin 2 → Fin 2 → ℝ := fun i j =>
    if i = (0 : Fin 2) ∧ j = (0 : Fin 2) then 1
    else if i = (0 : Fin 2) ∧ j = (1 : Fin 2) then (-1)
    else if i = (1 : Fin 2) ∧ j = (0 : Fin 2) then 1
    else 1
  let Ainv : Fin 2 → Fin 2 → ℝ := fun i j =>
    if i = (0 : Fin 2) ∧ j = (0 : Fin 2) then (1 / 2 : ℝ)
    else if i = (0 : Fin 2) ∧ j = (1 : Fin 2) then (1 / 2 : ℝ)
    else if i = (1 : Fin 2) ∧ j = (0 : Fin 2) then (-1 / 2 : ℝ)
    else (1 / 2 : ℝ)
  let Ablk : Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1) ℝ := fun i j _ _ => A i j
  let pivotInv : ℕ → Matrix (Fin 1) (Fin 1) ℝ := fun _ _ _ => 0
  let invDiagBound : Fin 2 → ℝ := fun _ => 1
  let P : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
  let Pinv : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
  have hA_right : IsRightInverse 2 A Ainv := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, Ainv, Fin.sum_univ_two]
    all_goals rfl
  have hA_left : IsLeftInverse 2 A Ainv := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, Ainv, Fin.sum_univ_two]
    all_goals rfl
  have hP_right : IsRightInverse 1 P Pinv := by
    intro i j
    fin_cases i
    fin_cases j
    norm_num [P, Pinv, Fin.sum_univ_one]
  have hP_left : IsLeftInverse 1 P Pinv := by
    intro i j
    fin_cases i
    fin_cases j
    norm_num [P, Pinv, Fin.sum_univ_one]
  have hInfNorm_Ablk :
      ∀ i j : Fin 2, infNorm (Ablk i j) = |A i j| := by
    intro i j
    apply le_antisymm
    · apply infNorm_le_of_row_sum_le
      · intro s
        fin_cases s
        simp [Ablk]
      · exact abs_nonneg (A i j)
    · have h := row_sum_le_infNorm (Ablk i j) (0 : Fin 1)
      simpa [Ablk] using h
  have hMaxNorm_Ablk :
      ∀ i j : Fin 2, maxEntryNorm (by norm_num : 0 < 1) (Ablk i j) = |A i j| := by
    intro i j
    apply le_antisymm
    · apply
        (maxEntryNormRect_le_of_entry_abs_le
          (by norm_num : 0 < 1) (by norm_num : 0 < 1) (Ablk i j) |A i j|)
      intro s t
      fin_cases s
      fin_cases t
      simp [Ablk]
    · have h :=
        entry_le_maxEntryNorm (by norm_num : 0 < 1) (Ablk i j) (0 : Fin 1) (0 : Fin 1)
      simpa [Ablk] using h
  have hDomInfCol :
      IsBlockDiagDomCol 2 (fun i j : Fin 2 => infNorm (Ablk i j)) invDiagBound := by
    intro j
    fin_cases j <;>
      norm_num [IsBlockDiagDomCol, hInfNorm_Ablk, A, invDiagBound, Fin.sum_univ_two]
  have hDomInfRow :
      IsBlockDiagDomRow 2 (fun i j : Fin 2 => infNorm (Ablk i j)) invDiagBound := by
    intro i
    fin_cases i <;>
      norm_num [IsBlockDiagDomRow, hInfNorm_Ablk, A, invDiagBound, Fin.sum_univ_two]
  have hDomMaxCol :
      IsBlockDiagDomCol 2
        (fun i j : Fin 2 => maxEntryNorm (by norm_num : 0 < 1) (Ablk i j))
        invDiagBound := by
    exact higham13_blockDiagDomCol_maxEntry_of_infNorm
      (by norm_num : 0 < 1) Ablk invDiagBound hDomInfCol
  have hDomMaxRow :
      IsBlockDiagDomRow 2
        (fun i j : Fin 2 => maxEntryNorm (by norm_num : 0 < 1) (Ablk i j))
        invDiagBound := by
    intro i
    fin_cases i <;>
      norm_num [IsBlockDiagDomRow, hMaxNorm_Ablk, A, invDiagBound, Fin.sum_univ_two]
  have hDiagMax :
      ∀ j : Fin 2,
        invDiagBound j ≤ maxEntryNorm (by norm_num : 0 < 1) (Ablk j j) := by
    intro j
    fin_cases j <;> norm_num [hMaxNorm_Ablk, A, invDiagBound]
  have hFlat :
      ∀ i j : Fin 2,
        blockMatrixFlatFin Ablk (finProdFinEquiv (i, (0 : Fin 1)))
          (finProdFinEquiv (j, (0 : Fin 1))) = A i j := by
    intro i j
    rw [blockMatrixFlatFin_apply]
  have hP_initial : ∀ i j : Fin 1, P i j = A (0 : Fin 2) (0 : Fin 2) := by
    intro i j
    fin_cases i
    fin_cases j
    norm_num [A, P]
  have hActive :
      ∀ i j s t,
        higham13_algorithm13_3_activeSuffixStageTailBlock Ablk pivotInv
            0 0 (by norm_num) i j s t = P s t := by
    intro i j s t
    fin_cases i
    fin_cases j
    simpa [Ablk, higham13_algorithm13_3_activeSuffixStageTailBlock,
      higham13_algorithm13_3_activeSuffixTail,
      higham13_algorithm13_3_schurStageMatrixTailBlock,
      higham13_algorithm13_3_schurStageMatrixBlock,
      higham13_algorithm13_3_schurStageBlock] using (hP_initial s t).symm
  have hAinv_norm :
      maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) Ainv =
        (1 / 2 : ℝ) := by
    apply le_antisymm
    · apply maxEntryNormRect_le_of_entry_abs_le
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num [Ainv]
    · have h :=
        entry_le_maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2)
          Ainv (0 : Fin 2) (0 : Fin 2)
      simpa [Ainv] using h
  have hbad :
      ¬ (∀ i j : Fin 1,
          |Pinv i j| ≤
            maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) Ainv) := by
    intro hbound
    have h := hbound (0 : Fin 1) (0 : Fin 1)
    rw [hAinv_norm] at h
    norm_num [Pinv] at h
  have hAblk_entry :
      ∀ i j : Fin 2, Ablk i j (0 : Fin 1) (0 : Fin 1) = A i j := by
    intro i j
    simp [Ablk]
  have hPrefix :
      ∀ p : ℕ, ∀ hp : p < 2,
        BlockMatrixNonsingular
          (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp) := by
    intro p hp
    cases p with
    | zero =>
        refine ⟨fun _ _ _ _ => Pinv (0 : Fin 1) (0 : Fin 1), ?_⟩
        constructor
        · intro i j s t
          fin_cases i
          fin_cases j
          fin_cases s
          fin_cases t
          have hA00 : Ablk (0 : Fin 2) (0 : Fin 2) (0 : Fin 1) (0 : Fin 1) =
              P (0 : Fin 1) (0 : Fin 1) := by
            rw [hAblk_entry]
            exact (hP_initial (0 : Fin 1) (0 : Fin 1)).symm
          simpa [BlockMatrixTwoSidedInverse, blockMatrixIdentity, idBlock,
            zeroBlock, leadingBlockPrefix13_2, Fin.sum_univ_one, hA00]
            using hP_left (0 : Fin 1) (0 : Fin 1)
        · intro i j s t
          fin_cases i
          fin_cases j
          fin_cases s
          fin_cases t
          have hA00 : Ablk (0 : Fin 2) (0 : Fin 2) (0 : Fin 1) (0 : Fin 1) =
              P (0 : Fin 1) (0 : Fin 1) := by
            rw [hAblk_entry]
            exact (hP_initial (0 : Fin 1) (0 : Fin 1)).symm
          simpa [BlockMatrixTwoSidedInverse, blockMatrixIdentity, idBlock,
            zeroBlock, leadingBlockPrefix13_2, Fin.sum_univ_one, hA00]
            using hP_right (0 : Fin 1) (0 : Fin 1)
    | succ p =>
        have hp0 : p = 0 := by omega
        subst p
        refine ⟨fun i j _ _ => Ainv i j, ?_⟩
        have hPrefixEntry :
            ∀ i j : Fin 2, ∀ s t : Fin 1,
              leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) (0 + 1) hp
                  i j s t = A i j := by
          intro i j s t
          fin_cases i <;> fin_cases j <;> fin_cases s <;> fin_cases t <;>
            simp [leadingBlockPrefix13_2, hAblk_entry]
        have hId :
            ∀ i j : Fin 2, ∀ s t : Fin 1,
              blockMatrixIdentity (0 + 1 + 1) 1 i j s t =
                if i = j then 1 else 0 := by
          intro i j s t
          fin_cases s
          fin_cases t
          by_cases hij : i = j
          · simp [blockMatrixIdentity, idBlock, hij]
          · simp [blockMatrixIdentity, zeroBlock, hij]
        constructor
        · intro i j s t
          calc
            (∑ k : Fin (0 + 1 + 1), ∑ l : Fin 1,
                (fun i j _ _ => Ainv i j) i k s l *
                  leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) (0 + 1) hp
                    k j l t)
                = ∑ k : Fin 2, Ainv i k * A k j := by
                    apply Finset.sum_congr rfl
                    intro k _hk
                    simp [hPrefixEntry]
            _ = if i = j then 1 else 0 := hA_left i j
            _ = blockMatrixIdentity (0 + 1 + 1) 1 i j s t := by
                  rw [hId]
        · intro i j s t
          calc
            (∑ k : Fin (0 + 1 + 1), ∑ l : Fin 1,
                leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) (0 + 1) hp
                    i k s l *
                  (fun i j _ _ => Ainv i j) k j l t)
                = ∑ k : Fin 2, A i k * Ainv k j := by
                    apply Finset.sum_congr rfl
                    intro k _hk
                    simp [hPrefixEntry]
            _ = if i = j then 1 else 0 := hA_right i j
            _ = blockMatrixIdentity (0 + 1 + 1) 1 i j s t := by
                  rw [hId]
  exact ⟨A, Ainv, Ablk, pivotInv, invDiagBound, P, Pinv, hA_right, hA_left,
    hP_right, hP_left, hDomInfCol, hDomInfRow, hDomMaxCol, hDomMaxRow,
    hDiagMax, hPrefix, hFlat, hP_initial, hActive, hAinv_norm, hbad⟩

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 audit:
    the direct local-inverse comparison used by the stage-local growth route is
    not a scalar consequence of ambient growth containment alone.

    The values come from a valid scalar-pivot search instance: ambient base
    norm `5`, stage-history growth norm `20`, full inverse norm `19/40`, and
    local inverse norm `2`.  The growth object contains the base norm, but the
    cross-multiplied direct inverse comparison
    `||A_local^{-1}|| * ||A|| <= ||G|| * ||A^{-1}||` fails. -/
theorem higham13_stage_local_inverse_bound_scalar_counterexample :
    ∃ normA growthNorm fullInvNorm localInvNorm : ℝ,
      0 ≤ normA ∧ 0 ≤ growthNorm ∧ 0 ≤ fullInvNorm ∧ 0 ≤ localInvNorm ∧
        normA ≤ growthNorm ∧
          ¬ localInvNorm * normA ≤ growthNorm * fullInvNorm := by
  refine ⟨5, 20, 19 / 40, 2, ?_⟩
  norm_num

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 audit:
    ambient growth containment does not imply the direct local-inverse
    comparison exposed by
    `higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_inverse_bound_exact_kappa`.

    A source proof must therefore provide the local inverse estimate itself or
    replace it by a stronger condition/inverse-ratio argument; it cannot be
    generated from `||A|| <= ||G||` and nonnegativity alone. -/
theorem higham13_stage_local_inverse_bound_not_implied_by_growth_containment :
    ¬ (∀ normA growthNorm fullInvNorm localInvNorm : ℝ,
      0 ≤ normA → 0 ≤ growthNorm → 0 ≤ fullInvNorm → 0 ≤ localInvNorm →
        normA ≤ growthNorm →
          localInvNorm * normA ≤ growthNorm * fullInvNorm) := by
  intro h
  rcases higham13_stage_local_inverse_bound_scalar_counterexample with
    ⟨normA, growthNorm, fullInvNorm, localInvNorm,
      hNormA, hGrowth, hFullInv, hLocalInv, hContains, hbad⟩
  exact hbad
    (h normA growthNorm fullInvNorm localInvNorm
      hNormA hGrowth hFullInv hLocalInv hContains)

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23) audit:
    even with equal dimensions, `rhoTail <= rho` and the Problem 13.4-shaped
    condition comparison `kappaTail <= rho * kappa` do not imply the lower
    budget comparison `s * rhoTail^2 * kappaTail <= n * rho^2 * kappa`.

    The scalar values `n = s = 1`, `rho = rhoTail = 2`, `kappa = 1`, and
    `kappaTail = 2` satisfy the premises but fail the conclusion. -/
theorem higham13_stage_local_budget_from_problem13_4_scalar_counterexample :
    ∃ n s rho rhoTail kappa kappaTail : ℝ,
      0 ≤ n ∧ 0 ≤ s ∧ s ≤ n ∧ 1 ≤ rho ∧ 0 ≤ rhoTail ∧
        0 ≤ kappa ∧ 0 ≤ kappaTail ∧ rhoTail ≤ rho ∧
          kappaTail ≤ rho * kappa ∧
            ¬ s * rhoTail ^ 2 * kappaTail ≤ n * rho ^ 2 * kappa := by
  refine ⟨1, 1, 2, 2, 1, 2, ?_⟩
  norm_num

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23) audit:
    the recursive lower-budget comparison is not a scalar consequence of
    tail-growth domination plus the Problem 13.4-shaped Schur condition bound.
    A proof of the recursive transport must therefore supply a genuinely
    stronger source comparison or prove the lower budget directly. -/
theorem higham13_stage_local_budget_not_implied_by_problem13_4_bound :
    ¬ (∀ n s rho rhoTail kappa kappaTail : ℝ,
      0 ≤ n → 0 ≤ s → s ≤ n → 1 ≤ rho → 0 ≤ rhoTail →
        0 ≤ kappa → 0 ≤ kappaTail → rhoTail ≤ rho →
          kappaTail ≤ rho * kappa →
            s * rhoTail ^ 2 * kappaTail ≤ n * rho ^ 2 * kappa) := by
  intro h
  rcases higham13_stage_local_budget_from_problem13_4_scalar_counterexample with
    ⟨n, s, rho, rhoTail, kappa, kappaTail, hn, hs, hsn, hrho, hrhoTail,
      hkappa, hkappaTail, hTail, hCond, hbad⟩
  exact hbad
    (h n s rho rhoTail kappa kappaTail hn hs hsn hrho hrhoTail hkappa
      hkappaTail hTail hCond)

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    positive scalar bridge for the source-shaped recursive lower-block budget.

    The book's derivation uses one local growth factor together with
    Problem 13.4's Schur-complement condition comparison, then enlarges the
    result to the fixed full ambient `n * rho^2 * kappa` budget.  Compare
    `higham13_stage_local_budget_not_implied_by_problem13_4_bound`, which
    rejects the stronger exact-tail `rhoTail^2 * kappaTail` transport. -/
theorem higham13_stage_local_source_lblock_budget_le_of_problem13_4_bound
    {n s rho rhoTail kappa kappaTail : ℝ}
    (hs_nonneg : 0 ≤ s) (hsn : s ≤ n)
    (hrho_nonneg : 0 ≤ rho) (hrhoTail_nonneg : 0 ≤ rhoTail)
    (hkappa_nonneg : 0 ≤ kappa)
    (hTail : rhoTail ≤ rho)
    (hCond : kappaTail ≤ rho * kappa) :
    s * rhoTail * kappaTail ≤ n * rho ^ 2 * kappa := by
  have hn_nonneg : 0 ≤ n := le_trans hs_nonneg hsn
  have hsrho : s * rhoTail ≤ n * rho :=
    mul_le_mul hsn hTail hrhoTail_nonneg hn_nonneg
  have hleft :
      s * rhoTail * kappaTail ≤ s * rhoTail * (rho * kappa) :=
    mul_le_mul_of_nonneg_left hCond
      (mul_nonneg hs_nonneg hrhoTail_nonneg)
  have hright :
      s * rhoTail * (rho * kappa) ≤ n * rho * (rho * kappa) :=
    mul_le_mul_of_nonneg_right hsrho
      (mul_nonneg hrho_nonneg hkappa_nonneg)
  calc
    s * rhoTail * kappaTail ≤ s * rhoTail * (rho * kappa) := hleft
    _ ≤ n * rho * (rho * kappa) := hright
    _ = n * rho ^ 2 * kappa := by ring

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 feeding equations
    (13.22)--(13.23):
    scalar bridge for the stage-local inverse-bound route.

    If the one-growth-factor local numerator budget
    `rhoLocal * ||A_local|| <= rhoFull * ||A||` is already supplied by stage
    history containment, and the remaining source inverse comparison gives
    `||A_local^{-1}|| <= rhoFull * ||A^{-1}||`, then the local
    `rhoLocal * kappaLocal` budget is below the full
    `rhoFull^2 * kappaFull` budget. -/
theorem higham13_stage_local_source_lblock_budget_le_of_growth_inverse_bound
    {rhoLocal rhoFull normLocal normFull normInvLocal normInvFull : ℝ}
    (hGrowthBudget : rhoLocal * normLocal ≤ rhoFull * normFull)
    (hInvBudget : normInvLocal ≤ rhoFull * normInvFull)
    (hInvLocal_nonneg : 0 ≤ normInvLocal)
    (hGlobalGrowthBudget_nonneg : 0 ≤ rhoFull * normFull) :
    rhoLocal * (normLocal * normInvLocal) ≤
      rhoFull ^ 2 * (normFull * normInvFull) := by
  have hmul :
      (rhoLocal * normLocal) * normInvLocal ≤
        (rhoFull * normFull) * (rhoFull * normInvFull) :=
    mul_le_mul hGrowthBudget hInvBudget hInvLocal_nonneg
      hGlobalGrowthBudget_nonneg
  calc
    rhoLocal * (normLocal * normInvLocal)
        = (rhoLocal * normLocal) * normInvLocal := by ring
    _ ≤ (rhoFull * normFull) * (rhoFull * normInvFull) := hmul
    _ = rhoFull ^ 2 * (normFull * normInvFull) := by ring

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 feeding equations
    (13.22)--(13.23):
    scalar bridge for the source-strength local inverse-bound route.

    This is the cleaner version of
    `higham13_stage_local_source_lblock_budget_le_of_growth_inverse_bound`:
    once the stage history supplies
    `rhoLocal * ||A_local|| <= rhoFull * ||A||`, it is enough to prove the
    Schur-tail inverse comparison `||A_local^{-1}|| <= ||A^{-1}||`.  The extra
    factor of `rhoFull` needed by the ambient `rhoFull^2 kappa(A)` budget is
    obtained from the standard growth fact `1 <= rhoFull`. -/
theorem higham13_stage_local_source_lblock_budget_le_of_growth_plain_inverse_bound
    {rhoLocal rhoFull normLocal normFull normInvLocal normInvFull : ℝ}
    (hGrowthBudget : rhoLocal * normLocal ≤ rhoFull * normFull)
    (hInvBudget : normInvLocal ≤ normInvFull)
    (hInvLocal_nonneg : 0 ≤ normInvLocal)
    (hInvFull_nonneg : 0 ≤ normInvFull)
    (hGlobalGrowthBudget_nonneg : 0 ≤ rhoFull * normFull)
    (hrhoFull_ge_one : 1 ≤ rhoFull) :
    rhoLocal * (normLocal * normInvLocal) ≤
      rhoFull ^ 2 * (normFull * normInvFull) := by
  have hInvBudgetRho : normInvLocal ≤ rhoFull * normInvFull := by
    refine le_trans hInvBudget ?_
    calc
      normInvFull = 1 * normInvFull := by ring
      _ ≤ rhoFull * normInvFull :=
          mul_le_mul_of_nonneg_right hrhoFull_ge_one hInvFull_nonneg
  exact
    higham13_stage_local_source_lblock_budget_le_of_growth_inverse_bound
      hGrowthBudget hInvBudgetRho hInvLocal_nonneg hGlobalGrowthBudget_nonneg

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 feeding equations
    (13.22)--(13.23):
    matrix-stage multiplier bounds from canonical local growth and the
    source scalar comparison table.

    For each active pair `j < i`, the canonical local `2 x 2` growth object
    supplies the actual Problem 13.4 lower-block estimate.  This theorem then
    applies the book-shaped scalar comparisons
    `rhoLocal <= rhoFull` and `kappaLocal <= rhoFull * kappaFull` to produce
    the exact per-stage multiplier hypothesis required by the assembled
    Eq.13.22/Eq.13.23 product wrappers. -/
theorem higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_source_comparisons_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
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
  intro i j hji
  letI : Invertible
      (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j) :=
    hInvPivot i j hji
  letI : Invertible
      (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
        (hInvPivot i j hji)) :=
    hInvSchur i j hji
  letI : Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j) :=
    hInvFull i j hji
  let rhoLocal : ℝ :=
    growthFactorEntry (Nat.add_pos_left hr r)
      (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
      (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
      (hLocalApos i j hji)
  let kappaLocal : ℝ :=
    maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j) *
      maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
        (nonsingInv (r + r)
          (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j))
  have hLocal :
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal * kappaLocal := by
    simpa [rhoLocal, kappaLocal] using
      higham13_algorithm13_3_source_lblock_bound_from_stageLocalGrowth_le
        hr Ablk pivotInv i j hji rhoLocal kappaLocal
        (hPivotRight i j hji)
        (hLocalApos i j hji)
        (by simp [rhoLocal])
        (by simp [kappaLocal])
  have hrhoLocal_nonneg : 0 ≤ rhoLocal := by
    simpa [rhoLocal] using
      growthFactorEntry_nonneg (Nat.add_pos_left hr r)
        (higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j)
        (higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j)
        (hLocalApos i j hji)
  have hBudget :
      (r : ℝ) * rhoLocal * kappaLocal ≤
        (n : ℝ) * rhoFull ^ 2 * kappaFull :=
    higham13_stage_local_source_lblock_budget_le_of_problem13_4_bound
      (hs_nonneg := Nat.cast_nonneg r) (hsn := hrn)
      (hrho_nonneg := hrhoFull_nonneg)
      (hrhoTail_nonneg := hrhoLocal_nonneg)
      (hkappa_nonneg := hkappaFull_nonneg)
      (hTail := by simpa [hN, rhoFull, rhoLocal] using hRhoLocal_le i j hji)
      (hCond := by simpa [hN, rhoFull, kappaFull, kappaLocal] using hKappaLocal_le i j hji)
  exact le_trans hLocal (by simpa [hN, rhoFull, kappaFull] using hBudget)

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 feeding equations
    (13.22)--(13.23):
    matrix-stage multiplier bounds from canonical local growth, an explicit
    local/global denominator comparison, and the source condition comparison.

    This is the source-comparison route with the `rhoLocal <= rhoFull`
    premise discharged by
    `higham13_algorithm13_3_stageLocalGrowthFactor_le_matrixStageHistoryGrowthFactor_of_base_le`.
    The remaining local/base comparison is explicit because it is false as a
    generic stage-local fact. -/
theorem higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_base_comparisons_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
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
  exact
    higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_source_comparisons_exact_kappa
      hm hr Ablk pivotInv Ainv hApos n hNn hInvPivot hInvSchur hInvFull
      hPivotRight hLocalApos
      (fun i j hji =>
        higham13_algorithm13_3_stageLocalGrowthFactor_le_matrixStageHistoryGrowthFactor_of_base_le
          hm hr Ablk pivotInv i j hji hApos (hLocalApos i j hji)
          (hBaseLocal i j hji))
      hKappaLocal_le

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 feeding equations
    (13.22)--(13.23):
    matrix-stage multiplier bounds from canonical local growth and a
    local-inverse comparison.

    The already-proved stage-history theorem supplies
    `rhoLocal * ||A_local|| <= rhoFull * ||A||`.  Hence the per-stage
    multiplier budget follows from the remaining source comparison
    `||A_local^{-1}|| <= rhoFull * ||A^{-1}||`, without separately assuming
    the false-in-general denominator route `rhoLocal <= rhoFull`. -/
theorem higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_inverse_bound_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
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
  let A0 : Fin (m * r) → Fin (m * r) → ℝ := blockMatrixFlatFin Ablk
  let G : Fin (m * r) → Fin (m * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv
  let rhoFull : ℝ := growthFactorEntry hN A0 G hApos
  let normA : ℝ := maxEntryNormRect hN hN A0
  let normAinv : ℝ := maxEntryNormRect hN hN Ainv
  let kappaFull : ℝ := normA * normAinv
  have hr_le_mr_nat : r ≤ m * r := by
    nth_rewrite 1 [← Nat.one_mul r]
    exact Nat.mul_le_mul_right r (Nat.succ_le_of_lt hm)
  have hrn : (r : ℝ) ≤ (n : ℝ) := by
    exact le_trans (by exact_mod_cast hr_le_mr_nat) hNn
  have hrhoFull_nonneg : 0 ≤ rhoFull := by
    simpa [hN, A0, G, rhoFull] using
      growthFactorEntry_nonneg hN A0 G hApos
  have hkappaFull_nonneg : 0 ≤ kappaFull := by
    exact mul_nonneg (maxEntryNormRect_nonneg hN hN A0)
      (maxEntryNormRect_nonneg hN hN Ainv)
  intro i j hji
  let hLocalN : 0 < r + r := Nat.add_pos_left hr r
  let Aloc : Fin (r + r) → Fin (r + r) → ℝ :=
    higham13_algorithm13_3_stageLocalFlatMatrix Ablk pivotInv i j
  let Gloc : Fin (r + r) → Fin (r + r) → ℝ :=
    higham13_algorithm13_3_stageLocalGrowthMatrix hr Ablk pivotInv i j
  let AinvLoc : Fin (r + r) → Fin (r + r) → ℝ :=
    nonsingInv (r + r) Aloc
  let hLocalApos : 0 < maxEntryNorm hLocalN Aloc :=
    (higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table
      hr Ablk pivotInv hInvFull) i j hji
  let rhoLocal : ℝ := growthFactorEntry hLocalN Aloc Gloc hLocalApos
  let normLocal : ℝ := maxEntryNormRect hLocalN hLocalN Aloc
  let normInvLocal : ℝ := maxEntryNormRect hLocalN hLocalN AinvLoc
  let kappaLocal : ℝ := normLocal * normInvLocal
  letI : Invertible
      (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j) :=
    hInvPivot i j hji
  letI : Invertible
      (@higham13_algorithm13_3_stageLocalSchurOfInv m r Ablk pivotInv i j
        (hInvPivot i j hji)) :=
    hInvSchur i j hji
  letI : Invertible (higham13_algorithm13_3_stageLocalBlockMatrix Ablk pivotInv i j) :=
    hInvFull i j hji
  have hLocal :
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (r : ℝ) * rhoLocal * kappaLocal := by
    simpa [rhoLocal, kappaLocal, normLocal, normInvLocal, Aloc, AinvLoc,
      hLocalN, Gloc] using
      higham13_algorithm13_3_source_lblock_bound_from_stageLocalGrowth_le
        hr Ablk pivotInv i j hji rhoLocal kappaLocal
        (hPivotRight i j hji) hLocalApos
        (by simp [rhoLocal, Aloc, Gloc])
        (by simp [kappaLocal, normLocal, normInvLocal, Aloc, AinvLoc])
  have hGrowthBudget :
      rhoLocal * normLocal ≤ rhoFull * normA := by
    calc
      rhoLocal * normLocal
          = maxEntryNorm hLocalN Gloc := by
              simpa [rhoLocal, normLocal, Aloc, Gloc, hLocalN] using
                growthFactorEntry_mul_maxEntryNormRect_eq_maxEntryNorm
                  hLocalN Aloc Gloc hLocalApos
      _ ≤ maxEntryNorm hN G := by
              simpa [hN, G, Gloc, hLocalN] using
                higham13_algorithm13_3_stageLocalGrowthMatrix_le_matrixStageHistoryGrowthMatrix
                  hm hr Ablk pivotInv i j hji
      _ = rhoFull * normA := by
              simpa [hN, A0, G, rhoFull, normA] using
                (growthFactorEntry_mul_maxEntryNormRect_eq_maxEntryNorm
                  hN A0 G hApos).symm
  have hInvBudget : normInvLocal ≤ rhoFull * normAinv := by
    simpa [hN, A0, G, rhoFull, normAinv, hLocalN, Aloc, AinvLoc,
      normInvLocal] using hInvLocal_le i j hji
  have hGlobalGrowthBudget_nonneg : 0 ≤ rhoFull * normA := by
    exact mul_nonneg hrhoFull_nonneg (maxEntryNormRect_nonneg hN hN A0)
  have hInvLocal_nonneg : 0 ≤ normInvLocal := by
    exact maxEntryNormRect_nonneg hLocalN hLocalN AinvLoc
  have hLocalBudgetCore : rhoLocal * kappaLocal ≤ rhoFull ^ 2 * kappaFull := by
    simpa [kappaLocal, kappaFull, normLocal, normInvLocal, normA, normAinv] using
      higham13_stage_local_source_lblock_budget_le_of_growth_inverse_bound
        (rhoLocal := rhoLocal) (rhoFull := rhoFull)
        (normLocal := normLocal) (normFull := normA)
        (normInvLocal := normInvLocal) (normInvFull := normAinv)
        hGrowthBudget hInvBudget hInvLocal_nonneg hGlobalGrowthBudget_nonneg
  have hBudget_nonneg : 0 ≤ rhoFull ^ 2 * kappaFull :=
    mul_nonneg (sq_nonneg rhoFull) hkappaFull_nonneg
  have hScaled :
      (r : ℝ) * rhoLocal * kappaLocal ≤
        (n : ℝ) * rhoFull ^ 2 * kappaFull := by
    calc
      (r : ℝ) * rhoLocal * kappaLocal
          = (r : ℝ) * (rhoLocal * kappaLocal) := by ring
      _ ≤ (r : ℝ) * (rhoFull ^ 2 * kappaFull) :=
            mul_le_mul_of_nonneg_left hLocalBudgetCore (Nat.cast_nonneg r)
      _ ≤ (n : ℝ) * (rhoFull ^ 2 * kappaFull) :=
            mul_le_mul_of_nonneg_right hrn hBudget_nonneg
      _ = (n : ℝ) * rhoFull ^ 2 * kappaFull := by ring
  exact le_trans hLocal
    (by simpa [hN, A0, G, rhoFull, kappaFull, normA, normAinv] using hScaled)

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 feeding equations
    (13.22)--(13.23):
    matrix-stage multiplier bounds from canonical local growth and a plain
    local-inverse comparison.

    Compared with
    `higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_inverse_bound_exact_kappa`,
    this theorem asks only for
    `||A_local^{-1}||_max <= ||A^{-1}||_max`.  The missing multiplier
    `rhoFull` is derived internally from the fact that the Algorithm 13.3
    history growth matrix contains the initial matrix, hence `rhoFull >= 1`. -/
theorem higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_plain_inverse_bound_exact_kappa
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ainv : Fin (m * r) → Fin (m * r) → ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
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
  let G : Fin (m * r) → Fin (m * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv
  have hA_le_G : maxEntryNorm hN (blockMatrixFlatFin Ablk) ≤ maxEntryNorm hN G := by
    simpa [hN, G] using
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_flat_initial
        hm hr Ablk pivotInv
  have hrhoFull_ge_one :
      1 ≤ growthFactorEntry hN (blockMatrixFlatFin Ablk) G hApos := by
    exact
      growthFactorEntry_ge_one_of_maxEntryNorm_le hN (blockMatrixFlatFin Ablk)
        G hApos hA_le_G
  have hAinv_nonneg : 0 ≤ maxEntryNormRect hN hN Ainv :=
    maxEntryNormRect_nonneg hN hN Ainv
  have hAinv_le_rho :
      maxEntryNormRect hN hN Ainv ≤
        growthFactorEntry hN (blockMatrixFlatFin Ablk) G hApos *
          maxEntryNormRect hN hN Ainv := by
    calc
      maxEntryNormRect hN hN Ainv = 1 * maxEntryNormRect hN hN Ainv := by ring
      _ ≤ growthFactorEntry hN (blockMatrixFlatFin Ablk) G hApos *
            maxEntryNormRect hN hN Ainv :=
          mul_le_mul_of_nonneg_right hrhoFull_ge_one hAinv_nonneg
  exact
    higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_inverse_bound_exact_kappa
      hm hr Ablk pivotInv Ainv hApos n hNn hInvPivot hInvSchur hInvFull
      hPivotRight
      (fun i j hji => by
        exact le_trans (hInvLocal_le i j hji) (by simpa [hN, G] using hAinv_le_rho))

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 audit:
    the base comparison required by the stronger base/inverse recursive
    tail-transport route is not automatic from a principal-tail right-inverse
    relation.

    The existing diagonal `diag(100,1,1)` principal-tail witness already
    satisfies the full and tail right-inverse certificates and the tail inverse
    comparison.  If `||A_full||_max <= ||A_tail||_max` also held, then
    `maxEntryNormRect_inverse_ratio_of_base_le_and_inverse_le` would give the
    inverse-ratio comparison rejected by
    `higham13_inverse_ratio_principal_tail_counterexample`. -/
theorem higham13_base_inverse_principal_tail_base_comparison_counterexample :
    ∃ A Ainv : Fin 3 → Fin 3 → ℝ,
    ∃ S Sinv : Fin 2 → Fin 2 → ℝ,
      IsRightInverse 3 A Ainv ∧ IsRightInverse 2 S Sinv ∧
        (∀ i j : Fin 2, S i j = A (Fin.succ i) (Fin.succ j)) ∧
        (∀ i j : Fin 2, Sinv i j = Ainv (Fin.succ i) (Fin.succ j)) ∧
        maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) Sinv ≤
          maxEntryNormRect (by norm_num : 0 < 3) (by norm_num : 0 < 3) Ainv ∧
        ¬ maxEntryNormRect (by norm_num : 0 < 3) (by norm_num : 0 < 3) A ≤
          maxEntryNormRect (by norm_num : 0 < 2) (by norm_num : 0 < 2) S := by
  rcases higham13_inverse_ratio_principal_tail_counterexample with
    ⟨A, Ainv, S, Sinv, hA, hS, hStail, hSinvtail, _hSle, hInvle, hbad⟩
  refine ⟨A, Ainv, S, Sinv, hA, hS, hStail, hSinvtail, hInvle, ?_⟩
  intro hBase
  exact hbad
    (maxEntryNormRect_inverse_ratio_of_base_le_and_inverse_le
      (by norm_num : 0 < 2) (by norm_num : 0 < 3) S Sinv A Ainv hBase hInvle)

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    lower-budget comparison for the recursive Schur tail from the remaining
    inverse-ratio condition.

    The tail-history comparison supplies the growth-object domination.  The
    only mathematical hypothesis left exposed here is the cross-multiplied
    inverse-ratio comparison between the tail Schur complement and the full
    first-split source matrix. -/
theorem
    higham13_eq13_22_tail_lower_budget_le_full_from_inverse_ratio_matrix_stage_history_exact_kappa
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
    (maxEntryNormRect hNTail hNTail AinvTail *
          maxEntryNormRect hNFull hNFull A0 ≤
        maxEntryNormRect hNFull hNFull AinvFull *
          maxEntryNormRect hNTail hNTail Atail) →
      (n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail) ≤
        (n : ℝ) * (growthFactorEntry hNFull A0 Gfull hFullPos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull) := by
  dsimp only
  intro hInvRatio
  have hCore :
      (growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr)
            (blockMatrixFlatFin (blockSchur A (pivotInv 0)))
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr
              (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)))
            hTailPos) ^ 2 *
          (maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
              (Nat.mul_pos (Nat.succ_pos m) hr)
              (blockMatrixFlatFin (blockSchur A (pivotInv 0))) *
            maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
              (Nat.mul_pos (Nat.succ_pos m) hr)
              (nonsingInv ((m + 1) * r)
                (blockMatrixFlatFin (blockSchur A (pivotInv 0))))) ≤
        (growthFactorEntry (Nat.add_pos_left hr ((m + 1) * r))
            (blockMatrixFirstSplitFlat A)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.add_pos_left hr ((m + 1) * r))
              (Nat.succ_pos (m + 1)) hr A pivotInv)
            hFullPos) ^ 2 *
          (maxEntryNormRect (Nat.add_pos_left hr ((m + 1) * r))
              (Nat.add_pos_left hr ((m + 1) * r))
              (blockMatrixFirstSplitFlat A) *
            maxEntryNormRect (Nat.add_pos_left hr ((m + 1) * r))
              (Nat.add_pos_left hr ((m + 1) * r))
              (nonsingInv (r + (m + 1) * r)
                (blockMatrixFirstSplitFlat A))) := by
    exact
      growthFactorEntry_sq_kappa_budget_le_of_growth_le_inv_ratio
        (Nat.mul_pos (Nat.succ_pos m) hr)
        (Nat.add_pos_left hr ((m + 1) * r))
        (blockMatrixFlatFin (blockSchur A (pivotInv 0)))
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)))
        (nonsingInv ((m + 1) * r)
          (blockMatrixFlatFin (blockSchur A (pivotInv 0))))
        (blockMatrixFirstSplitFlat A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.add_pos_left hr ((m + 1) * r))
          (Nat.succ_pos (m + 1)) hr A pivotInv)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat A))
        hTailPos hFullPos
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_tail_le
          (Nat.mul_pos (Nat.succ_pos m) hr)
          (Nat.add_pos_left hr ((m + 1) * r))
          (Nat.succ_pos m) hr A pivotInv)
        hInvRatio
  simpa [mul_assoc] using
    mul_le_mul_of_nonneg_left hCore (Nat.cast_nonneg n)

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    lower-budget comparison for the recursive Schur tail from explicit
    base/inverse comparisons.

    This is a conditional dependency for the Problem 13.4 tail route.  It
    derives the cross-multiplied inverse-ratio comparison from the stronger
    pair `||A_full||_max <= ||A_tail||_max` and
    `||A_tail^{-1}||_max <= ||A_full^{-1}||_max`, then reuses the existing
    inverse-ratio transport theorem. -/
theorem
    higham13_eq13_22_tail_lower_budget_le_full_from_base_inverse_matrix_stage_history_exact_kappa
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
    (maxEntryNormRect hNFull hNFull A0 ≤
        maxEntryNormRect hNTail hNTail Atail) →
      (maxEntryNormRect hNTail hNTail AinvTail ≤
        maxEntryNormRect hNFull hNFull AinvFull) →
      (n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
          (maxEntryNormRect hNTail hNTail Atail *
            maxEntryNormRect hNTail hNTail AinvTail) ≤
        (n : ℝ) * (growthFactorEntry hNFull A0 Gfull hFullPos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull) := by
  dsimp only
  intro hBase hInv
  exact
    higham13_eq13_22_tail_lower_budget_le_full_from_inverse_ratio_matrix_stage_history_exact_kappa
      hr A pivotInv hTailPos hFullPos n
      (maxEntryNormRect_inverse_ratio_of_base_le_and_inverse_le
        (Nat.mul_pos (Nat.succ_pos m) hr)
        (Nat.add_pos_left hr ((m + 1) * r))
        (blockMatrixFlatFin (blockSchur A (pivotInv 0)))
        (nonsingInv ((m + 1) * r)
          (blockMatrixFlatFin (blockSchur A (pivotInv 0))))
        (blockMatrixFirstSplitFlat A)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat A))
        hBase hInv)

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    transport a recursive Schur-tail chain to the full ambient budgets from
    the explicit inverse-ratio condition.

    This composes the lower-budget inverse-ratio adapter with the monotonicity
    transport theorem.  A downstream recursive proof therefore supplies a local
    tail chain and the source inverse-ratio comparison, while the upper-growth
    comparison is discharged automatically by the matrix-stage history. -/
theorem
    higham13_eq13_22_tail_chain_to_full_budget_from_inverse_ratio_matrix_stage_history_exact_kappa
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
        m (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hNFull A0 Gfull hFullPos) ^ 2 *
          (maxEntryNormRect hNFull hNFull A0 *
            maxEntryNormRect hNFull hNFull AinvFull))
        (growthFactorEntry hNFull A0 Gfull hFullPos *
          maxEntryNormRect hNFull hNFull A0)
        m (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) := by
  dsimp only
  intro hInvRatio hTail
  have hLower :=
    higham13_eq13_22_tail_lower_budget_le_full_from_inverse_ratio_matrix_stage_history_exact_kappa
      hr A pivotInv hTailPos hFullPos n hInvRatio
  exact
    higham13_eq13_22_tail_chain_to_full_budget_from_lower_comparison_matrix_stage_history_exact_kappa
      hr A pivotInv hTailPos hFullPos n hLower hTail

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    transport a recursive Schur-tail chain to the full ambient budgets from
    explicit base/inverse comparisons.

    This is the chain-level companion to
    `higham13_eq13_22_tail_lower_budget_le_full_from_base_inverse_matrix_stage_history_exact_kappa`.
    It keeps the strong base comparison and inverse comparison as hypotheses,
    because they are not generic consequences of the recursive matrix-stage
    history alone. -/
theorem
    higham13_eq13_22_tail_chain_to_full_budget_from_base_inverse_matrix_stage_history_exact_kappa
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
    (maxEntryNormRect hNFull hNFull A0 ≤
        maxEntryNormRect hNTail hNTail Atail) →
      (maxEntryNormRect hNTail hNTail AinvTail ≤
        maxEntryNormRect hNFull hNFull AinvFull) →
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
  intro hBase hInv hTail
  exact
    higham13_eq13_22_tail_chain_to_full_budget_from_inverse_ratio_matrix_stage_history_exact_kappa
      hr A pivotInv hTailPos hFullPos n
      (maxEntryNormRect_inverse_ratio_of_base_le_and_inverse_le
        (Nat.mul_pos (Nat.succ_pos m) hr)
        (Nat.add_pos_left hr ((m + 1) * r))
        (blockMatrixFlatFin (blockSchur A (pivotInv 0)))
        (nonsingInv ((m + 1) * r)
          (blockMatrixFlatFin (blockSchur A (pivotInv 0))))
        (blockMatrixFirstSplitFlat A)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat A))
        hBase hInv)
      hTail

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 / Problem 13.4:
    one active matrix-stage multiplier bound from a local two-block budget.

    This is the Algorithm 13.3 specialization of
    `higham13_problem13_4_single_block_multiplier_bound_from_local_growth_budget`.
    For an active lower entry `j < i`, the multiplier
    `Aᵢⱼ^(j) * pivotInv_j` is bounded once the local two-block partition using
    stage blocks `(j,j)`, `(j,i)`, `(i,j)`, `(i,i)` has the stated
    Problem 13.4 growth/condition budget. -/
theorem higham13_algorithm13_3_stage_multiplier_bound_from_local_growth_budget
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (i j : Fin m) (_hji : j.val < i.val)
    (U : Fin (r + r) → Fin (r + r) → ℝ)
    [Invertible (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)]
    [Invertible
      (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i i -
        higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
          ⅟(higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j) *
          higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j i)]
    [Invertible
      (Matrix.fromBlocks
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j i)
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j)
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i i))]
    (hpivot :
      pivotInv j.val =
        ⅟(higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j))
    (hApos :
      0 < maxEntryNorm (Nat.add_pos_left hr r)
        (fun p q : Fin (r + r) =>
          (Matrix.fromBlocks
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j i)
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j)
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i i))
            (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)))
    (n : ℕ) (hrn : (r : ℝ) ≤ (n : ℝ))
    (hA_le_U :
      maxEntryNorm (Nat.add_pos_left hr r)
          (fun p q : Fin (r + r) =>
            (Matrix.fromBlocks
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j i)
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j)
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i i))
              (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)) ≤
        maxEntryNorm (Nat.add_pos_left hr r) U)
    (hS_le_U :
      maxEntryNormRect hr hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i i -
            higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
              ⅟(higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j) *
              higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j i) ≤
        maxEntryNorm (Nat.add_pos_left hr r) U)
    {C : ℝ}
    (hBudget :
      (growthFactorEntry (Nat.add_pos_left hr r)
          (fun p q : Fin (r + r) =>
            (Matrix.fromBlocks
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j i)
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j)
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i i))
              (finSumFinEquiv.symm p) (finSumFinEquiv.symm q))
          U hApos) ^ 2 *
        (maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (fun p q : Fin (r + r) =>
              (Matrix.fromBlocks
                (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
                (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j i)
                (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j)
                (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i i))
                (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)) *
          maxEntryNormRect (Nat.add_pos_left hr r) (Nat.add_pos_left hr r)
            (nonsingInv (r + r)
              (fun p q : Fin (r + r) =>
                (Matrix.fromBlocks
                  (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
                  (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j i)
                  (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j)
                  (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i i))
                  (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)))) ≤ C) :
    maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
          pivotInv j.val) ≤
      (n : ℝ) * C := by
  simpa [hpivot] using
    higham13_problem13_4_single_block_multiplier_bound_from_local_growth_budget
      hr
      (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j j)
      (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val j i)
      (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j)
      (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i i)
      (pivotInv j.val) U hpivot hApos n hrn hA_le_U hS_le_U hBudget

end NumStability
