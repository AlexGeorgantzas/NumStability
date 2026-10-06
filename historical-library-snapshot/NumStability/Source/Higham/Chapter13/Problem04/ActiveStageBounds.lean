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
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStages
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis
import NumStability.Source.Higham.Chapter13.Theorem02.Factorization
import NumStability.Source.Higham.Chapter13.Theorem07.PivotExistence

/-!
# Source.Higham.Chapter13.Problem04.ActiveStageBounds

This module formalizes the source-facing Chapter 13 statements for
`Problem04.ActiveStageBounds`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


theorem higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_flat_initial
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A) ≤
      maxEntryNorm (Nat.mul_pos hm hr)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr A pivotInv) := by
  rw [maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm]
  exact
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
      (Nat.mul_pos hm hr) hm hr A pivotInv

noncomputable def higham13_algorithm13_3_schurStageMatrixTailBlock
    {m r b : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (k : ℕ) (tail : Fin b → Fin m) :
    Fin b → Fin b → Matrix (Fin r) (Fin r) ℝ :=
  fun i j => higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k (tail i) (tail j)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    canonical active suffix of block indices at Schur stage `k`.

    For a suffix of length `b`, this maps local tail index `i` to the ambient
    block index `k + i`.  It is the source-shaped tail list used by the
    all-stage Problem 13.4 Eq.13.22/Eq.13.23 route. -/
noncomputable def higham13_algorithm13_3_activeSuffixTail
    (M k b : ℕ) (hkb : k + b ≤ M) : Fin b → Fin M :=
  fun i => ⟨k + i.val, by
    have hi : i.val < b := i.isLt
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi k) hkb⟩

@[simp] theorem higham13_algorithm13_3_activeSuffixTail_val
    {M k b : ℕ} (hkb : k + b ≤ M) (i : Fin b) :
    (higham13_algorithm13_3_activeSuffixTail M k b hkb i).val =
      k + i.val := rfl

theorem higham13_algorithm13_3_activeSuffixTail_zero
    {M k b : ℕ} (hkb : k + (b + 1) ≤ M) (hkM : k < M) :
    higham13_algorithm13_3_activeSuffixTail M k (b + 1) hkb 0 =
      ⟨k, hkM⟩ := by
  ext
  simp [higham13_algorithm13_3_activeSuffixTail]

theorem higham13_algorithm13_3_activeSuffixTail_succ
    {M k b : ℕ} (hkb : k + ((b + 1) + 1) ≤ M)
    (hkb_tail : k + 1 + (b + 1) ≤ M) (i : Fin (b + 1)) :
    higham13_algorithm13_3_activeSuffixTail M k ((b + 1) + 1) hkb (Fin.succ i) =
      higham13_algorithm13_3_activeSuffixTail M (k + 1) (b + 1) hkb_tail i := by
  ext
  simp [higham13_algorithm13_3_activeSuffixTail, Nat.add_comm, Nat.add_left_comm]

theorem higham13_algorithm13_3_activeSuffixTail_active
    {M k b : ℕ} (hkb_tail : k + 1 + (b + 1) ≤ M)
    (i : Fin (b + 1)) :
    k + 1 ≤
      (higham13_algorithm13_3_activeSuffixTail M (k + 1) (b + 1)
        hkb_tail i).val := by
  simp [higham13_algorithm13_3_activeSuffixTail]

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    recorded Schur-stage matrix restricted to the canonical active suffix. -/
noncomputable abbrev higham13_algorithm13_3_activeSuffixStageTailBlock
    {M r : ℕ}
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (k m : ℕ) (hkm : k + (m + 1) ≤ M) :
    Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ :=
  higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k
    (higham13_algorithm13_3_activeSuffixTail M k (m + 1) hkm)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    at stage zero, the canonical active suffix is the whole input matrix. -/
theorem higham13_algorithm13_3_activeSuffixStageTailBlock_zero_eq
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (h0m : 0 + (m + 1) ≤ m + 1) :
    higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv 0 m h0m = A := by
  ext i j s t
  simp [higham13_algorithm13_3_activeSuffixStageTailBlock,
    higham13_algorithm13_3_activeSuffixTail,
    higham13_algorithm13_3_schurStageMatrixTailBlock,
    higham13_algorithm13_3_schurStageMatrixBlock,
    higham13_algorithm13_3_schurStageBlock]

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    at stage one, the canonical active suffix is the first Schur complement. -/
theorem higham13_algorithm13_3_activeSuffixStageTailBlock_one_eq_blockSchur
    {m r : ℕ}
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (A11_inv : Matrix (Fin r) (Fin r) ℝ)
    (h1m : 1 + (m + 1) ≤ (m + 1) + 1)
    (hpivot : pivotInv 0 = A11_inv) :
    higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv 1 m h1m =
      blockSchur A A11_inv := by
  have htail :
      higham13_algorithm13_3_activeSuffixTail ((m + 1) + 1) 1 (m + 1) h1m =
        Fin.succ := by
    funext i
    ext
    simp [higham13_algorithm13_3_activeSuffixTail, Nat.add_comm]
  rw [← higham13_algorithm13_3_schurStageMatrixBlock_one_tail_eq_blockSchur
    A pivotInv A11_inv hpivot]
  ext i j s t
  simp [higham13_algorithm13_3_activeSuffixStageTailBlock,
    higham13_algorithm13_3_schurStageMatrixTailBlock, htail]

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    active recorded tails commute with one local Schur step.

    If `tailFull` records an active trailing block list at stage `k`, begins
    with the active pivot index `k`, and `tailSucc` is its successor tail, then
    taking the first local Schur complement of the recorded stage-`k` tail is
    exactly the recorded stage-`k+1` tail.  This is the all-tail version of the
    first-split identity used in the Problem 13.4 global-tableau route. -/
theorem higham13_algorithm13_3_schurStageMatrixTailBlock_succ_active_eq_blockSchur
    {M r b k : ℕ}
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hkM : k < M)
    (tailFull : Fin (b + 1) → Fin M)
    (tailSucc : Fin b → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin b, tailFull (Fin.succ i) = tailSucc i)
    (hactive : ∀ i : Fin b, k + 1 ≤ (tailSucc i).val) :
    blockSchur
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)
        (pivotInv k) =
      higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc := by
  ext i j s t
  have hupdate :=
    (higham13_algorithm13_3_schurStageBlock_exact_update A pivotInv)
      k hkM (tailSucc i) (tailSucc j) (hactive i) (hactive j)
  have hupdate' :
      higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1)
          (tailSucc i) (tailSucc j) =
        higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
            (tailSucc i) (tailSucc j) -
          higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
              (tailSucc i) ⟨k, hkM⟩ * pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
              ⟨k, hkM⟩ (tailSucc j) := by
    simpa [higham13_algorithm13_3_schurStageMatrixBlock] using hupdate
  simp [blockSchur, higham13_algorithm13_3_schurStageMatrixTailBlock,
    h0, hsucc, hupdate', Matrix.mul_apply, Finset.mul_sum, mul_assoc]

theorem higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_flat_stage_tail
    {N m r b : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r) (hb : 0 < b)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (k : ℕ) (hk : k ≤ m)
    (tail : Fin b → Fin m) :
    maxEntryNorm (Nat.mul_pos hb hr)
        (blockMatrixFlatFin
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tail)) ≤
      maxEntryNorm hN
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr A pivotInv) := by
  rw [maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm hb hr]
  exact le_trans
    (blockMaxNorm_le_of_entry_abs_le hb hr
      (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tail)
      (blockMaxNorm hm hr
        (fun p q => higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k p q))
      (by
        intro i j s t
        exact
          block_entry_abs_le_blockMaxNorm hm hr
            (fun p q => higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k p q)
            (tail i) (tail j) s t))
    (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_stage
      hN hm hr A pivotInv k hk)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    the exact matrix-product Schur update gives the active local Schur
    max-entry estimate once the true matrix triple product has the corresponding
    max-entry product bound.

    The product-bound hypothesis is deliberately explicit.  It is the precise
    replacement for the unavailable `SeminormedRing` norm-submultiplicativity
    step in the source max-entry norm for true matrix multiplication. -/
theorem higham13_algorithm13_3_matrix_active_local_schur_bound_of_product_bound
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hProduct : ∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j)) :
    SchurStageActiveLocalSchurBound13_8
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (fun k => maxEntryNorm hr (pivotInv k)) := by
  intro k hk i j hik hjk
  let p : Fin m := ⟨k, hk⟩
  have hUpdate :=
    (higham13_algorithm13_3_schurStageBlock_exact_update A pivotInv)
      k hk i j hik hjk
  have hUpdateM :
      higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1) i j =
        higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j -
          higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i p *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k p j := by
    simpa [higham13_algorithm13_3_schurStageMatrixBlock, p] using hUpdate
  have hsub :
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1) i j) ≤
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) +
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i p *
          pivotInv k *
          higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k p j) := by
    rw [hUpdateM]
    exact maxEntryNorm_sub_le hr
      (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j)
      (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i p *
        pivotInv k *
        higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k p j)
  have hp := hProduct k hk i j hik hjk
  dsimp [p] at hp ⊢
  nlinarith

/-- Audit for the Chapter 13 max-entry route: the product-bound hypothesis in
    `higham13_algorithm13_3_matrix_active_local_schur_bound_of_product_bound`
    is not a generic consequence of the Algorithm 13.3 stage-table shape.

    At the initial stage of a `2 × 2` block table whose blocks and pivot
    inverse are all the all-ones `2 × 2` matrix, the required active
    triple-product max-entry estimate would assert `4 <= 1`.  Any source
    closure of the product-bound route therefore has to use additional
    structure, not ordinary max-entry submultiplicativity. -/
theorem higham13_algorithm13_3_product_bound_not_generic :
    ¬ (∀ (A : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℝ)
        (pivotInv : ℕ → Matrix (Fin 2) (Fin 2) ℝ),
      ∀ k : ℕ, ∀ hk : k < 2, ∀ i j : Fin 2,
        k + 1 ≤ i.val → k + 1 ≤ j.val →
          maxEntryNorm (by norm_num : 0 < 2)
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
              pivotInv k *
              higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
            maxEntryNorm (by norm_num : 0 < 2)
              (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
            maxEntryNorm (by norm_num : 0 < 2) (pivotInv k) *
            maxEntryNorm (by norm_num : 0 < 2)
              (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j)) := by
  intro h
  let J : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1
  let A : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => J
  let pivotInv : ℕ → Matrix (Fin 2) (Fin 2) ℝ := fun _ => J
  have hineq :=
    h A pivotInv 0 (by norm_num) ⟨1, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num) (by norm_num)
  norm_num [A, pivotInv, J, maxEntryNorm,
    higham13_algorithm13_3_schurStageMatrixBlock,
    higham13_algorithm13_3_schurStageBlock, Matrix.mul_apply,
    Fin.sum_univ_two] at hineq

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    exact matrix-product local Schur estimate in the Chapter 13 max-entry
    norm, with the finite-dimensional `r^2` factor made explicit.

    This is the honest matrix-product replacement for the generic
    normed-ring local Schur estimate: entrywise max norm is not
    dimension-free submultiplicative for matrix multiplication, so the pivot
    norm carried by the active-stage interface is inflated by `(r : ℝ)^2`. -/
theorem higham13_algorithm13_3_matrix_active_local_schur_bound_with_dim_factor
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    SchurStageActiveLocalSchurBound13_8
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (fun k => (r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k)) := by
  intro k hk i j hik hjk
  let p : Fin m := ⟨k, hk⟩
  have hUpdate :=
    (higham13_algorithm13_3_schurStageBlock_exact_update A pivotInv)
      k hk i j hik hjk
  have hUpdateM :
      higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1) i j =
        higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j -
          higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i p *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k p j := by
    simpa [higham13_algorithm13_3_schurStageMatrixBlock, p] using hUpdate
  have hsub :
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1) i j) ≤
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) +
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i p *
          pivotInv k *
          higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k p j) := by
    rw [hUpdateM]
    exact maxEntryNorm_sub_le hr
      (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j)
      (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i p *
        pivotInv k *
        higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k p j)
  have hprod :
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i p *
          pivotInv k *
          higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k p j) ≤
        (r : ℝ) ^ 2 *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i p) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k p j) := by
    exact maxEntryNorm_matrix_mul_mul_le_dim_sq hr
      (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i p)
      (pivotInv k)
      (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k p j)
  calc
    maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1) i j)
        ≤
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) +
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i p *
          pivotInv k *
          higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k p j) := hsub
    _ ≤
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) +
      (r : ℝ) ^ 2 *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i p) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k p j) := by
        exact add_le_add le_rfl hprod
    _ =
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) +
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i p) *
          ((r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k)) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k p j) := by
        ring

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    exact matrix-product local Schur estimate in the matrix `∞` operator norm.

    This instantiates the generic `SeminormedRing` exact-update proof with
    Mathlib's `Matrix.linftyOpNormedRing`.  Unlike the entrywise max norm
    route above, no dimension factor or separate product-bound hypothesis is
    needed, because the block norm is genuinely submultiplicative for matrix
    multiplication. -/
theorem higham13_algorithm13_3_matrix_infNorm_active_local_schur_bound
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    SchurStageActiveLocalSchurBound13_8
      (fun k i j => infNorm
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (fun k => infNorm (pivotInv k)) := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  simpa [higham13_algorithm13_3_schurStageNorm,
    higham13_algorithm13_3_pivotInvNorm,
    higham13_algorithm13_3_schurStageMatrixBlock, infNorm] using
    (higham13_algorithm13_3_schurStage_local_schur_bound A pivotInv)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    exact matrix-product local Schur estimate in the Euclidean `2`-operator
    norm.

    This is the Euclidean analogue of the matrix-`∞` local Schur route above.
    It uses the exact Algorithm 13.3 Schur update, the `opNorm2` triangle
    inequality, and the triple-product subordinate bound, so no entrywise
    max-norm product shortcut is asserted. -/
theorem higham13_algorithm13_3_matrix_opNorm2_active_local_schur_bound
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    SchurStageActiveLocalSchurBound13_8
      (fun k i j => opNorm2 (fun s t =>
        higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j s t))
      (fun k => opNorm2 (fun s t => pivotInv k s t)) := by
  intro k hk i j hik hjk
  let stage : ℕ → Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_schurStageMatrixBlock A pivotInv
  let p : Fin m := ⟨k, hk⟩
  have hUpdate :=
    (higham13_algorithm13_3_schurStageBlock_exact_update A pivotInv)
      k hk i j hik hjk
  have hUpdateM :
      stage (k + 1) i j =
        stage k i j - stage k i p * pivotInv k * stage k p j := by
    simpa [stage, higham13_algorithm13_3_schurStageMatrixBlock, p] using
      hUpdate
  have hsub :
      opNorm2 (fun s t => stage (k + 1) i j s t) ≤
        opNorm2 (fun s t => stage k i j s t) +
          opNorm2
            (fun s t => (stage k i p * pivotInv k * stage k p j) s t) := by
    rw [hUpdateM]
    simpa [Pi.sub_apply] using
      (opNorm2_sub_le
        (fun s t => stage k i j s t)
        (fun s t => (stage k i p * pivotInv k * stage k p j) s t))
  have hprod :
      opNorm2
          (fun s t => (stage k i p * pivotInv k * stage k p j) s t) ≤
        opNorm2 (fun s t => stage k i p s t) *
          opNorm2 (fun s t => pivotInv k s t) *
            opNorm2 (fun s t => stage k p j s t) := by
    simpa [matMul, Matrix.mul_apply] using
      (opNorm2_matMul_triple_le
        (fun s t => stage k i p s t)
        (fun s t => pivotInv k s t)
        (fun s t => stage k p j s t))
  exact le_trans hsub (add_le_add_right hprod _)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7:
    Euclidean lower-norm source table gives active column dominance for the
    matrix-product Algorithm 13.3 stage table in the `2`-operator norm.

    The stage diagonal certificate is the attained lower norm
    `matMulVecLowerNorm2`; the active reciprocal table is derived from exact
    pivot right-inverse data.  This is a genuine Euclidean downstream surface,
    deliberately separate from the entrywise max-norm Eq.13.21 branch. -/
theorem
    higham13_algorithm13_3_matrix_opNorm2_active_column_dominance_of_vecNorm2_source_table
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => opNorm2 (fun s t => A i j s t)) invDiagBound)
    (hInitInv : ∀ j : Fin m,
      matMulVecLowerNorm2 hr (fun s t => A j j s t) = invDiagBound j)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (fun s t =>
          higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩ s t)
        (fun s t => pivotInv k s t)) :
    SchurStageActiveColumnDom13_7
      (fun k i j => opNorm2 (fun s t =>
        higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j s t))
      (fun k j => matMulVecLowerNorm2 hr (fun s t =>
        higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k j j s t)) := by
  let stageNorm : ℕ → Fin m → Fin m → ℝ :=
    fun k i j => opNorm2 (fun s t =>
      higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j s t)
  let stageInvDiagBound : ℕ → Fin m → ℝ :=
    fun k j => matMulVecLowerNorm2 hr (fun s t =>
      higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k j j s t)
  let pivotInvNorm : ℕ → ℝ :=
    fun k => opNorm2 (fun s t => pivotInv k s t)
  have hDiagUpdate :
      SchurStageActiveDiagLowerUpdate13_7
        stageNorm stageInvDiagBound pivotInvNorm := by
    simpa [stageNorm, stageInvDiagBound, pivotInvNorm] using
      (higham13_algorithm13_3_vecNorm2_diag_lower_update hr A pivotInv)
  have hRecip :
      SchurStageActivePivotInvReciprocal13_7
        stageInvDiagBound pivotInvNorm := by
    simpa [stageInvDiagBound, pivotInvNorm] using
      (higham13_algorithm13_3_vecNorm2_active_pivot_reciprocal_of_right_inverse
        hr A pivotInv hPivotRight)
  have hPivotBound :
      ∀ k : ℕ, ∀ hk : k < m,
        pivotInvNorm k * stageInvDiagBound k ⟨k, hk⟩ ≤ 1 :=
    higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
      stageInvDiagBound pivotInvNorm hRecip
  exact
    higham13_theorem13_7_active_column_dominance_of_steps
      (fun i j : Fin m => opNorm2 (fun s t => A i j s t))
      invDiagBound hDom stageNorm stageInvDiagBound
      (by
        intro i j
        simp [stageNorm, higham13_algorithm13_3_schurStageMatrixBlock,
          higham13_algorithm13_3_schurStageBlock])
      (by
        intro j
        simpa [stageInvDiagBound, higham13_algorithm13_3_schurStageMatrixBlock,
          higham13_algorithm13_3_schurStageBlock] using hInitInv j)
      (higham13_theorem13_7_active_column_dom_step_of_local_schur_bound
        stageNorm stageInvDiagBound pivotInvNorm
        (by
          intro k i j
          exact opNorm2_nonneg _)
        (by
          intro k
          exact opNorm2_nonneg _)
        hPivotBound
        (by
          simpa [stageNorm, pivotInvNorm] using
            (higham13_algorithm13_3_matrix_opNorm2_active_local_schur_bound
              A pivotInv))
        hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    Euclidean active-stage `2 * max` bound for Algorithm 13.3 from the
    concrete `matMulVecLowerNorm2` source table and active pivot right
    inverses.

    This theorem explicitly chooses the `opNorm2` downstream surface: both the
    initial BDD table and every Schur-stage block are measured in the
    Euclidean operator norm.  It is not the printed entrywise max-norm
    Eq.13.21 endpoint. -/
theorem
    higham13_algorithm13_3_matrix_opNorm2_active_stage_bound_of_vecNorm2_source_table
    {m r : ℕ} (_hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => opNorm2 (fun s t => A i j s t)) invDiagBound)
    (hDiagBound : ∀ j : Fin m,
      invDiagBound j ≤ opNorm2 (fun s t => A j j s t))
    (hInitInv : ∀ j : Fin m,
      matMulVecLowerNorm2 hr (fun s t => A j j s t) = invDiagBound j)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (fun s t =>
          higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩ s t)
        (fun s t => pivotInv k s t))
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, opNorm2 (fun s t => A i j s t) ≤ normMax) :
    ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      opNorm2 (fun s t =>
        higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j s t) ≤
          2 * normMax := by
  intro k i j _hk hik hjk
  let stageNorm : ℕ → Fin m → Fin m → ℝ :=
    fun k i j => opNorm2 (fun s t =>
      higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j s t)
  let stageInvDiagBound : ℕ → Fin m → ℝ :=
    fun k j => matMulVecLowerNorm2 hr (fun s t =>
      higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k j j s t)
  let pivotInvNorm : ℕ → ℝ :=
    fun k => opNorm2 (fun s t => pivotInv k s t)
  have hDiagUpdate :
      SchurStageActiveDiagLowerUpdate13_7
        stageNorm stageInvDiagBound pivotInvNorm := by
    simpa [stageNorm, stageInvDiagBound, pivotInvNorm] using
      (higham13_algorithm13_3_vecNorm2_diag_lower_update hr A pivotInv)
  have hRecip :
      SchurStageActivePivotInvReciprocal13_7
        stageInvDiagBound pivotInvNorm := by
    simpa [stageInvDiagBound, pivotInvNorm] using
      (higham13_algorithm13_3_vecNorm2_active_pivot_reciprocal_of_right_inverse
        hr A pivotInv hPivotRight)
  have hPivotBound :
      ∀ k : ℕ, ∀ hk : k < m,
        pivotInvNorm k * stageInvDiagBound k ⟨k, hk⟩ ≤ 1 :=
    higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
      stageInvDiagBound pivotInvNorm hRecip
  exact
    higham13_theorem13_8_active_stage_block_bound_of_local_schur_bound
      (fun i j : Fin m => opNorm2 (fun s t => A i j s t))
      invDiagBound hDom hDiagBound
      stageNorm stageInvDiagBound pivotInvNorm
      (by
        intro i j
        simp [stageNorm, higham13_algorithm13_3_schurStageMatrixBlock,
          higham13_algorithm13_3_schurStageBlock])
      (by
        intro k i j
        exact opNorm2_nonneg _)
      (by
        intro k
        exact opNorm2_nonneg _)
      (higham13_algorithm13_3_matrix_opNorm2_active_column_dominance_of_vecNorm2_source_table
        hr A pivotInv invDiagBound hDom hInitInv hPivotRight)
      hPivotBound
      (by
        simpa [stageNorm, pivotInvNorm] using
          (higham13_algorithm13_3_matrix_opNorm2_active_local_schur_bound
            A pivotInv))
      normMax hMax k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7:
    source-shaped active column block diagonal dominance for true
    matrix-product Algorithm 13.3 in the matrix `∞` operator norm.

    This is the concrete block-`∞` specialization of the exact-update
    Theorem 13.7 proof layer.  The pivot-product and diagonal-update
    certificates remain explicit; this theorem closes only the active
    dominance propagation step for the submultiplicative matrix norm. -/
theorem higham13_algorithm13_3_matrix_infNorm_active_column_dominance_of_pivot_bound
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      infNorm (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => infNorm
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => infNorm (pivotInv k))) :
    SchurStageActiveColumnDom13_7
      (fun k i j => infNorm
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hInitNorm :
      ∀ i j : Fin m, ‖A i j‖ = (fun i j : Fin m => infNorm (A i j)) i j := by
    intro i j
    rfl
  have hStageNorm :
      ∀ k : ℕ, ∀ i j : Fin m,
        higham13_algorithm13_3_schurStageNorm A pivotInv k i j =
          infNorm
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) := by
    intro k i j
    rfl
  have hPivotNorm :
      ∀ k : ℕ, higham13_algorithm13_3_pivotInvNorm pivotInv k =
        infNorm (pivotInv k) := by
    intro k
    rfl
  have hPivotBound' : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_pivotInvNorm pivotInv k *
          stageInvDiagBound k ⟨k, hk⟩ ≤ 1 := by
    intro k hk
    simpa [hPivotNorm k] using hPivotBound k hk
  have hDiagUpdate' : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv) := by
    intro k hk j hj
    simpa [hStageNorm, hPivotNorm] using hDiagUpdate k hk j hj
  have h :=
    higham13_algorithm13_3_active_column_dominance_of_pivot_bound
      (blockNorm := fun i j : Fin m => infNorm (A i j))
      (invDiagBound := invDiagBound)
      (hDom := hDom)
      (A := A)
      (pivotInv := pivotInv)
      (stageInvDiagBound := stageInvDiagBound)
      (hInitNorm := hInitNorm)
      (hInitInv := hInitInv)
      (hPivotBound := hPivotBound')
      (hDiagUpdate := hDiagUpdate')
  simpa [hStageNorm] using h

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    matrix-`∞` active column dominance from the concrete CLM source-table
    hypotheses.

    This removes the intermediate pivot-product and diagonal-update arguments
    from the theorem surface by using `diagLowerCertGeneric` and the concrete
    CLM source-table bridge.  The source lower table and exact active pivot
    inverse identities remain explicit. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_active_column_dominance_of_continuousLinearMap_source_table
    {m r : ℕ}
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
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
    SchurStageActiveColumnDom13_7
      (fun k i j => infNorm
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv) := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hPivotBound :
      ∀ k : ℕ, ∀ hk : k < m,
        infNorm (pivotInv k) *
            higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv
              k ⟨k, hk⟩ ≤
          1 :=
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_pivot_bound_of_continuousLinearMap_source_table
      hunit invDiagBound A pivotInv hInit hLeft hRight
  have hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => infNorm
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (fun k => infNorm (pivotInv k)) := by
    simpa [higham13_algorithm13_3_schurStageNorm,
      higham13_algorithm13_3_pivotInvNorm,
      higham13_algorithm13_3_schurStageMatrixBlock, infNorm] using
      (higham13_algorithm13_3_diagLowerCertGeneric_update invDiagBound A pivotInv)
  exact
    higham13_algorithm13_3_matrix_infNorm_active_column_dominance_of_pivot_bound
      A pivotInv invDiagBound
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      hDom
      (higham13_algorithm13_3_diagLowerCertGeneric_zero invDiagBound A pivotInv)
      hPivotBound hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    matrix-`∞` active column dominance from CLM source-table data and certified
    active pivot right inverses.

    Compared with
    `higham13_algorithm13_3_matrix_infNorm_active_column_dominance_of_continuousLinearMap_source_table`,
    this wrapper derives the exact active CLM inverse identities from
    `IsRightInverse` pivot certificates. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_active_column_dominance_of_continuousLinearMap_source_table_of_pivot_right_inverse
    {m r : ℕ}
    (hunit : ({x : Fin r → ℝ | ‖x‖ = 1} : Set (Fin r → ℝ)).Nonempty)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
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
    SchurStageActiveColumnDom13_7
      (fun k i j => infNorm
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv) := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hPivotBound :
      ∀ k : ℕ, ∀ hk : k < m,
        infNorm (pivotInv k) *
            higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv
              k ⟨k, hk⟩ ≤
          1 :=
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_pivot_bound_of_continuousLinearMap_source_table_of_pivot_right_inverse
      hunit invDiagBound A pivotInv hInit hPivotRight
  have hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => infNorm
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (fun k => infNorm (pivotInv k)) := by
    simpa [higham13_algorithm13_3_schurStageNorm,
      higham13_algorithm13_3_pivotInvNorm,
      higham13_algorithm13_3_schurStageMatrixBlock, infNorm] using
      (higham13_algorithm13_3_diagLowerCertGeneric_update invDiagBound A pivotInv)
  exact
    higham13_algorithm13_3_matrix_infNorm_active_column_dominance_of_pivot_bound
      A pivotInv invDiagBound
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      hDom
      (higham13_algorithm13_3_diagLowerCertGeneric_zero invDiagBound A pivotInv)
      hPivotBound hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7:
    BDD all-leading-prefix data gives matrix-`∞` active column dominance once
    the active Algorithm 13.3 pivots have certified right inverses.

    This positive-block-size wrapper accepts the source-facing matrix-`∞` BDD
    hypothesis, transports it to the finite-function block norm needed by the
    initial lower-table bridge, and then reuses the matrix-`∞` source-table
    active-dominance route. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_active_column_dominance_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
    {m r : ℕ} (hr : 0 < r)
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
    letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
    SchurStageActiveColumnDom13_7
      (fun k i j => infNorm
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv) := by
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
  exact
    higham13_algorithm13_3_matrix_infNorm_active_column_dominance_of_continuousLinearMap_source_table_of_pivot_right_inverse
      (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv invDiagBound
      hDom hInit hPivotRight

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7:
    source-facing matrix-`∞` active column dominance from BDD data and
    canonical first-Schur-tail pivot inverse data.

    The active pivot right-inverse table is derived internally from
    `pivotInv 0 = nonsingInv r (A 0 0)` and the first Schur tail's determinant
    plus canonical `nonsingInv` table. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_active_column_dominance_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pos_dim
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
    letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
    SchurStageActiveColumnDom13_7
      (fun k i j => infNorm
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv) := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr A pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTailDet
      hTailPivotInv
  exact
    higham13_algorithm13_3_matrix_infNorm_active_column_dominance_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
      hr A pivotInv invDiagBound hPrefix hDom hBound hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    matrix-`∞` active column dominance from initial diagonal inverse reciprocal
    data and certified active pivot right inverses. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_active_column_dominance_of_initial_diag_right_inverse_of_pivot_right_inverse
    {m r : ℕ}
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
    letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
    SchurStageActiveColumnDom13_7
      (fun k i j => infNorm
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv) := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hPivotBound :
      ∀ k : ℕ, ∀ hk : k < m,
        infNorm (pivotInv k) *
            higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv
              k ⟨k, hk⟩ ≤
          1 :=
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_pivot_bound_of_initial_diag_right_inverse_of_pivot_right_inverse
      hunit invDiagBound A pivotInv diagInv hInvBound hDiagRight hPivotRight
  have hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => infNorm
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (fun k => infNorm (pivotInv k)) := by
    simpa [higham13_algorithm13_3_schurStageNorm,
      higham13_algorithm13_3_pivotInvNorm,
      higham13_algorithm13_3_schurStageMatrixBlock, infNorm] using
      (higham13_algorithm13_3_diagLowerCertGeneric_update invDiagBound A pivotInv)
  exact
    higham13_algorithm13_3_matrix_infNorm_active_column_dominance_of_pivot_bound
      A pivotInv invDiagBound
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      hDom
      (higham13_algorithm13_3_diagLowerCertGeneric_zero invDiagBound A pivotInv)
      hPivotBound hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7:
    matrix-product active column dominance from the source induction layer.

    This specializes the abstract active-dominance induction to the concrete
    Algorithm 13.3 matrix-stage table.  The local Schur estimate and diagonal
    lower-update certificate remain explicit, matching the proof obligations in
    equation (13.18). -/
theorem higham13_algorithm13_3_matrix_active_column_dominance_of_local_schur_bound
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvNonneg : ∀ k : ℕ, 0 ≤ pivotInvNorm k)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      pivotInvNorm k * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hLocal : SchurStageActiveLocalSchurBound13_8
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      pivotInvNorm)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound pivotInvNorm) :
    SchurStageActiveColumnDom13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound := by
  exact
    higham13_theorem13_7_active_column_dominance_of_steps
      (fun i j => maxEntryNorm hr (A i j))
      invDiagBound hDom
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (by
        intro i j
        rfl)
      hInitInv
      (higham13_theorem13_7_active_column_dom_step_of_local_schur_bound
        (fun k i j => maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
        stageInvDiagBound pivotInvNorm
        (by
          intro k i j
          exact maxEntryNorm_nonneg hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
        hPivotInvNonneg hPivotInvBound hLocal hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7:
    source-strength active column dominance for the matrix-product stage table
    from an explicit max-entry triple-product estimate. -/
theorem higham13_algorithm13_3_matrix_active_column_dominance_of_product_bound
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    SchurStageActiveColumnDom13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound := by
  exact
    higham13_algorithm13_3_matrix_active_column_dominance_of_local_schur_bound
      hr A pivotInv (fun k => maxEntryNorm hr (pivotInv k))
      invDiagBound stageInvDiagBound hDom hInitInv
      (by
        intro k
        exact maxEntryNorm_nonneg hr (pivotInv k))
      hPivotInvBound
      (higham13_algorithm13_3_matrix_active_local_schur_bound_of_product_bound
        hr A pivotInv hProduct)
      hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7:
    dimension-aware active column dominance for the true matrix-product
    Algorithm 13.3 stage table.

    The pivot norm is inflated by `(r : ℝ)^2`, exactly as in the proved
    max-entry matrix-product local Schur estimate.  This is a reusable
    dimension-aware proof-layer result, not the source's dimension-free
    structured argument. -/
theorem higham13_algorithm13_3_matrix_active_column_dominance_with_dim_factor
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      ((r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k)) *
          stageInvDiagBound k ⟨k, hk⟩ ≤
        1)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => (r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k))) :
    SchurStageActiveColumnDom13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound := by
  exact
    higham13_algorithm13_3_matrix_active_column_dominance_of_local_schur_bound
      hr A pivotInv (fun k => (r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k))
      invDiagBound stageInvDiagBound hDom hInitInv
      (by
        intro k
        exact mul_nonneg (sq_nonneg (r : ℝ)) (maxEntryNorm_nonneg hr (pivotInv k)))
      hPivotInvBound
      (higham13_algorithm13_3_matrix_active_local_schur_bound_with_dim_factor
        hr A pivotInv)
      hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    active-stage max-entry bound for the source-faithful matrix-product
    Algorithm 13.3 stage table from the active column-dominance proof layer and
    an explicit local Schur max-entry estimate.

    This is the matrix-product analogue of the generic normed-ring
    `higham13_theorem13_8_active_stage_block_bound_of_local_schur_bound`.  It
    deliberately keeps the local Schur max-entry estimate on the theorem
    surface, since `Matrix` has no compatible `SeminormedRing` norm instance in
    this source max-entry norm. -/
theorem higham13_algorithm13_3_matrix_active_stage_bound_of_local_schur_bound
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hActiveDom : SchurStageActiveColumnDom13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hLocal : SchurStageActiveLocalSchurBound13_8
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
          2 * blockMaxNorm hm hr A := by
  intro k i j _hk hik hjk
  exact
    higham13_theorem13_8_active_stage_block_bound_of_local_schur_bound
      (fun i j => maxEntryNorm hr (A i j))
      invDiagBound
      hDom hDiagBound
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))
      (by
        intro i j
        rfl)
      (by
        intro k i j
        exact maxEntryNorm_nonneg hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (by
        intro k
        exact maxEntryNorm_nonneg hr (pivotInv k))
      hActiveDom
      hPivotInvBound
      hLocal
      (blockMaxNorm hm hr A)
      (fun i j => block_le_blockMaxNorm hm hr A i j)
      k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    active-stage max-entry bound for the true matrix-product Algorithm 13.3
    stage table using the proved finite-dimensional max-entry product estimate.

    The pivot budget is strengthened by the explicit `(r : ℝ)^2` factor
    required by matrix multiplication in the entrywise max norm.  This is a
    proved dimension-aware bridge, not the source's dimension-free structured
    argument. -/
theorem higham13_algorithm13_3_matrix_active_stage_bound_with_dim_factor
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hActiveDom : SchurStageActiveColumnDom13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      ((r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k)) *
          stageInvDiagBound k ⟨k, hk⟩ ≤
        1) :
    ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
          2 * blockMaxNorm hm hr A := by
  intro k i j _hk hik hjk
  exact
    higham13_theorem13_8_active_stage_block_bound_of_local_schur_bound
      (fun i j => maxEntryNorm hr (A i j))
      invDiagBound
      hDom hDiagBound
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => (r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k))
      (by
        intro i j
        rfl)
      (by
        intro k i j
        exact maxEntryNorm_nonneg hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (by
        intro k
        exact mul_nonneg (sq_nonneg (r : ℝ)) (maxEntryNorm_nonneg hr (pivotInv k)))
      hActiveDom
      hPivotInvBound
      (higham13_algorithm13_3_matrix_active_local_schur_bound_with_dim_factor
        hr A pivotInv)
      (blockMaxNorm hm hr A)
      (fun i j => block_le_blockMaxNorm hm hr A i j)
      k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    matrix-product active-stage bound from the local Schur estimate and the
    Theorem 13.7 diagonal lower-update layer.

    This wrapper removes the raw active-column-dominance premise from
    `higham13_algorithm13_3_matrix_active_stage_bound_of_local_schur_bound`;
    the remaining source obligations are the local Schur estimate, pivot
    budget, and diagonal certificate update. -/
theorem higham13_algorithm13_3_matrix_active_stage_bound_of_local_schur_diag_update
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hLocal : SchurStageActiveLocalSchurBound13_8
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (fun k => maxEntryNorm hr (pivotInv k)))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
          2 * blockMaxNorm hm hr A := by
  exact
    higham13_algorithm13_3_matrix_active_stage_bound_of_local_schur_bound
      hm hr A pivotInv invDiagBound stageInvDiagBound hDom hDiagBound
      (higham13_algorithm13_3_matrix_active_column_dominance_of_local_schur_bound
        hr A pivotInv (fun k => maxEntryNorm hr (pivotInv k))
        invDiagBound stageInvDiagBound hDom hInitInv
        (by
          intro k
          exact maxEntryNorm_nonneg hr (pivotInv k))
      hPivotInvBound hLocal hDiagUpdate)
      hPivotInvBound hLocal

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    source-strength conditional matrix-product active-stage bound from a
    dimension-free triple-product max-entry estimate and the diagonal
    lower-update layer.

    This leaves the structured product estimate visible instead of replacing it
    by the generic `(r : ℝ)^2` matrix-multiplication bound. -/
theorem higham13_algorithm13_3_matrix_active_stage_bound_of_product_bound_diag_update
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
          2 * blockMaxNorm hm hr A := by
  exact
    higham13_algorithm13_3_matrix_active_stage_bound_of_local_schur_diag_update
      hm hr A pivotInv invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hPivotInvBound
      (higham13_algorithm13_3_matrix_active_local_schur_bound_of_product_bound
        hr A pivotInv hProduct)
      hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    dimension-aware matrix-product active-stage bound from the diagonal
    lower-update layer.

    The active-column dominance premise is now proved from the explicit
    diagonal update and the strengthened `(r : ℝ)^2` pivot budget. -/
theorem higham13_algorithm13_3_matrix_active_stage_bound_with_dim_factor_of_diag_update
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      ((r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k)) *
          stageInvDiagBound k ⟨k, hk⟩ ≤
        1)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => (r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k))) :
    ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
          2 * blockMaxNorm hm hr A := by
  exact
    higham13_algorithm13_3_matrix_active_stage_bound_with_dim_factor
      hm hr A pivotInv invDiagBound stageInvDiagBound hDom hDiagBound
      (higham13_algorithm13_3_matrix_active_column_dominance_with_dim_factor
        hr A pivotInv invDiagBound stageInvDiagBound hDom hInitInv
        hPivotInvBound hDiagUpdate)
      hPivotInvBound

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    source-shaped active-stage bound for true matrix-product Algorithm 13.3
    in the matrix `∞` operator norm.

    The theorem follows the book's submultiplicative block-norm proof path:
    the exact Schur update supplies the local product estimate through
    `Matrix.linftyOpNormedRing`, then the existing Theorem 13.7--13.8 active
    dominance machinery gives
    `‖Aᵢⱼ^(k)‖∞ <= 2 * normMax`.  The pivot product and diagonal-update
    certificates remain explicit, matching the analytic source obligations. -/
theorem higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_pivot_bound
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j))
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      infNorm (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => infNorm
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => infNorm (pivotInv k)))
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, infNorm (A i j) ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
      2 * normMax := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hInitNorm :
      ∀ i j : Fin m, ‖A i j‖ = (fun i j : Fin m => infNorm (A i j)) i j := by
    intro i j
    rfl
  have hStageNorm :
      ∀ k : ℕ, ∀ i j : Fin m,
        higham13_algorithm13_3_schurStageNorm A pivotInv k i j =
          infNorm
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) := by
    intro k i j
    rfl
  have hPivotNorm :
      ∀ k : ℕ, higham13_algorithm13_3_pivotInvNorm pivotInv k =
        infNorm (pivotInv k) := by
    intro k
    rfl
  have hPivotBound' : ∀ k : ℕ, ∀ hk : k < m,
      higham13_algorithm13_3_pivotInvNorm pivotInv k *
          stageInvDiagBound k ⟨k, hk⟩ ≤ 1 := by
    intro k hk
    simpa [hPivotNorm k] using hPivotBound k hk
  have hDiagUpdate' : SchurStageActiveDiagLowerUpdate13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      stageInvDiagBound
      (higham13_algorithm13_3_pivotInvNorm pivotInv) := by
    intro k hk j hj
    simpa [hStageNorm, hPivotNorm] using hDiagUpdate k hk j hj
  have h :=
    higham13_algorithm13_3_active_stage_block_bound_of_pivot_bound
      (blockNorm := fun i j : Fin m => infNorm (A i j))
      (invDiagBound := invDiagBound)
      (hDom := hDom)
      (hDiagBound := hDiagBound)
      (A := A)
      (pivotInv := pivotInv)
      (stageInvDiagBound := stageInvDiagBound)
      (hInitNorm := hInitNorm)
      (hInitInv := hInitInv)
      (hPivotBound := hPivotBound')
      (hDiagUpdate := hDiagUpdate')
      (normMax := normMax)
      (hMax := hMax)
      (k := k) (i := i) (j := j) hik hjk
  simpa [hStageNorm k i j] using h

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    matrix-`∞` active-stage bound from the concrete CLM source-table
    hypotheses.

    The theorem packages the source-table-to-certificate, pivot-product, and
    active-column steps for Mathlib's submultiplicative matrix `∞` norm.  It
    remains conditional on the initial lower table and exact active pivot
    inverse identities, which are the mathematical BDD source obligations. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_continuousLinearMap_source_table
    {m r : ℕ}
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
        (matrixMulVecCLM (pivotInv k) y) = y)
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, infNorm (A i j) ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
      2 * normMax := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hPivotBound :
      ∀ k : ℕ, ∀ hk : k < m,
        infNorm (pivotInv k) *
            higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv
              k ⟨k, hk⟩ ≤
          1 :=
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_pivot_bound_of_continuousLinearMap_source_table
      hunit invDiagBound A pivotInv hInit hLeft hRight
  have hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => infNorm
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (fun k => infNorm (pivotInv k)) := by
    simpa [higham13_algorithm13_3_schurStageNorm,
      higham13_algorithm13_3_pivotInvNorm,
      higham13_algorithm13_3_schurStageMatrixBlock, infNorm] using
      (higham13_algorithm13_3_diagLowerCertGeneric_update invDiagBound A pivotInv)
  exact
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_pivot_bound
      A pivotInv invDiagBound
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      hDom hDiagBound
      (higham13_algorithm13_3_diagLowerCertGeneric_zero invDiagBound A pivotInv)
      hPivotBound hDiagUpdate normMax hMax k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    matrix-`∞` active-stage bound from CLM source-table data and certified
    active pivot right inverses.

    This wrapper derives the continuous-linear inverse identities from
    `IsRightInverse` certificates and then reuses the existing matrix-`∞`
    source-table route. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_continuousLinearMap_source_table_of_pivot_right_inverse
    {m r : ℕ}
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
        (pivotInv k))
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, infNorm (A i j) ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
      2 * normMax := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hPivotBound :
      ∀ k : ℕ, ∀ hk : k < m,
        infNorm (pivotInv k) *
            higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv
              k ⟨k, hk⟩ ≤
          1 :=
    higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_pivot_bound_of_continuousLinearMap_source_table_of_pivot_right_inverse
      hunit invDiagBound A pivotInv hInit hPivotRight
  have hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => infNorm
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      (fun k => infNorm (pivotInv k)) := by
    simpa [higham13_algorithm13_3_schurStageNorm,
      higham13_algorithm13_3_pivotInvNorm,
      higham13_algorithm13_3_schurStageMatrixBlock, infNorm] using
      (higham13_algorithm13_3_diagLowerCertGeneric_update invDiagBound A pivotInv)
  exact
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_pivot_bound
      A pivotInv invDiagBound
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      hDom hDiagBound
      (higham13_algorithm13_3_diagLowerCertGeneric_zero invDiagBound A pivotInv)
      hPivotBound hDiagUpdate normMax hMax k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    BDD all-leading-prefix data gives the matrix-`∞` active-stage `2 * max`
    bound once the active Algorithm 13.3 pivots have certified right inverses.

    The wrapper derives both source-table prerequisites from BDD data: the
    initial lower table comes through the finite-function norm bridge, and
    `invDiagBound <= ‖A_jj‖∞` follows from the nonpositive bound table. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
    {m r : ℕ} (hr : 0 < r)
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
        (pivotInv k))
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, infNorm (A i j) ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
      2 * normMax := by
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
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_continuousLinearMap_source_table_of_pivot_right_inverse
      (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv invDiagBound
      hDom hDiagBound hInit hPivotRight normMax hMax k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    source-facing matrix-`∞` active-stage `2 * max` bound from BDD data and
    canonical first-Schur-tail pivot inverse data.

    This removes the explicit all-active pivot right-inverse table from the
    BDD matrix-`∞` stage-bound interface, leaving the recursive tail
    determinant/equality table as the remaining source obligation. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pos_dim
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
            ⟨k, hk⟩ ⟨k, hk⟩))
    (normMax : ℝ)
    (hMax : ∀ i j : Fin (m + 1), infNorm (A i j) ≤ normMax)
    (k : ℕ) (i j : Fin (m + 1)) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
      2 * normMax := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hPivotRight :=
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr A pivotInv invDiagBound hPrefix hDom hBound hPivot0 hTailDet
      hTailPivotInv
  exact
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
      hr A pivotInv invDiagBound hPrefix hDom hBound hPivotRight
      normMax hMax k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    matrix-`∞` active-stage bound from initial diagonal inverse reciprocal data
    and certified active pivot right inverses.

    This wrapper derives both the initial lower table and the diagonal
    comparison `invDiagBound j <= ‖A_jj‖∞` from the same diagonal-block
    right-inverse certificates. -/
theorem
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_initial_diag_right_inverse_of_pivot_right_inverse
    {m r : ℕ}
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
        (pivotInv k))
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, infNorm (A i j) ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
      2 * normMax := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hInit :=
    higham13_algorithm13_3_matrix_infNorm_initial_lower_table_of_diag_right_inverse
      hunit invDiagBound A pivotInv diagInv hInvBound hDiagRight
  have hDiagBound :
      ∀ j : Fin m, invDiagBound j ≤ infNorm (A j j) :=
    higham13_algorithm13_3_matrix_infNorm_initial_diag_bound_of_diag_right_inverse
      hunit invDiagBound A diagInv hInvBound hDiagRight
  exact
    higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_continuousLinearMap_source_table_of_pivot_right_inverse
      hunit A pivotInv invDiagBound hDom hDiagBound hInit hPivotRight
      normMax hMax k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, §13.3.1:
    comparison from the matrix `∞` operator norm on one block to the chapter
    block max norm of the whole block matrix.

    This is a bookkeeping bridge for routes that prove Algorithm 13.3 stage
    bounds in `infNorm` but must feed the Eq.13.21 max-entry surface.  The
    explicit factor `r` is the standard `∞`-operator/max-entry comparison for
    one `r × r` block, so this is dependency-strength rather than the
    source-strength dimension-free Eq.13.21 conclusion. -/
theorem higham13_algorithm13_3_matrix_infNorm_block_le_card_mul_blockMaxNorm
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (i j : Fin m) :
    infNorm (A i j) ≤ (r : ℝ) * blockMaxNorm hm hr A := by
  calc
    infNorm (A i j) ≤ (r : ℝ) * maxEntryNorm hr (A i j) :=
      infNorm_le_card_mul_maxEntryNorm hr (A i j)
    _ ≤ (r : ℝ) * blockMaxNorm hm hr A :=
      mul_le_mul_of_nonneg_left (block_le_blockMaxNorm hm hr A i j)
        (Nat.cast_nonneg r)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    an active-stage matrix-`∞` bound gives the corresponding max-entry bound
    on the same active matrix-product Schur-stage block. -/
theorem higham13_algorithm13_3_matrix_infNorm_active_stage_maxEntry_bound
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (normMax : ℝ)
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
        2 * normMax)
    (k : ℕ) (i j : Fin m) (hk : k ≤ m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
      2 * normMax := by
  exact le_trans
    (maxEntryNorm_le_infNorm hr
      (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
    (hActive k i j hk hik hjk)

/-- A source active-stage max-entry bound controls every entry of every
    recorded matrix-product Schur stage.

    Algorithm 13.3 carries inactive blocks forward.  Hence a bound proved for
    each active block of each stage extends to the total finite stage table by
    induction over the stage index. -/
theorem higham13_algorithm13_3_matrixStageBlock_bound_of_active_bound
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {C : ℝ}
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤ C) :
    ∀ k : ℕ, k ≤ m → ∀ i j : Fin m,
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤ C := by
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
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1) i j =
              higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j := by
          simp [higham13_algorithm13_3_schurStageMatrixBlock,
            higham13_algorithm13_3_schurStageBlock, hklt, hnot_lt]
        simpa [hstage] using ih (Nat.le_of_succ_le hk) i j

/-- Active-stage max-entry bounds give a block-max bound for one total
    matrix-product Schur stage. -/
theorem higham13_algorithm13_3_matrixStage_blockMaxNorm_bound_of_active_bound
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {C : ℝ}
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤ C)
    (k : ℕ) (hk : k ≤ m) :
    blockMaxNorm hm hr
        (fun i j => higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
      C := by
  apply blockMaxNorm_le_of_entry_abs_le
  intro i j s t
  exact le_trans
    (entry_le_maxEntryNorm hr
      (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) s t)
    (higham13_algorithm13_3_matrixStageBlock_bound_of_active_bound
      hr A pivotInv hActive k hk i j)

/-- A uniform bound on each recorded matrix-product Schur stage controls the
    finite matrix-stage history bound. -/
theorem higham13_algorithm13_3_matrixStageHistoryBound_le_of_stage_bound
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {C : ℝ}
    (hStage : ∀ k : ℕ, k ≤ m →
      blockMaxNorm hm hr
          (fun i j => higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
        C) :
    higham13_algorithm13_3_matrixStageHistoryBound hm hr A pivotInv ≤ C := by
  unfold higham13_algorithm13_3_matrixStageHistoryBound
  apply Finset.sup'_le
  intro K _hK
  exact hStage K.val (Nat.le_of_lt_succ K.isLt)

/-- A source active-stage matrix-`∞` bound controls every block of every
    recorded matrix-product Schur stage. -/
theorem higham13_algorithm13_3_matrixStageBlock_infNorm_bound_of_active_bound
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {C : ℝ}
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤ C) :
    ∀ k : ℕ, k ≤ m → ∀ i j : Fin m,
      infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
        C := by
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
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1) i j =
              higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j := by
          simp [higham13_algorithm13_3_schurStageMatrixBlock,
            higham13_algorithm13_3_schurStageBlock, hklt, hnot_lt]
        simpa [hstage] using ih (Nat.le_of_succ_le hk) i j

/-- Active-stage matrix-`∞` bounds give a blockwise matrix-`∞` bound for one
    total matrix-product Schur stage. -/
theorem higham13_algorithm13_3_matrixStage_blockInfNorm_bound_of_active_bound
    {m r : ℕ} (hm : 0 < m)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {C : ℝ}
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤ C)
    (k : ℕ) (hk : k ≤ m) :
    blockInfNorm hm
        (fun i j => higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
      C := by
  apply blockInfNorm_le_of_block_le
  intro i j
  exact higham13_algorithm13_3_matrixStageBlock_infNorm_bound_of_active_bound
    A pivotInv hActive k hk i j

/-- A uniform blockwise matrix-`∞` bound on each recorded stage controls the
    finite matrix-`∞` stage-history bound. -/
theorem higham13_algorithm13_3_matrixStageHistoryInfBound_le_of_stage_bound
    {m r : ℕ} (hm : 0 < m)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {C : ℝ}
    (hStage : ∀ k : ℕ, k ≤ m →
      blockInfNorm hm
          (fun i j => higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
        C) :
    higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤ C := by
  unfold higham13_algorithm13_3_matrixStageHistoryInfBound
  apply Finset.sup'_le
  intro K _hK
  exact hStage K.val (Nat.le_of_lt_succ K.isLt)

/-- Active-stage matrix-`∞` bounds control the finite matrix-`∞`
    stage-history scalar. -/
theorem higham13_algorithm13_3_matrixStageHistoryInfBound_le_of_active_bound
    {m r : ℕ} (hm : 0 < m)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {C : ℝ}
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤ C) :
    higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤ C :=
  higham13_algorithm13_3_matrixStageHistoryInfBound_le_of_stage_bound
    hm A pivotInv
    (fun k hk =>
      higham13_algorithm13_3_matrixStage_blockInfNorm_bound_of_active_bound
        hm A pivotInv hActive k hk)

/-- Higham, 2nd ed., Chapter 13, equation (13.23) in the blockwise
    matrix-`∞` stage-history norm: active-stage `2‖A‖` bounds control the
    finite matrix-product history. -/
theorem higham13_algorithm13_3_matrixStageHistoryInfBound_le_two_of_active_stage_bound
    {m r : ℕ} (hm : 0 < m)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (normMax : ℝ)
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      infNorm (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
        2 * normMax) :
    higham13_algorithm13_3_matrixStageHistoryInfBound hm A pivotInv ≤
      2 * normMax :=
  higham13_algorithm13_3_matrixStageHistoryInfBound_le_of_active_bound
    hm A pivotInv hActive

/-- Active-stage max-entry bounds control the max-entry norm of the finite
    matrix-stage history growth object. -/
theorem higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_le_of_active_bound
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {C : ℝ}
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤ C) :
    maxEntryNorm hN
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr A pivotInv) ≤
      C := by
  rw [higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_maxEntryNorm]
  exact
    higham13_algorithm13_3_matrixStageHistoryBound_le_of_stage_bound hm hr A pivotInv
      (fun k hk =>
        higham13_algorithm13_3_matrixStage_blockMaxNorm_bound_of_active_bound
          hm hr A pivotInv hActive k hk)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    the matrix-stage history growth object is bounded by `2‖A‖` once the
    Theorem 13.8 active-stage max-entry bound has been proved for every active
    block of the matrix-product Schur-stage table. -/
theorem higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_le_two_of_active_stage_bound
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
          2 * blockMaxNorm hm hr A) :
    maxEntryNorm hN
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr A pivotInv) ≤
      2 * blockMaxNorm hm hr A :=
  higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_le_of_active_bound
    hN hm hr A pivotInv hActive

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    active-stage `2‖A‖` bounds imply `ρ_n <= 2` for the finite matrix-stage
    history growth factor. -/
theorem higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_active_stage_bound
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
          2 * blockMaxNorm hm hr A) :
    growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
      2 := by
  exact
    growthFactorEntry_le_of_maxEntryNorm_le_mul (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        (Nat.mul_pos hm hr) hm hr A pivotInv)
      hApos
      (by
        rw [maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm hm hr A]
        exact
          higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_le_two_of_active_stage_bound
            (Nat.mul_pos hm hr) hm hr A pivotInv hActive)

/-- Higham, 2nd ed., Chapter 13, equation (13.21):
    active-stage max-entry bounds also control the upper factor assembled from
    the true matrix-product Algorithm 13.3 stage table.

    This is the matrix-stage analogue of the function-block Eq.13.21 upper
    endpoint.  It is conditional on the active-stage theorem, and therefore
    does not by itself prove the missing BDD product/update data. -/
theorem higham13_algorithm13_3_upperFromMatrixStages_blockMaxNorm_bound_of_active_stage_bound
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hActive : ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤ C) :
    blockMaxNorm hm hr
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤ C := by
  apply blockMaxNorm_le_of_entry_abs_le
  intro i j s t
  by_cases hij : i.val ≤ j.val
  · have hentry :
        |higham13_algorithm13_3_upperFromMatrixStages A pivotInv i j s t| ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv i.val i j) := by
      rw [higham13_algorithm13_3_upperFromMatrixStages_eq_of_le A pivotInv hij]
      exact entry_le_maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv i.val i j) s t
    exact le_trans hentry
      (hActive i.val i j (Nat.le_of_lt i.isLt) le_rfl hij)
  · have hzero :
        higham13_algorithm13_3_upperFromMatrixStages A pivotInv i j = 0 := by
      simp [higham13_algorithm13_3_upperFromMatrixStages, hij]
    calc
      |higham13_algorithm13_3_upperFromMatrixStages A pivotInv i j s t| = 0 := by
        simp [hzero]
      _ ≤ C := hC

/-- Higham, 2nd ed., Chapter 13, equation (13.21):
    source-strength upper-factor max-entry bound from the mixed
    matrix-`∞`/max-entry column-mass route. -/
theorem higham13_algorithm13_3_upperFromMatrixStages_blockMaxNorm_bound_of_mixed_column_mass
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDomInf : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagMax : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInfDom : SchurStageActiveColumnDom13_7
      (fun k i j => infNorm
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      infNorm (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
      2 * blockMaxNorm hm hr A := by
  exact
    higham13_algorithm13_3_upperFromMatrixStages_blockMaxNorm_bound_of_active_stage_bound
      hm hr A pivotInv
      (mul_nonneg (by norm_num) (blockMaxNorm_nonneg hm hr A))
      (higham13_algorithm13_3_matrix_active_stage_bound_of_mixed_column_mass
        hm hr A pivotInv invDiagBound stageInvDiagBound
        hDomInf hDiagMax hInfDom hPivotBound)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    source-strength `ρ_n <= 2` growth-factor bound from the mixed
    matrix-`∞`/max-entry column-mass route. -/
theorem higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_mixed_column_mass
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDomInf : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagMax : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInfDom : SchurStageActiveColumnDom13_7
      (fun k i j => infNorm
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      infNorm (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1) :
    growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
      2 := by
  exact
    higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_active_stage_bound
      hm hr A pivotInv hApos
      (higham13_algorithm13_3_matrix_active_stage_bound_of_mixed_column_mass
        hm hr A pivotInv invDiagBound stageInvDiagBound
        hDomInf hDiagMax hInfDom hPivotBound)

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    paired source-strength upper-factor and finite-history growth-factor
    consequences of the mixed matrix-`∞`/max-entry column-mass route. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_mixed_column_mass
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDomInf : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagMax : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInfDom : SchurStageActiveColumnDom13_7
      (fun k i j => infNorm
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      infNorm (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockMaxNorm hm hr A ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 := by
  exact
    ⟨higham13_algorithm13_3_upperFromMatrixStages_blockMaxNorm_bound_of_mixed_column_mass
        hm hr A pivotInv invDiagBound stageInvDiagBound hDomInf hDiagMax
        hInfDom hPivotBound,
      higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_mixed_column_mass
        hm hr A pivotInv hApos invDiagBound stageInvDiagBound hDomInf
        hDiagMax hInfDom hPivotBound⟩

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    source-strength mixed matrix-`∞`/max-entry endpoint from ordinary BDD,
    certified initial diagonal inverses, and certified active pivot inverses.

    The diagonal reciprocal data gives the max-entry diagonal comparison via
    `inv_infNorm_le_maxEntryNorm_of_isRightInverse`.  The same initial inverse
    table drives the matrix-`∞` active-column certificate, so the mixed
    column-mass proof reaches `rho <= 2` without the former nonpositive-budget
    collapse and without a factor depending on the block size. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_initial_diag_right_inverse_of_pivot_right_inverse_mixed_column_mass
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hInvBound : ∀ j : Fin m,
      invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockMaxNorm hm hr A ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hDiagMax : ∀ j : Fin m,
      invDiagBound j ≤ maxEntryNorm hr (A j j) := by
    intro j
    exact le_trans (hInvBound j)
      (inv_infNorm_le_maxEntryNorm_of_isRightInverse
        hr (A j j) (diagInv j) (hDiagRight j))
  have hInfDom :
      SchurStageActiveColumnDom13_7
        (fun k i j => infNorm
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
        (higham13_algorithm13_3_diagLowerCertGeneric
          invDiagBound A pivotInv) := by
    simpa using
      (higham13_algorithm13_3_matrix_infNorm_active_column_dominance_of_initial_diag_right_inverse_of_pivot_right_inverse
        (higham13_fin_fun_unit_sphere_nonempty hr) A pivotInv invDiagBound
        diagInv hDom hInvBound hDiagRight hPivotRight)
  have hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      infNorm (pivotInv k) *
          higham13_algorithm13_3_diagLowerCertGeneric
            invDiagBound A pivotInv k ⟨k, hk⟩ ≤
        1 := by
    simpa using
      (higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_pivot_bound_of_initial_diag_right_inverse_of_pivot_right_inverse
        (higham13_fin_fun_unit_sphere_nonempty hr) invDiagBound A pivotInv
        diagInv hInvBound hDiagRight hPivotRight)
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_mixed_column_mass
      hm hr A pivotInv hApos invDiagBound
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      hDom hDiagMax hInfDom hPivotBound

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equations
    (13.17)--(13.23): source-strength BDD endpoint with the complete recursive
    pivot-inverse sequence constructed internally.

    Ordinary column BDD is stated with the actual reciprocal matrix-`∞` norm
    of each nonsingular diagonal block.  All-leading-prefix nonsingularity
    constructs one compatible right-inverse table for every active Schur
    pivot.  The preceding mixed column-mass theorem then gives both the
    Eq.13.21 upper-factor estimate and the dimension-free `rho <= 2` stage
    growth estimate. -/
theorem
    higham13_algorithm13_3_exists_pivotInv_eq13_21_eq13_23_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDiagDet : ∀ j : Fin m, Matrix.det (A j j) ≠ 0)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol m
      (fun i j : Fin m => infNorm (A i j))
      (fun j : Fin m => (infNorm (nonsingInv r (A j j)))⁻¹)) :
    ∃ pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ,
      blockMaxNorm hm hr
          (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
          2 * blockMaxNorm hm hr A ∧
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos hm hr) hm hr A pivotInv)
            (maxEntryNorm_pos_of_det_ne_zero
              (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
              (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
                hm (fun i j a b => A i j a b) hPrefix)) ≤
          2 := by
  rcases
      higham13_algorithm13_3_exists_pivotInv_right_inverse_of_all_leadingBlockPrefixes
        A hPrefix with
    ⟨pivotInv, hPivotRight⟩
  have hDiagRight : ∀ j : Fin m,
      IsRightInverse r (A j j) (nonsingInv r (A j j)) := by
    intro j
    exact (isInverse_nonsingInv_of_det_ne_zero r (A j j) (hDiagDet j)).2
  refine ⟨pivotInv, ?_⟩
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_initial_diag_right_inverse_of_pivot_right_inverse_mixed_column_mass
      hm hr A pivotInv
      (maxEntryNorm_pos_of_det_ne_zero
        (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
        (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
          hm (fun i j a b => A i j a b) hPrefix))
      (fun j : Fin m => (infNorm (nonsingInv r (A j j)))⁻¹)
      (fun j : Fin m => nonsingInv r (A j j)) hDom (fun _ => le_rfl)
      hDiagRight hPivotRight

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    BDD all-leading-prefix data and certified active pivot right inverses supply
    the mixed matrix-`∞`/max-entry upper-factor and finite-history growth-factor
    bounds. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_mixed_column_mass
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockMaxNorm hm hr A ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 := by
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hDomPi :
      IsBlockDiagDomCol m
        (fun i j => ‖(fun a b => A i j a b : Fin r → Fin r → ℝ)‖)
        invDiagBound :=
    higham13_blockDiagDomCol_piNorm_of_infNorm hr A invDiagBound hDomInf
  have hDiagMax : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (A j j) := by
    intro j
    exact le_trans (hBound j) (maxEntryNorm_nonneg hr (A j j))
  have hInfDom :
      SchurStageActiveColumnDom13_7
        (fun k i j => infNorm
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
        (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv) := by
    simpa using
      (higham13_algorithm13_3_matrix_infNorm_active_column_dominance_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
        hr A pivotInv invDiagBound hPrefix hDomInf hBound hPivotRight)
  have hPivotBound :
      ∀ k : ℕ, ∀ hk : k < m,
        infNorm (pivotInv k) *
            higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv
              k ⟨k, hk⟩ ≤
          1 := by
    simpa using
      (higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_pivot_bound_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
        hr invDiagBound A pivotInv hPrefix hDomPi hBound hPivotRight)
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_mixed_column_mass
      hm hr A pivotInv hApos invDiagBound
      (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound A pivotInv)
      hDomInf hDiagMax hInfDom hPivotBound

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    first-Schur-tail canonical pivot data supplies the mixed matrix-`∞`/
    max-entry upper-factor and finite-history growth-factor bounds. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_mixed_column_mass
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
    higham13_algorithm13_3_pivot_right_inverse_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
      hr A pivotInv invDiagBound hPrefix hDomInf hBound hPivot0 hTailDet
      hTailPivotInv
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_mixed_column_mass
      (Nat.succ_pos m) hr A pivotInv hApos invDiagBound hPrefix hDomInf
      hBound hPivotRight

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    determinant-nonzero form of the BDD mixed matrix-`∞`/max-entry endpoint.

    The determinant hypothesis supplies only the positive denominator required
    by `growthFactorEntry`; the BDD and active pivot right-inverse data still
    drive the stage bound. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_det_ne_zero_of_mixed_column_mass
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
    (hDomInf : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockMaxNorm hm hr A ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet) ≤
        2 := by
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_mixed_column_mass
      hm hr A pivotInv
      (maxEntryNorm_pos_of_det_ne_zero
        (Nat.mul_pos hm hr) (blockMatrixFlatFin A) hdet)
      invDiagBound hPrefix hDomInf hBound hPivotRight

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    source-facing BDD mixed matrix-`∞`/max-entry endpoint from all-leading
    prefixes and certified active pivot right inverses.

    The all-leading-prefix table supplies the full-matrix determinant
    certificate needed only for the `growthFactorEntry` denominator. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockMaxNorm hm hr A ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
            (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
              hm (fun i j a b => A i j a b) hPrefix)) ≤
        2 := by
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_det_ne_zero_of_mixed_column_mass
      hm hr A pivotInv invDiagBound
      (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
        hm (fun i j a b => A i j a b) hPrefix)
      hPrefix hDomInf hBound hPivotRight

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    conditional BDD mixed matrix-`∞`/max-entry endpoint with the Algorithm
    13.3 pivot sequence constructed internally from all-leading-prefix
    nonsingularity.

    The conclusion produces both the recursive pivot table and the resulting
    upper-factor/growth estimates, removing the former external all-pivot
    right-inverse obligation from this surface.  The explicit auxiliary
    hypothesis `invDiagBound j ≤ 0` is stronger than the source's ordinary BDD
    data, so this wrapper is dependency progress and does not close the general
    source-strength BDD row. -/
theorem
    higham13_algorithm13_3_exists_pivotInv_eq13_21_eq13_23_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol m
      (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0) :
    ∃ pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ,
      blockMaxNorm hm hr
          (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
          2 * blockMaxNorm hm hr A ∧
        growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos hm hr) hm hr A pivotInv)
            (maxEntryNorm_pos_of_det_ne_zero
              (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
              (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
                hm (fun i j a b => A i j a b) hPrefix)) ≤
          2 := by
  rcases
      higham13_algorithm13_3_exists_pivotInv_right_inverse_of_all_leadingBlockPrefixes
        A hPrefix with
    ⟨pivotInv, hPivotRight⟩
  exact
    ⟨pivotInv,
      higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse
        hm hr A pivotInv invDiagBound hPrefix hDomInf hBound hPivotRight⟩

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    determinant-nonzero form of the BDD mixed endpoint with canonical
    first-Schur-tail pivot data. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_mixed_column_mass
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
        2 * blockMaxNorm (Nat.succ_pos m) hr A ∧
      growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A) hdet) ≤
        2 := by
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_mixed_column_mass
      hr A pivotInv
      (maxEntryNorm_pos_of_det_ne_zero
        (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A) hdet)
      invDiagBound hPrefix hDomInf hBound hPivot0 hTailDet hTailPivotInv

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    source-facing BDD mixed matrix-`∞`/max-entry endpoint with canonical
    first-Schur-tail pivot data.

    This removes the separate positivity proof artifact from the canonical-tail
    mixed endpoint; the remaining recursive obligation is the tail determinant
    and canonical `nonsingInv` table. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos
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
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_first_schur_tail_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_det_ne_zero_of_mixed_column_mass
      hr A pivotInv invDiagBound
      (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
        (Nat.succ_pos m) (fun i j a b => A i j a b) hPrefix)
      hPrefix hDomInf hBound hPivot0 hTailDet hTailPivotInv

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    the finite matrix-stage history growth factor satisfies `ρ_n <= 2` once
    the matrix-product Theorem 13.8 proof layer supplies active column
    dominance and a local Schur max-entry estimate. -/
theorem higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_local_schur_bound
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hActiveDom : SchurStageActiveColumnDom13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hLocal : SchurStageActiveLocalSchurBound13_8
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (fun k => maxEntryNorm hr (pivotInv k))) :
    growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
      2 := by
  exact
    higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_active_stage_bound
      hm hr A pivotInv hApos
      (higham13_algorithm13_3_matrix_active_stage_bound_of_local_schur_bound
        hm hr A pivotInv invDiagBound stageInvDiagBound hDom hDiagBound
        hActiveDom hPivotInvBound hLocal)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    source-strength conditional matrix-stage history growth-factor bridge from
    a dimension-free triple-product max-entry estimate and the diagonal
    lower-update layer. -/
theorem
    higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
      2 := by
  exact
    higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_active_stage_bound
      hm hr A pivotInv hApos
      (higham13_algorithm13_3_matrix_active_stage_bound_of_product_bound_diag_update
        hm hr A pivotInv invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
        hPivotInvBound hProduct hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table form of the product-bound/diagonal-update route to
    `rho_n <= 2`.

    The source table naturally records the active diagonal entry as the
    reciprocal of the pivot-inverse norm.  This wrapper converts that
    reciprocal equality into the scalar product bound required by the existing
    source-strength matrix-product bridge, leaving the structured triple-product
    estimate and diagonal-update table as the remaining source obligations. -/
theorem
    higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update_reciprocal
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
      2 := by
  exact
    higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
      hm hr A pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
      hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    paired matrix-stage package from the source-strength product-bound and
    diagonal-update route.

    The conclusion gives both the assembled upper-factor bound and the
    matrix-stage `rho <= 2` side condition for the same true matrix-product
    Algorithm 13.3 stages.  The dimension-free triple-product max-entry
    estimate remains an explicit hypothesis. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockMaxNorm hm hr A ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 := by
  have hActive :
      ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
            2 * blockMaxNorm hm hr A :=
    higham13_algorithm13_3_matrix_active_stage_bound_of_product_bound_diag_update
      hm hr A pivotInv invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hPivotInvBound hProduct hDiagUpdate
  have hC : 0 ≤ 2 * blockMaxNorm hm hr A :=
    mul_nonneg (by norm_num) (blockMaxNorm_nonneg hm hr A)
  exact
    ⟨higham13_algorithm13_3_upperFromMatrixStages_blockMaxNorm_bound_of_active_stage_bound
        hm hr A pivotInv hC hActive,
      higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hm hr A pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
        hInitInv hPivotInvBound hProduct hDiagUpdate⟩

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    reciprocal-table form of the paired matrix-stage product/update package.

    This accepts the source-style reciprocal pivot table and internally derives
    the pivot-product bound consumed by the source-strength product/update
    package.  The structured triple-product estimate and diagonal-update table
    remain explicit obligations. -/
theorem
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update_reciprocal
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    blockMaxNorm hm hr (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ≤
        2 * blockMaxNorm hm hr A ∧
      growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
        2 := by
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
      hm hr A pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
      hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    dimension-aware matrix-stage history growth-factor bridge.

    This closes the finite-history `ρ_n <= 2` side condition from active
    dominance and the strengthened `(r : ℝ)^2` pivot-inverse budget supplied by
    the proved max-entry matrix-product estimate.  The theorem is deliberately
    labelled as dimension-aware; the source-strength dimension-free route
    remains a separate open selected-scope obligation. -/
theorem higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_with_dim_factor
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hActiveDom : SchurStageActiveColumnDom13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      ((r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k)) *
          stageInvDiagBound k ⟨k, hk⟩ ≤
        1) :
    growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
      2 := by
  exact
    higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_active_stage_bound
      hm hr A pivotInv hApos
      (higham13_algorithm13_3_matrix_active_stage_bound_with_dim_factor
        hm hr A pivotInv invDiagBound stageInvDiagBound hDom hDiagBound
        hActiveDom hPivotInvBound)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    dimension-aware matrix-stage history growth-factor bridge from the
    diagonal lower-update layer.

    This is the proved `(r : ℝ)^2` route with the active-dominance premise
    discharged by the Theorem 13.7 induction wrapper above. -/
theorem
    higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_with_dim_factor_of_diag_update
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A))
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      ((r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k)) *
          stageInvDiagBound k ⟨k, hk⟩ ≤
        1)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => (r : ℝ) ^ 2 * maxEntryNorm hr (pivotInv k))) :
    growthFactorEntry (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hm hr) hm hr A pivotInv) hApos ≤
      2 := by
  exact
    higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_with_dim_factor
      hm hr A pivotInv hApos invDiagBound stageInvDiagBound hDom hDiagBound
      (higham13_algorithm13_3_matrix_active_column_dominance_with_dim_factor
        hr A pivotInv invDiagBound stageInvDiagBound hDom hInitInv
        hPivotInvBound hDiagUpdate)
      hPivotInvBound

end NumStability
