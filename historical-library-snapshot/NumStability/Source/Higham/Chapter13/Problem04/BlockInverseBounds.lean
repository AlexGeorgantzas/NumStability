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
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.GrowthBounds
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Lemma10.SchurComplement
import NumStability.Source.Higham.Chapter13.Problem04.LocalNormBounds
import NumStability.Source.Higham.Chapter13.Problem08

/-!
# Source.Higham.Chapter13.Problem04.BlockInverseBounds

This module formalizes the source-facing Chapter 13 statements for
`Problem04.BlockInverseBounds`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    parent first-split inverse entries are bounded by the canonical ambient
    `nonsingInv` max-entry norm.

    This packages the reindexing bridge between the displayed first-split
    `Matrix.fromBlocks` inverse and the flat source matrix used by the
    Eq.13.22/Eq.13.23 exact-`κ(A)` denominators. -/
theorem higham13_problem13_4_firstSplit_parent_inverse_entry_bound_from_nonsingInv
    {m r : ℕ} (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))] :
    ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
      |(⅟(Matrix.fromBlocks
          (blockMatrixFirstSplitA11 Ablk)
          (blockMatrixFirstSplitA12 Ablk)
          (blockMatrixFirstSplitA21 Ablk)
          (blockMatrixFirstSplitA22 Ablk)) :
        Matrix (Fin r ⊕ Fin ((m + 1) * r))
          (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤
        maxEntryNormRect hN hN
          (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk)) := by
  classical
  let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    blockMatrixFirstSplitFlat Ablk
  have hFull_eq :
      Matrix.fromBlocks
          (blockMatrixFirstSplitA11 Ablk)
          (blockMatrixFirstSplitA12 Ablk)
          (blockMatrixFirstSplitA21 Ablk)
          (blockMatrixFirstSplitA22 Ablk) =
        (fun i j : Fin r ⊕ Fin ((m + 1) * r) =>
          A0 (finSumFinEquiv i) (finSumFinEquiv j)) := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            simp [A0, blockMatrixFirstSplitA11, blockMatrixFirstSplitFlat]
        | inr j =>
            simp [A0, blockMatrixFirstSplitA12, blockMatrixFirstSplitFlat]
    | inr i =>
        cases j with
        | inl j =>
            simp [A0, blockMatrixFirstSplitA21, blockMatrixFirstSplitFlat]
        | inr j =>
            simp [A0, blockMatrixFirstSplitA22, blockMatrixFirstSplitFlat,
              blockMatrixFlatFin]
  simpa [A0] using
    (maxEntryNormRect_invOf_reindex_equiv_nonsingInv_entry_bound
      hN
      (finSumFinEquiv :
        (Fin r ⊕ Fin ((m + 1) * r)) ≃ Fin (r + (m + 1) * r))
      A0
      (Matrix.fromBlocks
        (blockMatrixFirstSplitA11 Ablk)
        (blockMatrixFirstSplitA12 Ablk)
        (blockMatrixFirstSplitA21 Ablk)
        (blockMatrixFirstSplitA22 Ablk))
      hFull_eq)

/-- The exact max-entry condition product for the first-split scalar matrix is
    bounded by the same product for the uniform flat representation. -/
theorem maxEntryNormRect_kappa_blockMatrixFirstSplitFlat_le_blockMatrixFlatFin
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitFlat A)] :
    maxEntryNormRect (Nat.add_pos_left hr (m * r)) (Nat.add_pos_left hr (m * r))
        (blockMatrixFirstSplitFlat A) *
      maxEntryNormRect (Nat.add_pos_left hr (m * r)) (Nat.add_pos_left hr (m * r))
        (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat A)) ≤
    maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
        (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A) *
      maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
        (Nat.mul_pos (Nat.succ_pos m) hr)
        (nonsingInv ((m + 1) * r) (blockMatrixFlatFin A)) := by
  let hSplit : 0 < r + m * r := Nat.add_pos_left hr (m * r)
  let hFlat : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
  have hAeq :
      maxEntryNormRect hSplit hSplit (blockMatrixFirstSplitFlat A) =
        maxEntryNormRect hFlat hFlat (blockMatrixFlatFin A) := by
    rw [maxEntryNormRect_eq_maxEntryNorm hSplit]
    rw [maxEntryNormRect_eq_maxEntryNorm hFlat]
    exact maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin hm hr A
  have hInv :=
    maxEntryNormRect_nonsingInv_blockMatrixFirstSplitFlat_le_blockMatrixFlatFin
      hr A
  have hFlatNonneg :
      0 ≤ maxEntryNormRect hFlat hFlat (blockMatrixFlatFin A) :=
    maxEntryNormRect_nonneg hFlat hFlat (blockMatrixFlatFin A)
  calc
    maxEntryNormRect hSplit hSplit (blockMatrixFirstSplitFlat A) *
        maxEntryNormRect hSplit hSplit
          (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat A))
        =
      maxEntryNormRect hFlat hFlat (blockMatrixFlatFin A) *
        maxEntryNormRect hSplit hSplit
          (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat A)) := by
        rw [hAeq]
    _ ≤ maxEntryNormRect hFlat hFlat (blockMatrixFlatFin A) *
        maxEntryNormRect hFlat hFlat
          (nonsingInv ((m + 1) * r) (blockMatrixFlatFin A)) := by
        exact mul_le_mul_of_nonneg_left hInv hFlatNonneg

/-- Determinant-nonzero variant of the first-split/uniform-flat exact
    condition-product bridge. -/
theorem
    maxEntryNormRect_kappa_blockMatrixFirstSplitFlat_le_blockMatrixFlatFin_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (hdet :
      Matrix.det (blockMatrixFirstSplitFlat A :
        Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ) ≠ 0) :
    maxEntryNormRect (Nat.add_pos_left hr (m * r)) (Nat.add_pos_left hr (m * r))
        (blockMatrixFirstSplitFlat A) *
      maxEntryNormRect (Nat.add_pos_left hr (m * r)) (Nat.add_pos_left hr (m * r))
        (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat A)) ≤
    maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
        (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A) *
      maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
        (Nat.mul_pos (Nat.succ_pos m) hr)
        (nonsingInv ((m + 1) * r) (blockMatrixFlatFin A)) := by
  let M : Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ :=
    blockMatrixFirstSplitFlat A
  letI : Invertible M :=
    Matrix.invertibleOfIsUnitDet (A := M) (isUnit_iff_ne_zero.mpr hdet)
  simpa [M] using
    maxEntryNormRect_kappa_blockMatrixFirstSplitFlat_le_blockMatrixFlatFin
      hm hr A

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    the first-split `Matrix.fromBlocks` view of a Schur tail is invertible
    whenever the scalar Schur-complement block is invertible.

    This is a representation bridge: it transports invertibility across the
    equality between the scalar Schur complement of the first-split flattening
    and the uniform flat matrix of the recursive block Schur tail. -/
noncomputable def higham13_problem13_4_schurTail_fromBlocks_invertible_of_schur_invertible
    {m r : ℕ}
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ)
    (A11_inv : Matrix (Fin r) (Fin r) ℝ)
    (Atail : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * A11_inv *
        blockMatrixFirstSplitA12 Ablk)]
    (hAtail : Atail = blockSchur Ablk A11_inv) :
    Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Atail)
      (blockMatrixFirstSplitA12 Atail)
      (blockMatrixFirstSplitA21 Atail)
      (blockMatrixFirstSplitA22 Atail)) := by
  classical
  have hflat :
      blockMatrixFlatFin Atail =
        blockMatrixFirstSplitA22 Ablk -
          blockMatrixFirstSplitA21 Ablk * A11_inv *
            blockMatrixFirstSplitA12 Ablk := by
    rw [hAtail, ← blockMatrixFirstSplit_schur_eq_blockMatrixFlatFin_blockSchur]
  letI : Invertible (blockMatrixFlatFin Atail) :=
    hflat.symm ▸
      (inferInstance : Invertible
        (blockMatrixFirstSplitA22 Ablk -
          blockMatrixFirstSplitA21 Ablk * A11_inv *
            blockMatrixFirstSplitA12 Ablk))
  exact blockMatrixFirstSplit_fromBlocks_invertible_of_blockMatrixFlatFin Atail

/-- Higham, 2nd ed., Chapter 13, Problems 13.4 and 13.8:
    the lower-right block of the full block inverse is the inverse of the
    `A₁₁` Schur complement `S = A₂₂ - A₂₁A₁₁⁻¹A₁₂`. -/
theorem higham13_problem13_4_Sinv_eq_full_inverse_lower_right_of_block_inverse
    {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]
    (A11 : Matrix r r ℝ) (A12 : Matrix r s ℝ)
    (A21 : Matrix s r ℝ) (A22 : Matrix s s ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)] :
    ⅟(A22 - A21 * ⅟A11 * A12) =
      fun i j => (⅟(Matrix.fromBlocks A11 A12 A21 A22)) (Sum.inr i) (Sum.inr j) := by
  ext i j
  have h := congr_fun (congr_fun
    (higham13_problem13_8_block_inverse A11 A12 A21 A22) (Sum.inr i)) (Sum.inr j)
  simpa [Matrix.fromBlocks] using h.symm

/-- Higham, 2nd ed., Chapter 13, Problems 13.4 and 13.8:
    entries of the displayed Schur-complement inverse inherit any entrywise
    max bound on the inverse of the parent block matrix.

    This is the pointwise form of the source step "the inverse of the Schur
    complement is the lower-right block of the full inverse".  It removes the
    need to pass that lower-right-block identity as a separate hypothesis in
    recursive max-entry source-comparison routes. -/
theorem higham13_problem13_4_Sinv_entry_bound_from_block_inverse
    {r s : ℕ}
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin s) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)]
    {normAinv : ℝ}
    (hAinv_entry : ∀ i j : Fin r ⊕ Fin s,
      |(⅟(Matrix.fromBlocks A11 A12 A21 A22) :
          Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ) i j| ≤ normAinv) :
    ∀ i j : Fin s,
      |(((⅟(A22 - A21 * ⅟A11 * A12)) :
          Matrix (Fin s) (Fin s) ℝ) i j)| ≤ normAinv := by
  intro i j
  have hSinv :
      ((⅟(A22 - A21 * ⅟A11 * A12)) :
          Matrix (Fin s) (Fin s) ℝ) =
        fun i j =>
          (⅟(Matrix.fromBlocks A11 A12 A21 A22) :
            Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ)
            (Sum.inr i) (Sum.inr j) :=
    higham13_problem13_4_Sinv_eq_full_inverse_lower_right_of_block_inverse
      A11 A12 A21 A22
  calc
    |(((⅟(A22 - A21 * ⅟A11 * A12)) :
          Matrix (Fin s) (Fin s) ℝ) i j)|
        = |(⅟(Matrix.fromBlocks A11 A12 A21 A22) :
            Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ)
            (Sum.inr i) (Sum.inr j)| := by
          rw [hSinv]
    _ ≤ normAinv := hAinv_entry (Sum.inr i) (Sum.inr j)

/-- Higham, 2nd ed., Chapter 13, Problems 13.4 and 13.8:
    max-entry form of
    `higham13_problem13_4_Sinv_entry_bound_from_block_inverse`. -/
theorem higham13_problem13_4_Sinv_maxEntryNormRect_from_block_inverse
    {r s : ℕ} (hs : 0 < s)
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin s) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)]
    {normAinv : ℝ}
    (hAinv_entry : ∀ i j : Fin r ⊕ Fin s,
      |(⅟(Matrix.fromBlocks A11 A12 A21 A22) :
          Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ) i j| ≤ normAinv) :
    maxEntryNormRect hs hs
        (((⅟(A22 - A21 * ⅟A11 * A12)) :
          Matrix (Fin s) (Fin s) ℝ)) ≤ normAinv :=
  maxEntryNormRect_le_of_entry_abs_le hs hs
    ((⅟(A22 - A21 * ⅟A11 * A12)) : Matrix (Fin s) (Fin s) ℝ)
    normAinv
    (higham13_problem13_4_Sinv_entry_bound_from_block_inverse
      A11 A12 A21 A22 hAinv_entry)

/-- Higham, 2nd ed., Chapter 13, Problems 13.4 and 13.8:
    first-split specialization of
    `higham13_problem13_4_Sinv_entry_bound_from_block_inverse`.

    This is the source-shaped form used by recursive block-LU routes: the
    Schur-complement inverse of the first block split inherits an entrywise max
    bound from the inverse of the displayed parent block matrix. -/
theorem higham13_problem13_4_firstSplit_Sinv_entry_bound_from_block_inverse
    {m r : ℕ}
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    {normAinv : ℝ}
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11 Ablk)
            (blockMatrixFirstSplitA12 Ablk)
            (blockMatrixFirstSplitA21 Ablk)
            (blockMatrixFirstSplitA22 Ablk)) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤ normAinv) :
    ∀ i j : Fin ((m + 1) * r),
      |(((⅟(blockMatrixFirstSplitA22 Ablk -
          blockMatrixFirstSplitA21 Ablk *
            ⅟(blockMatrixFirstSplitA11 Ablk) *
              blockMatrixFirstSplitA12 Ablk)) :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) i j)| ≤
        normAinv :=
  higham13_problem13_4_Sinv_entry_bound_from_block_inverse
    (blockMatrixFirstSplitA11 Ablk)
    (blockMatrixFirstSplitA12 Ablk)
    (blockMatrixFirstSplitA21 Ablk)
    (blockMatrixFirstSplitA22 Ablk)
    hAinv_entry

/-- Higham, 2nd ed., Chapter 13, Problems 13.4 and 13.8:
    max-entry first-split specialization of
    `higham13_problem13_4_firstSplit_Sinv_entry_bound_from_block_inverse`. -/
theorem higham13_problem13_4_firstSplit_Sinv_maxEntryNormRect_from_block_inverse
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    {normAinv : ℝ}
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11 Ablk)
            (blockMatrixFirstSplitA12 Ablk)
            (blockMatrixFirstSplitA21 Ablk)
            (blockMatrixFirstSplitA22 Ablk)) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤ normAinv) :
    maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
        (Nat.mul_pos (Nat.succ_pos m) hr)
        (((⅟(blockMatrixFirstSplitA22 Ablk -
          blockMatrixFirstSplitA21 Ablk *
            ⅟(blockMatrixFirstSplitA11 Ablk) *
              blockMatrixFirstSplitA12 Ablk)) :
          Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ)) ≤
      normAinv :=
  higham13_problem13_4_Sinv_maxEntryNormRect_from_block_inverse
    (Nat.mul_pos (Nat.succ_pos m) hr)
    (blockMatrixFirstSplitA11 Ablk)
    (blockMatrixFirstSplitA12 Ablk)
    (blockMatrixFirstSplitA21 Ablk)
    (blockMatrixFirstSplitA22 Ablk)
    hAinv_entry

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    recursive Schur-tail inverse-entry handoff from the parent block inverse.

    If the current first-split parent block inverse is entrywise bounded by the
    ambient inverse certificate, then the first-split inverse of its Schur tail
    inherits the same entrywise bound.  This combines the Problem 13.8
    lower-right block-inverse formula with the first-split/uniform-flat
    reindexing bridge, and is the direct inverse-entry propagation step needed
    by recursive Eq.13.22/Eq.13.23 source chains. -/
theorem
    higham13_problem13_4_firstSplit_schurTail_inverse_entry_bound_from_block_inverse
    {m r : ℕ}
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (A11_inv : Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Ablk)
      (blockMatrixFirstSplitA12 Ablk)
      (blockMatrixFirstSplitA21 Ablk)
      (blockMatrixFirstSplitA22 Ablk))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (blockSchur Ablk A11_inv))
      (blockMatrixFirstSplitA12
        (blockSchur Ablk A11_inv))
      (blockMatrixFirstSplitA21
        (blockSchur Ablk A11_inv))
      (blockMatrixFirstSplitA22
        (blockSchur Ablk A11_inv)))]
    (hA11_inv : A11_inv = ⅟(blockMatrixFirstSplitA11 Ablk))
    {normAinv : ℝ}
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11 Ablk)
            (blockMatrixFirstSplitA12 Ablk)
            (blockMatrixFirstSplitA21 Ablk)
            (blockMatrixFirstSplitA22 Ablk)) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤ normAinv) :
    ∀ i j : Fin r ⊕ Fin (m * r),
      |(⅟(Matrix.fromBlocks
          (blockMatrixFirstSplitA11
            (blockSchur Ablk A11_inv))
          (blockMatrixFirstSplitA12
            (blockSchur Ablk A11_inv))
          (blockMatrixFirstSplitA21
            (blockSchur Ablk A11_inv))
          (blockMatrixFirstSplitA22
            (blockSchur Ablk A11_inv)))) i j| ≤
        normAinv := by
  classical
  let Tail : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ :=
    blockSchur Ablk A11_inv
  let S : Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ :=
    blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk
  let Mtail : Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ :=
    Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Tail)
      (blockMatrixFirstSplitA12 Tail)
      (blockMatrixFirstSplitA21 Tail)
      (blockMatrixFirstSplitA22 Tail)
  let e : (Fin r ⊕ Fin (m * r)) ≃ Fin ((m + 1) * r) :=
    (finSumFinEquiv : (Fin r ⊕ Fin (m * r)) ≃ Fin (r + m * r)).trans
      (blockMatrixFirstSplitToFlatFinEquiv :
        Fin (r + m * r) ≃ Fin ((m + 1) * r))
  have hSinv_entry :
      ∀ i j : Fin ((m + 1) * r),
        |(⅟S : Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) i j| ≤
          normAinv := by
    simpa [S] using
      (higham13_problem13_4_firstSplit_Sinv_entry_bound_from_block_inverse
        (Ablk := Ablk) hAinv_entry)
  have hMtail :
      Mtail = fun i j : Fin r ⊕ Fin (m * r) => S (e i) (e j) := by
    ext i j
    have hFrom :
        Mtail i j =
          blockMatrixFirstSplitFlat Tail (finSumFinEquiv i) (finSumFinEquiv j) := by
      cases i with
      | inl i =>
          cases j with
          | inl j =>
              simp [Mtail, Tail, Matrix.fromBlocks, blockMatrixFirstSplitFlat,
                blockMatrixFirstSplitA11]
          | inr j =>
              simp [Mtail, Tail, Matrix.fromBlocks, blockMatrixFirstSplitFlat,
                blockMatrixFirstSplitA12]
      | inr i =>
          cases j with
          | inl j =>
              simp [Mtail, Tail, Matrix.fromBlocks, blockMatrixFirstSplitFlat,
                blockMatrixFirstSplitA21]
          | inr j =>
              simp [Mtail, Tail, Matrix.fromBlocks, blockMatrixFirstSplitFlat,
                blockMatrixFirstSplitA22, blockMatrixFlatFin]
    have hFlat := congr_fun (congr_fun
      (blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin_reindex Tail)
      (finSumFinEquiv i)) (finSumFinEquiv j)
    have hS :
        S = blockMatrixFlatFin Tail := by
      simpa [S, Tail, hA11_inv] using
        (blockMatrixFirstSplit_schur_eq_blockMatrixFlatFin_blockSchur
          Ablk (⅟(blockMatrixFirstSplitA11 Ablk)))
    calc
      Mtail i j =
          blockMatrixFirstSplitFlat Tail (finSumFinEquiv i) (finSumFinEquiv j) := hFrom
      _ = blockMatrixFlatFin Tail
          (blockMatrixFirstSplitToFlatFinEquiv (finSumFinEquiv i))
          (blockMatrixFirstSplitToFlatFinEquiv (finSumFinEquiv j)) := hFlat
      _ = S (e i) (e j) := by simp [e, hS]
  simpa [Mtail, Tail] using
    (invOf_entry_bound_of_reindex_eq e S Mtail hMtail hSinv_entry)

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    source max-entry lower-left solve bound from the Problem 13.8 block-inverse
    formula.

    The lower-left block of the full inverse is
    `-S⁻¹ A₂₁ A₁₁⁻¹`; multiplying by `S` gives
    `A₂₁ A₁₁⁻¹ = -S (A⁻¹)₂₁`.  Thus the growth certificate
    `||S|| <= ρ ||A||`, the full-inverse max-entry certificate, and the
    condition-number product imply the first inequality in Problem 13.4. -/
theorem higham13_problem13_4_A21A11inv_maxEntryNormRect_from_block_inverse_growth
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin s) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)]
    {normA normAinv rho kappaA : ℝ} (n : ℕ)
    (hRho : 0 ≤ rho) (hKappa : 0 ≤ kappaA)
    (hsn : (s : ℝ) ≤ (n : ℝ))
    (hS_entry : ∀ i : Fin s, ∀ j : Fin s,
      |(A22 - A21 * ⅟A11 * A12) i j| ≤ rho * normA)
    (hAinv_entry : ∀ i j : Fin r ⊕ Fin s,
      |(⅟(Matrix.fromBlocks A11 A12 A21 A22) :
          Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ) i j| ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappaA) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
      (n : ℝ) * rho * kappaA := by
  classical
  let S : Matrix (Fin s) (Fin s) ℝ := A22 - A21 * ⅟A11 * A12
  let Ainv21 : Matrix (Fin s) (Fin r) ℝ :=
    fun i j => (⅟(Matrix.fromBlocks A11 A12 A21 A22) :
      Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ) (Sum.inr i) (Sum.inl j)
  have hAinv21_formula :
      Ainv21 = (-(⅟S * A21 * ⅟A11) : Matrix (Fin s) (Fin r) ℝ) := by
    ext i j
    have h := congr_fun (congr_fun
      (higham13_problem13_8_block_inverse A11 A12 A21 A22)
      (Sum.inr i)) (Sum.inl j)
    simpa [S, Ainv21, Matrix.fromBlocks] using h
  have hprod_formula :
      (A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ) =
        (-(S * Ainv21) : Matrix (Fin s) (Fin r) ℝ) := by
    have hS_mul :
        S * Ainv21 =
          (-(A21 * ⅟A11) : Matrix (Fin s) (Fin r) ℝ) := by
      rw [hAinv21_formula]
      simp [Matrix.mul_assoc]
    rw [hS_mul]
    simp
  have hAbsBridge : ∀ i : Fin s, ∀ j : Fin r,
      |(A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ) i j| =
        |rectMatMul S Ainv21 i j| := by
    intro i j
    have h := congr_fun (congr_fun hprod_formula i) j
    calc
      |(A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ) i j|
          = |(-(S * Ainv21 : Matrix (Fin s) (Fin r) ℝ)) i j| := by
              rw [h]
      _ = |(S * Ainv21 : Matrix (Fin s) (Fin r) ℝ) i j| := by
              change |-((S * Ainv21 : Matrix (Fin s) (Fin r) ℝ) i j)| =
                |(S * Ainv21 : Matrix (Fin s) (Fin r) ℝ) i j|
              rw [abs_neg]
      _ = |rectMatMul S Ainv21 i j| := by
              simp [rectMatMul, Matrix.mul_apply]
  have hBridgeNorm :
      maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
        maxEntryNormRect hs hr (rectMatMul S Ainv21) := by
    apply maxEntryNormRect_le_of_entry_abs_le
    intro i j
    rw [hAbsBridge i j]
    exact entry_le_maxEntryNormRect hs hr (rectMatMul S Ainv21) i j
  have hProduct :
      maxEntryNormRect hs hr (rectMatMul S Ainv21) ≤
        (s : ℝ) * maxEntryNormRect hs hs S * maxEntryNormRect hs hr Ainv21 :=
    maxEntryNormRect_rectMatMul_le hs hs hr S Ainv21
  have hS_bound :
      maxEntryNormRect hs hs S ≤ rho * normA := by
    apply maxEntryNormRect_le_of_entry_abs_le
    intro i j
    exact hS_entry i j
  have hAinv21_bound :
      maxEntryNormRect hs hr Ainv21 ≤ normAinv := by
    apply maxEntryNormRect_le_of_entry_abs_le
    intro i j
    exact hAinv_entry (Sum.inr i) (Sum.inl j)
  have hAinv21_nonneg : 0 ≤ maxEntryNormRect hs hr Ainv21 :=
    maxEntryNormRect_nonneg hs hr Ainv21
  have hSupper_nonneg : 0 ≤ rho * normA :=
    le_trans (maxEntryNormRect_nonneg hs hs S) hS_bound
  have hNormProduct :
      maxEntryNormRect hs hs S * maxEntryNormRect hs hr Ainv21 ≤
        rho * kappaA := by
    have hmul :
        maxEntryNormRect hs hs S * maxEntryNormRect hs hr Ainv21 ≤
          (rho * normA) * normAinv :=
      mul_le_mul hS_bound hAinv21_bound hAinv21_nonneg hSupper_nonneg
    calc
      maxEntryNormRect hs hs S * maxEntryNormRect hs hr Ainv21
          ≤ (rho * normA) * normAinv := hmul
      _ = rho * (normA * normAinv) := by ring
      _ ≤ rho * kappaA := mul_le_mul_of_nonneg_left hkappa hRho
  have hScaleS :
      (s : ℝ) * maxEntryNormRect hs hs S * maxEntryNormRect hs hr Ainv21 ≤
        (s : ℝ) * (rho * kappaA) := by
    calc
      (s : ℝ) * maxEntryNormRect hs hs S * maxEntryNormRect hs hr Ainv21 =
          (s : ℝ) *
            (maxEntryNormRect hs hs S * maxEntryNormRect hs hr Ainv21) := by ring
      _ ≤ (s : ℝ) * (rho * kappaA) :=
          mul_le_mul_of_nonneg_left hNormProduct (Nat.cast_nonneg s)
  have hScaleN :
      (s : ℝ) * (rho * kappaA) ≤ (n : ℝ) * (rho * kappaA) :=
    mul_le_mul_of_nonneg_right hsn (mul_nonneg hRho hKappa)
  calc
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ))
        ≤ maxEntryNormRect hs hr (rectMatMul S Ainv21) := hBridgeNorm
    _ ≤ (s : ℝ) * maxEntryNormRect hs hs S * maxEntryNormRect hs hr Ainv21 :=
        hProduct
    _ ≤ (s : ℝ) * (rho * kappaA) := hScaleS
    _ ≤ (n : ℝ) * (rho * kappaA) := hScaleN
    _ = (n : ℝ) * rho * kappaA := by ring

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 feeding equation (13.22):
    ambient lower-left block budget from the block-inverse proof route.

    The source proof of Problem 13.4 first gives
    `‖A₂₁ A₁₁⁻¹‖_max <= n ρ κ(A)` from the Schur-growth certificate and a
    full-inverse entry certificate.  Since the Gaussian-elimination growth
    factor is at least one in the ambient source history, this immediately
    supplies the Eq.13.22 lower-factor budget `n ρ² κ(A)`.

    In recursive uses, `A11,A12,A21,A22` may be the current Schur tail.  The
    hypothesis `hAinv_entry` is deliberately explicit: it is the remaining
    source certificate identifying the current tail inverse entries with
    entries bounded by the original inverse. -/
theorem higham13_problem13_4_L21_eq13_22_premise_from_ambient_block_inverse_growth
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin s) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)]
    {normA normAinv rho kappaA : ℝ} (n : ℕ)
    (hRho_ge_one : 1 ≤ rho) (hKappa : 0 ≤ kappaA)
    (hsn : (s : ℝ) ≤ (n : ℝ))
    (hS_entry : ∀ i : Fin s, ∀ j : Fin s,
      |(A22 - A21 * ⅟A11 * A12) i j| ≤ rho * normA)
    (hAinv_entry : ∀ i j : Fin r ⊕ Fin s,
      |(⅟(Matrix.fromBlocks A11 A12 A21 A22) :
          Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ) i j| ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappaA) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
      (n : ℝ) * rho ^ 2 * kappaA := by
  have hRho_nonneg : 0 ≤ rho := le_trans zero_le_one hRho_ge_one
  have hBase :
      maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
        (n : ℝ) * rho * kappaA :=
    higham13_problem13_4_A21A11inv_maxEntryNormRect_from_block_inverse_growth
      hr hs A11 A12 A21 A22 n hRho_nonneg hKappa hsn hS_entry
      hAinv_entry hkappa
  have hrho_le_sq : rho ≤ rho ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hRho_ge_one hRho_nonneg
    simpa [pow_two] using hmul
  have hscale :
      (n : ℝ) * rho * kappaA ≤ (n : ℝ) * rho ^ 2 * kappaA := by
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrho_le_sq hn_nonneg) hKappa
  exact le_trans hBase hscale

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 feeding equation (13.22):
    global-growth-tableau form of the ambient lower-left block budget.

    This is the recursive source shape suggested by the printed argument:
    `rho` is the growth factor of one ambient GE history, `hS_le_G` says the
    next Schur complement is contained in that global history, and
    `hAinv_entry` says the current tail inverse entries are bounded by the
    ambient inverse norm.  No local Schur-complement growth factor appears in
    the conclusion. -/
theorem
    higham13_problem13_4_L21_eq13_22_premise_from_global_growth_tableau_exact_kappa
    {r s N : ℕ} (hr : 0 < r) (hs : 0 < s) (hN : 0 < N)
    (Aglob Gglob AinvGlob : Fin N → Fin N → ℝ)
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin s) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)]
    (hApos : 0 < maxEntryNorm hN Aglob)
    (n : ℕ) (hsn : (s : ℝ) ≤ (n : ℝ))
    (hA_le_G : maxEntryNorm hN Aglob ≤ maxEntryNorm hN Gglob)
    (hS_le_G :
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) ≤
        maxEntryNorm hN Gglob)
    (hAinv_entry : ∀ i j : Fin r ⊕ Fin s,
      |(⅟(Matrix.fromBlocks A11 A12 A21 A22) :
          Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ) i j| ≤
        maxEntryNormRect hN hN AinvGlob) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
      (n : ℝ) *
        (growthFactorEntry hN Aglob Gglob hApos) ^ 2 *
        (maxEntryNormRect hN hN Aglob *
          maxEntryNormRect hN hN AinvGlob) := by
  let rho : ℝ := growthFactorEntry hN Aglob Gglob hApos
  let kappaA : ℝ :=
    maxEntryNormRect hN hN Aglob * maxEntryNormRect hN hN AinvGlob
  have hRho_ge_one : 1 ≤ rho := by
    simpa [rho] using
      growthFactorEntry_ge_one_of_maxEntryNorm_le hN Aglob Gglob hApos hA_le_G
  have hKappa : 0 ≤ kappaA := by
    exact mul_nonneg (maxEntryNormRect_nonneg hN hN Aglob)
      (maxEntryNormRect_nonneg hN hN AinvGlob)
  have hS_growth :
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) ≤
        rho * maxEntryNormRect hN hN Aglob := by
    calc
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12)
          ≤ maxEntryNorm hN Gglob := hS_le_G
      _ = rho * maxEntryNormRect hN hN Aglob := by
          rw [maxEntryNormRect_eq_maxEntryNorm hN Aglob]
          unfold rho growthFactorEntry
          exact (div_mul_cancel₀ (maxEntryNorm hN Gglob) (ne_of_gt hApos)).symm
  have hS_entry : ∀ i : Fin s, ∀ j : Fin s,
      |(A22 - A21 * ⅟A11 * A12) i j| ≤
        rho * maxEntryNormRect hN hN Aglob := by
    intro i j
    exact le_trans
      (entry_le_maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) i j)
      hS_growth
  simpa [rho, kappaA] using
    higham13_problem13_4_L21_eq13_22_premise_from_ambient_block_inverse_growth
      hr hs A11 A12 A21 A22 n hRho_ge_one hKappa hsn hS_entry
      hAinv_entry (le_rfl :
        maxEntryNormRect hN hN Aglob * maxEntryNormRect hN hN AinvGlob ≤
          kappaA)

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 feeding equation (13.22):
    source-indexed global-growth-tableau lower-left block budget.

    This specializes
    `higham13_problem13_4_L21_eq13_22_premise_from_global_growth_tableau_exact_kappa`
    to a source `Fin (r+s)` matrix and the repository canonical inverse
    `nonsingInv`.  The block-identification hypotheses provide the exact
    reindexing certificate, so the only remaining mathematical assumptions are
    the ambient growth-tableau containments for the initial matrix and the
    current Schur complement. -/
theorem
    higham13_problem13_4_L21_eq13_22_premise_from_source_global_growth_tableau_exact_kappa
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hN : 0 < r + s)
    (A G : Fin (r + s) → Fin (r + s) → ℝ)
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
    (n : ℕ) (hsn : (s : ℝ) ≤ (n : ℝ))
    (hA_le_G : maxEntryNorm hN A ≤ maxEntryNorm hN G)
    (hS_le_G :
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) ≤
        maxEntryNorm hN G) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
      (n : ℝ) * (growthFactorEntry hN A G hApos) ^ 2 *
        (maxEntryNormRect hN hN A *
          maxEntryNormRect hN hN (nonsingInv (r + s) A)) := by
  classical
  have hFull :
      Matrix.fromBlocks A11 A12 A21 A22 =
        (fun i j : Fin r ⊕ Fin s =>
          A (finSumFinEquiv i) (finSumFinEquiv j)) := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            have h := congr_fun (congr_fun hA11_block i) j
            simpa [Matrix.fromBlocks] using h
        | inr j =>
            have h := congr_fun (congr_fun hA12_block i) j
            simpa [Matrix.fromBlocks] using h
    | inr i =>
        cases j with
        | inl j =>
            have h := congr_fun (congr_fun hA21_block i) j
            simpa [Matrix.fromBlocks] using h
        | inr j =>
            have h := congr_fun (congr_fun hA22_block i) j
            simpa [Matrix.fromBlocks] using h
  have hAinv_entry :
      ∀ i j : Fin r ⊕ Fin s,
        |(⅟(Matrix.fromBlocks A11 A12 A21 A22) :
          Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ) i j| ≤
            maxEntryNormRect hN hN (nonsingInv (r + s) A) :=
    maxEntryNormRect_invOf_reindex_equiv_nonsingInv_entry_bound
      hN (finSumFinEquiv : (Fin r ⊕ Fin s) ≃ Fin (r + s))
      A (Matrix.fromBlocks A11 A12 A21 A22) hFull
  exact
    higham13_problem13_4_L21_eq13_22_premise_from_global_growth_tableau_exact_kappa
      hr hs hN A G (nonsingInv (r + s) A)
      A11 A12 A21 A22 hApos n hsn hA_le_G hS_le_G hAinv_entry

/-- Higham, 2nd ed., Chapter 13, Lemma 13.10 / Problem 13.4 dependency:
    the inverse of the Schur complement inherits an operator-2 certificate from
    the lower-right block of the full block inverse.

    The mathematical content is the Problem 13.8 block-inverse formula plus the
    generic principal-submatrix operator certificate. -/
theorem higham13_problem13_4_Sinv_finiteOpNorm2Le_from_block_inverse
    {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]
    (A11 : Matrix r r ℝ) (A12 : Matrix r s ℝ)
    (A21 : Matrix s r ℝ) (A22 : Matrix s s ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)]
    {normAinv : ℝ}
    (hAinv : finiteOpNorm2Le
      (fun i j : r ⊕ s =>
        (⅟(Matrix.fromBlocks A11 A12 A21 A22) :
          Matrix (r ⊕ s) (r ⊕ s) ℝ) i j)
      normAinv) :
    finiteOpNorm2Le
      (fun i j : s =>
        (⅟(A22 - A21 * ⅟A11 * A12) : Matrix s s ℝ) i j)
      normAinv := by
  classical
  have hprincipal :=
    finiteOpNorm2Le_sumInr_principal
      (fun i j : r ⊕ s =>
        (⅟(Matrix.fromBlocks A11 A12 A21 A22) :
          Matrix (r ⊕ s) (r ⊕ s) ℝ) i j)
      hAinv
  have hSinv :=
    higham13_problem13_4_Sinv_eq_full_inverse_lower_right_of_block_inverse
      A11 A12 A21 A22
  simpa [hSinv] using hprincipal

/-- Higham, 2nd ed., Chapter 13, Lemma 13.10 / Problem 13.4 dependency:
    source-indexed version of the Schur-inverse operator-2 certificate.

    Once the displayed block matrix is identified with the `finSumFinEquiv`
    reindexing of a source `Fin (r+s)` matrix, the full-inverse certificate is
    supplied by the exact norm of the canonical repository inverse
    `nonsingInv (r+s) A`. -/
theorem higham13_problem13_4_Sinv_finiteOpNorm2Le_from_source_block_inverse
    {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ)
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
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s))) :
    finiteOpNorm2Le
      (fun i j : Fin s =>
        (⅟(A22 - A21 * ⅟A11 * A12) : Matrix (Fin s) (Fin s) ℝ) i j)
      (opNorm2 (nonsingInv (r + s) A)) := by
  classical
  have hFull :
      Matrix.fromBlocks A11 A12 A21 A22 =
        (fun i j : Fin r ⊕ Fin s =>
          A (finSumFinEquiv i) (finSumFinEquiv j)) := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            have h := congr_fun (congr_fun hA11_block i) j
            simpa [Matrix.fromBlocks] using h
        | inr j =>
            have h := congr_fun (congr_fun hA12_block i) j
            simpa [Matrix.fromBlocks] using h
    | inr i =>
        cases j with
        | inl j =>
            have h := congr_fun (congr_fun hA21_block i) j
            simpa [Matrix.fromBlocks] using h
        | inr j =>
            have h := congr_fun (congr_fun hA22_block i) j
            simpa [Matrix.fromBlocks] using h
  have hAinv :
      finiteOpNorm2Le
        (fun i j : Fin r ⊕ Fin s =>
          (⅟(Matrix.fromBlocks A11 A12 A21 A22) :
            Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ) i j)
        (opNorm2 (nonsingInv (r + s) A)) :=
    finiteOpNorm2Le_invOf_reindex_equiv_nonsingInv
      (e := (finSumFinEquiv : (Fin r ⊕ Fin s) ≃ Fin (r + s)))
      A (Matrix.fromBlocks A11 A12 A21 A22) hFull
  exact
    higham13_problem13_4_Sinv_finiteOpNorm2Le_from_block_inverse
      A11 A12 A21 A22 hAinv

/-- Higham, 2nd ed., Chapter 13, Lemma 13.10 / Problem 13.4 dependency:
    positive definiteness of the displayed SPD block matrix supplies the
    constructive inverse instances needed by the source-block Schur-inverse
    operator certificate.

    This removes the local `Invertible` assumptions from
    `higham13_problem13_4_Sinv_finiteOpNorm2Le_from_source_block_inverse` when
    the source partition is already known to be positive definite. -/
theorem higham13_problem13_4_Sinv_finiteOpNorm2Le_from_source_posDef_block_inverse
    {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    (hFull : (Matrix.fromBlocks A11 A21ᵀ A21 A22).PosDef)
    (hA11_block : A11 =
      fun i j : Fin r =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA12_block : A21ᵀ =
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
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s))) :
    finiteOpNorm2Le
      (fun i j : Fin s =>
        ((A22 - A21 * A11⁻¹ * A21ᵀ)⁻¹ :
          Matrix (Fin s) (Fin s) ℝ) i j)
      (opNorm2 (nonsingInv (r + s) A)) := by
  classical
  have hFullHerm :
      (Matrix.fromBlocks A11 A21ᵀ (A21ᵀ)ᴴ A22).PosDef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hFull
  have hA11pos : A11.PosDef :=
    higham13_spd_leadingBlock_posDef A11 A21ᵀ A22 hFullHerm
  letI : Invertible A11 := hA11pos.isUnit.invertible
  letI : Invertible (Matrix.fromBlocks A11 A21ᵀ A21 A22) :=
    hFull.isUnit.invertible
  have hSpos :
      (A22 - A21 * ⅟A11 * A21ᵀ).PosDef := by
    have h := higham13_spd_schurComplement_source_posDef A11 A21 A22 hFull
    simpa using h
  letI : Invertible (A22 - A21 * ⅟A11 * A21ᵀ) :=
    hSpos.isUnit.invertible
  have hcert :=
    higham13_problem13_4_Sinv_finiteOpNorm2Le_from_source_block_inverse
      A A11 A21ᵀ A21 A22
      hA11_block hA12_block hA21_block hA22_block
  simpa using hcert

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    Schur-complement max-entry condition-product bridge with the `S⁻¹`
    certificate derived from the Problem 13.8 block inverse formula. -/
theorem higham13_problem13_4_schur_kappa_maxEntryNormRect_from_block_inverse
    {r s : ℕ} (hs : 0 < s)
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin s) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)]
    {normA normAinv rho kappaA : ℝ}
    (hRho : 0 ≤ rho)
    (hS_entry : ∀ i : Fin s, ∀ j : Fin s,
      |(A22 - A21 * ⅟A11 * A12) i j| ≤ rho * normA)
    (hAinv_entry : ∀ i j : Fin r ⊕ Fin s,
      |(⅟(Matrix.fromBlocks A11 A12 A21 A22) :
          Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ) i j| ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappaA) :
    maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) *
        maxEntryNormRect hs hs
          ((⅟(A22 - A21 * ⅟A11 * A12)) : Matrix (Fin s) (Fin s) ℝ) ≤
      rho * kappaA :=
  higham13_problem13_4_schur_kappa_maxEntryNormRect_from_full_inverse_entry_bound
    hs ((⅟(Matrix.fromBlocks A11 A12 A21 A22)) :
      Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ)
    (A22 - A21 * ⅟A11 * A12)
    ((⅟(A22 - A21 * ⅟A11 * A12)) : Matrix (Fin s) (Fin s) ℝ)
    hRho hS_entry hAinv_entry
    (higham13_problem13_4_Sinv_eq_full_inverse_lower_right_of_block_inverse
      A11 A12 A21 A22)
    hkappa

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    paired source max-entry bounds from the block-inverse proof route.

    Given the growth-factor certificate `||S|| <= ρ_n ||A||`, the entrywise
    max certificate for the full inverse, and the condition-number product
    `||A|| ||A⁻¹|| <= κ(A)`, this theorem proves both displayed inequalities
    in the exercise:
    `||A₂₁ A₁₁⁻¹|| <= n ρ_n κ(A)` and
    `κ(S) <= ρ_n κ(A)` in the chapter's max-entry norm. -/
theorem higham13_problem13_4_maxEntry_bounds_from_block_inverse_growth
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin s) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)]
    {normA normAinv rho kappaA : ℝ} (n : ℕ)
    (hRho : 0 ≤ rho) (hKappa : 0 ≤ kappaA)
    (hsn : (s : ℝ) ≤ (n : ℝ))
    (hS_entry : ∀ i : Fin s, ∀ j : Fin s,
      |(A22 - A21 * ⅟A11 * A12) i j| ≤ rho * normA)
    (hAinv_entry : ∀ i j : Fin r ⊕ Fin s,
      |(⅟(Matrix.fromBlocks A11 A12 A21 A22) :
          Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ) i j| ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappaA) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
        (n : ℝ) * rho * kappaA ∧
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) *
          maxEntryNormRect hs hs
            ((⅟(A22 - A21 * ⅟A11 * A12)) : Matrix (Fin s) (Fin s) ℝ) ≤
        rho * kappaA := by
  constructor
  · exact
      higham13_problem13_4_A21A11inv_maxEntryNormRect_from_block_inverse_growth
        hr hs A11 A12 A21 A22 n hRho hKappa hsn hS_entry hAinv_entry hkappa
  · exact
      higham13_problem13_4_schur_kappa_maxEntryNormRect_from_block_inverse
        hs A11 A12 A21 A22 hRho hS_entry hAinv_entry hkappa

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    source-indexed max-entry block-inverse route.

    Once the displayed block matrix is identified with the standard
    `finSumFinEquiv` reindexing of a source `Fin (r+s)` matrix, the full
    inverse max-entry certificate is supplied by the canonical repository
    inverse `nonsingInv (r+s) A`.  The remaining hypotheses are exactly the
    source growth certificate for the Schur complement and the max-entry
    condition-product certificate. -/
theorem higham13_problem13_4_maxEntry_bounds_from_source_block_inverse_growth
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hN : 0 < r + s)
    (A : Fin (r + s) → Fin (r + s) → ℝ)
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
    {rho kappaA : ℝ} (n : ℕ)
    (hRho : 0 ≤ rho)
    (hsn : (s : ℝ) ≤ (n : ℝ))
    (hS_entry : ∀ i : Fin s, ∀ j : Fin s,
      |(A22 - A21 * ⅟A11 * A12) i j| ≤
        rho * maxEntryNormRect hN hN A)
    (hkappa :
      maxEntryNormRect hN hN A *
          maxEntryNormRect hN hN (nonsingInv (r + s) A) ≤ kappaA) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
        (n : ℝ) * rho * kappaA ∧
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) *
          maxEntryNormRect hs hs
            ((⅟(A22 - A21 * ⅟A11 * A12)) : Matrix (Fin s) (Fin s) ℝ) ≤
        rho * kappaA := by
  classical
  have hFull :
      Matrix.fromBlocks A11 A12 A21 A22 =
        (fun i j : Fin r ⊕ Fin s =>
          A (finSumFinEquiv i) (finSumFinEquiv j)) := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            have h := congr_fun (congr_fun hA11_block i) j
            simpa [Matrix.fromBlocks] using h
        | inr j =>
            have h := congr_fun (congr_fun hA12_block i) j
            simpa [Matrix.fromBlocks] using h
    | inr i =>
        cases j with
        | inl j =>
            have h := congr_fun (congr_fun hA21_block i) j
            simpa [Matrix.fromBlocks] using h
        | inr j =>
            have h := congr_fun (congr_fun hA22_block i) j
            simpa [Matrix.fromBlocks] using h
  have hAinv_entry :
      ∀ i j : Fin r ⊕ Fin s,
        |(⅟(Matrix.fromBlocks A11 A12 A21 A22) :
          Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ) i j| ≤
            maxEntryNormRect hN hN (nonsingInv (r + s) A) :=
    maxEntryNormRect_invOf_reindex_equiv_nonsingInv_entry_bound
      hN (finSumFinEquiv : (Fin r ⊕ Fin s) ≃ Fin (r + s))
      A (Matrix.fromBlocks A11 A12 A21 A22) hFull
  have hKappa_nonneg : 0 ≤ kappaA :=
    le_trans
      (mul_nonneg (maxEntryNormRect_nonneg hN hN A)
        (maxEntryNormRect_nonneg hN hN (nonsingInv (r + s) A)))
      hkappa
  exact
    higham13_problem13_4_maxEntry_bounds_from_block_inverse_growth
      hr hs A11 A12 A21 A22 n hRho hKappa_nonneg hsn hS_entry
      hAinv_entry hkappa

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    source-indexed max-entry block-inverse route with the condition number
    represented by the exact product `||A||_max ||A⁻¹||_max`.

    This discharges the condition-product certificate in
    `higham13_problem13_4_maxEntry_bounds_from_source_block_inverse_growth`.
    The remaining mathematical source obligation is the Schur-growth
    certificate `||S||_max <= rho * ||A||_max`. -/
theorem higham13_problem13_4_maxEntry_bounds_from_source_block_inverse_growth_exact_kappa
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hN : 0 < r + s)
    (A : Fin (r + s) → Fin (r + s) → ℝ)
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
    {rho : ℝ} (n : ℕ)
    (hRho : 0 ≤ rho)
    (hsn : (s : ℝ) ≤ (n : ℝ))
    (hS_entry : ∀ i : Fin s, ∀ j : Fin s,
      |(A22 - A21 * ⅟A11 * A12) i j| ≤
        rho * maxEntryNormRect hN hN A) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
        (n : ℝ) * rho *
          (maxEntryNormRect hN hN A *
            maxEntryNormRect hN hN (nonsingInv (r + s) A)) ∧
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) *
          maxEntryNormRect hs hs
            ((⅟(A22 - A21 * ⅟A11 * A12)) : Matrix (Fin s) (Fin s) ℝ) ≤
        rho *
          (maxEntryNormRect hN hN A *
            maxEntryNormRect hN hN (nonsingInv (r + s) A)) :=
  higham13_problem13_4_maxEntry_bounds_from_source_block_inverse_growth
    hr hs hN A A11 A12 A21 A22
    hA11_block hA12_block hA21_block hA22_block
    (rho := rho)
    (kappaA :=
      maxEntryNormRect hN hN A *
        maxEntryNormRect hN hN (nonsingInv (r + s) A))
    n hRho hsn hS_entry le_rfl

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    source-indexed max-entry route from the norm-level Schur-growth certificate
    used in the book.

    This is the source-shaped form of the exact-κ wrapper: it assumes
    `||S||_max <= rho * ||A||_max`, derives the required entrywise Schur
    certificate from the definition of `maxEntryNormRect`, and then applies
    `higham13_problem13_4_maxEntry_bounds_from_source_block_inverse_growth_exact_kappa`.
    The remaining mathematical source obligation is now exactly the norm-level
    Schur-growth statement. -/
theorem higham13_problem13_4_maxEntry_bounds_from_source_schur_growth_exact_kappa
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hN : 0 < r + s)
    (A : Fin (r + s) → Fin (r + s) → ℝ)
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
    {rho : ℝ} (n : ℕ)
    (hRho : 0 ≤ rho)
    (hsn : (s : ℝ) ≤ (n : ℝ))
    (hS_growth :
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) ≤
        rho * maxEntryNormRect hN hN A) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
        (n : ℝ) * rho *
          (maxEntryNormRect hN hN A *
            maxEntryNormRect hN hN (nonsingInv (r + s) A)) ∧
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) *
          maxEntryNormRect hs hs
            ((⅟(A22 - A21 * ⅟A11 * A12)) : Matrix (Fin s) (Fin s) ℝ) ≤
        rho *
          (maxEntryNormRect hN hN A *
            maxEntryNormRect hN hN (nonsingInv (r + s) A)) := by
  have hS_entry : ∀ i : Fin s, ∀ j : Fin s,
      |(A22 - A21 * ⅟A11 * A12) i j| ≤
        rho * maxEntryNormRect hN hN A := by
    intro i j
    exact le_trans
      (entry_le_maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) i j)
      hS_growth
  exact
    higham13_problem13_4_maxEntry_bounds_from_source_block_inverse_growth_exact_kappa
      hr hs hN A A11 A12 A21 A22
      hA11_block hA12_block hA21_block hA22_block
      n hRho hsn hS_entry

/-- Higham, 2nd ed., Chapter 13, equation (13.22) nonvacuity support:
    the exact max-entry condition product makes the lower-factor diagonal
    budget at least one.

    If `Ainv` is a right inverse of `A`, the growth object contains the initial
    matrix, and the displayed scalar dimension `n` dominates the matrix
    dimension `N`, then
    `1 <= n * ρ^2 * (‖A‖_max ‖Ainv‖_max)`. -/
theorem higham13_eq13_22_lower_diagonal_budget_from_right_inverse_growth
    {N : ℕ} (hN : 0 < N)
    (A G Ainv : Fin N → Fin N → ℝ)
    (hApos : 0 < maxEntryNorm hN A)
    (hRight : IsRightInverse N A Ainv)
    (n : ℕ)
    (hNn : (N : ℝ) ≤ (n : ℝ))
    (hA_le_G : maxEntryNorm hN A ≤ maxEntryNorm hN G) :
    1 ≤ (n : ℝ) * (growthFactorEntry hN A G hApos) ^ 2 *
      (maxEntryNormRect hN hN A * maxEntryNormRect hN hN Ainv) := by
  let rho : ℝ := growthFactorEntry hN A G hApos
  let kappaA : ℝ := maxEntryNormRect hN hN A * maxEntryNormRect hN hN Ainv
  have hkappa_nonneg : 0 ≤ kappaA := by
    exact mul_nonneg (maxEntryNormRect_nonneg hN hN A)
      (maxEntryNormRect_nonneg hN hN Ainv)
  have hbase : 1 ≤ (N : ℝ) * kappaA := by
    simpa [kappaA, mul_assoc] using
      one_le_dim_mul_maxEntryNormRect_mul_of_isRightInverse hN A Ainv hRight
  have hrho_ge_one : 1 ≤ rho := by
    simpa [rho] using
      growthFactorEntry_ge_one_of_maxEntryNorm_le hN A G hApos hA_le_G
  have hrho_nonneg : 0 ≤ rho := le_trans zero_le_one hrho_ge_one
  have hrho_sq_ge_one : 1 ≤ rho ^ 2 := by
    have hmul := mul_le_mul hrho_ge_one hrho_ge_one zero_le_one hrho_nonneg
    simpa [pow_two] using hmul
  have hcoef : (N : ℝ) ≤ (n : ℝ) * rho ^ 2 := by
    calc
      (N : ℝ) ≤ (n : ℝ) := hNn
      _ = (n : ℝ) * 1 := by ring
      _ ≤ (n : ℝ) * rho ^ 2 :=
        mul_le_mul_of_nonneg_left hrho_sq_ge_one (Nat.cast_nonneg n)
  have hbudget :
      (N : ℝ) * kappaA ≤ ((n : ℝ) * rho ^ 2) * kappaA :=
    mul_le_mul_of_nonneg_right hcoef hkappa_nonneg
  calc
    (1 : ℝ) ≤ (N : ℝ) * kappaA := hbase
    _ ≤ ((n : ℝ) * rho ^ 2) * kappaA := hbudget
    _ = (n : ℝ) * rho ^ 2 * kappaA := by ring
    _ = (n : ℝ) * (growthFactorEntry hN A G hApos) ^ 2 *
        (maxEntryNormRect hN hN A * maxEntryNormRect hN hN Ainv) := by
        simp [rho, kappaA]

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    source-indexed exact-κ bounds with `rho` instantiated as the formal
    max-entry growth factor.

    This specializes
    `higham13_problem13_4_maxEntry_bounds_from_source_schur_growth_exact_kappa`
    by deriving the source Schur-growth premise from `growthFactorEntry`.
    The remaining mathematical source obligation is the concrete GE/stage
    bookkeeping certificate
    `||S||_max <= ||U||_max` for the growth-factor matrix `U`. -/
theorem higham13_problem13_4_maxEntry_bounds_from_source_growthFactorEntry_exact_kappa
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hN : 0 < r + s)
    (A U : Fin (r + s) → Fin (r + s) → ℝ)
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
    (hS_le_U :
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) ≤
        maxEntryNorm hN U) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
        (n : ℝ) * growthFactorEntry hN A U hApos *
          (maxEntryNormRect hN hN A *
            maxEntryNormRect hN hN (nonsingInv (r + s) A)) ∧
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) *
          maxEntryNormRect hs hs
            ((⅟(A22 - A21 * ⅟A11 * A12)) : Matrix (Fin s) (Fin s) ℝ) ≤
        growthFactorEntry hN A U hApos *
          (maxEntryNormRect hN hN A *
            maxEntryNormRect hN hN (nonsingInv (r + s) A)) := by
  have hRho : 0 ≤ growthFactorEntry hN A U hApos := by
    unfold growthFactorEntry
    exact div_nonneg (maxEntryNorm_nonneg hN U) (le_of_lt hApos)
  have hS_growth :
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) ≤
        growthFactorEntry hN A U hApos * maxEntryNormRect hN hN A :=
    maxEntryNormRect_le_growthFactorEntry_mul_of_le_maxEntryNorm
      hN hs A U (A22 - A21 * ⅟A11 * A12) hApos hS_le_U
  exact
    higham13_problem13_4_maxEntry_bounds_from_source_schur_growth_exact_kappa
      hr hs hN A A11 A12 A21 A22
      hA11_block hA12_block hA21_block hA22_block
      n hRho hsn hS_growth

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 feeding equation (13.22):
    an arbitrary source growth-factor matrix that contains both the initial
    max-entry norm and the Schur complement supplies the lower-factor premise
    `‖L‖ <= n ρ_n^2 κ(A)`.

    The two containment hypotheses are the remaining recursive GE bookkeeping:
    `hA_le_U` records that the growth object includes the initial matrix, and
    `hS_le_U` records that it includes the current Schur complement. -/
theorem higham13_problem13_4_L21_eq13_22_premise_from_source_growthFactorEntry_exact_kappa
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hN : 0 < r + s)
    (A U : Fin (r + s) → Fin (r + s) → ℝ)
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
    (hA_le_U : maxEntryNorm hN A ≤ maxEntryNorm hN U)
    (hS_le_U :
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) ≤
        maxEntryNorm hN U) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
        (n : ℝ) * (growthFactorEntry hN A U hApos) ^ 2 *
          (maxEntryNormRect hN hN A *
            maxEntryNormRect hN hN (nonsingInv (r + s) A)) := by
  let rho : ℝ := growthFactorEntry hN A U hApos
  let kappaA : ℝ :=
    maxEntryNormRect hN hN A *
      maxEntryNormRect hN hN (nonsingInv (r + s) A)
  have hProblem :
      maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
        (n : ℝ) * rho * kappaA := by
    have hpair :=
      higham13_problem13_4_maxEntry_bounds_from_source_growthFactorEntry_exact_kappa
        hr hs hN A U A11 A12 A21 A22
        hA11_block hA12_block hA21_block hA22_block
        hApos n hsn hS_le_U
    simpa [rho, kappaA] using hpair.1
  have hrho_ge_one : 1 ≤ rho := by
    simpa [rho] using
      growthFactorEntry_ge_one_of_maxEntryNorm_le hN A U hApos hA_le_U
  have hrho_nonneg : 0 ≤ rho := le_trans zero_le_one hrho_ge_one
  have hkappa_nonneg : 0 ≤ kappaA := by
    exact mul_nonneg (maxEntryNormRect_nonneg hN hN A)
      (maxEntryNormRect_nonneg hN hN (nonsingInv (r + s) A))
  have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hrho_le_sq : rho ≤ rho ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hrho_ge_one hrho_nonneg
    simpa [pow_two] using hmul
  have hfactor :
      (n : ℝ) * rho * kappaA ≤ (n : ℝ) * rho ^ 2 * kappaA := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrho_le_sq hn_nonneg) hkappa_nonneg
  exact le_trans hProblem (by simpa [rho, kappaA] using hfactor)

end NumStability
