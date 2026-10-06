import Mathlib.LinearAlgebra.Matrix.SchurComplement
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum

/-!
# Block LU Schur complements

Reusable uniform-block Schur-complement definitions and bridges to flattened
matrix nonsingularity and entrywise-norm positivity.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix

/-- **Block Schur complement** (Higham, 2nd ed., Chapter 13, eq. 13.2):
    S_{ij} = A_{i+1,j+1} − ∑_{l₁,l₂} A_{i+1,0}(s,l₁) · A₁₁⁻¹(l₁,l₂) · A_{0,j+1}(l₂,t).
    Eliminates block row/column 0, yielding an m×m block matrix from (m+1)×(m+1). -/
noncomputable def blockSchur {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (A11_inv : Fin r → Fin r → ℝ) :
    Fin m → Fin m → (Fin r → Fin r → ℝ) :=
  fun i j s t => A i.succ j.succ s t -
    ∑ l₁ : Fin r, ∑ l₂ : Fin r,
      A i.succ (0 : Fin (m + 1)) s l₁ * A11_inv l₁ l₂ *
      A (0 : Fin (m + 1)) j.succ l₂ t

/-- The scalar Schur complement of the first-split flattening is the standard
    flattening of the Chapter 13 block Schur complement. -/
theorem blockMatrixFirstSplit_schur_eq_blockMatrixFlatFin_blockSchur {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (A11_inv : Matrix (Fin r) (Fin r) ℝ) :
    blockMatrixFirstSplitA22 A -
        blockMatrixFirstSplitA21 A * A11_inv * blockMatrixFirstSplitA12 A =
      blockMatrixFlatFin (blockSchur A A11_inv) := by
  ext p q
  simp [blockMatrixFirstSplitA22, blockMatrixFirstSplitA21,
    blockMatrixFirstSplitA12, blockMatrixFlatFin, blockSchur, Matrix.mul_apply,
    Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    determinant nonzero for the recursive Schur tail from the source
    first-split Schur-complement invertibility.

    This removes a proof-artifact premise from recursive source surfaces: the
    positive denominator for the tail growth factor follows from the already
    explicit Schur-complement invertibility and pivot-inverse identification. -/
theorem det_ne_zero_blockMatrixFlatFin_blockSchur_of_first_split_invertible
    {m r : ℕ}
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk)) :
    Matrix.det (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0)) :
      Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0 := by
  have hdetSchur :
      Matrix.det
          (blockMatrixFirstSplitA22 Ablk -
            blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
              blockMatrixFirstSplitA12 Ablk :
            Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0 :=
    (Matrix.isUnit_det_of_invertible
      (blockMatrixFirstSplitA22 Ablk -
        blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
          blockMatrixFirstSplitA12 Ablk)).ne_zero
  have hSchur :
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0)) =
        blockMatrixFirstSplitA22 Ablk -
          blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
            blockMatrixFirstSplitA12 Ablk := by
    rw [hpivot]
    exact (blockMatrixFirstSplit_schur_eq_blockMatrixFlatFin_blockSchur
      Ablk (⅟(blockMatrixFirstSplitA11 Ablk))).symm
  rw [hSchur]
  exact hdetSchur

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    positive max-entry norm for the recursive Schur tail from first-split
    Schur-complement invertibility. -/
theorem maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
    {m r : ℕ} (hr : 0 < r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitA11 Ablk)]
    [Invertible (blockMatrixFirstSplitA22 Ablk -
      blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
        blockMatrixFirstSplitA12 Ablk)]
    (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk)) :
    0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
      (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))) :=
  maxEntryNorm_pos_of_det_ne_zero (Nat.mul_pos (Nat.succ_pos m) hr)
    (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0)))
    (det_ne_zero_blockMatrixFlatFin_blockSchur_of_first_split_invertible
      Ablk pivotInv hpivot)

end NumStability
