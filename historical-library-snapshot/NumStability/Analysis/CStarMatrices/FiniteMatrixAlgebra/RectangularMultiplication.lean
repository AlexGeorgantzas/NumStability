import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block
import NumStability.Analysis.MatrixAlgebra

/-!
# Analysis.CStarMatrices.FiniteMatrixAlgebra.RectangularMultiplication

R07 canonical `reusable` leaf. Declaration-level review groups 8 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.cstarMatrix_add_mul_rect`, `NumStability.cstarMatrix_mul_add_rect`, `NumStability.cstarMatrix_mul_assoc_rect`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


namespace NumStability

open scoped ComplexOrder MatrixOrder

/-- Rectangular associativity for `CStarMatrix` multiplication.  Mathlib's
square semiring associativity does not fire reliably for rectangular products,
so this entrywise wrapper is useful for block-column compression algebra. -/
theorem cstarMatrix_mul_assoc_rect {α β γ δ : Type*}
    [Fintype β] [Fintype γ] [DecidableEq γ] [DecidableEq δ]
    (A : CStarMatrix α β ℂ) (B : CStarMatrix β γ ℂ)
    (C : CStarMatrix γ δ ℂ) :
    (A * B) * C = A * (B * C) := by
  ext i j
  simp [CStarMatrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- Right distributivity for rectangular `CStarMatrix` multiplication. -/
theorem cstarMatrix_mul_add_rect {α β γ : Type*}
    [Fintype β] (A : CStarMatrix α β ℂ)
    (B C : CStarMatrix β γ ℂ) :
    A * (B + C) = A * B + A * C := by
  ext i j
  simp [CStarMatrix.mul_apply, mul_add, Finset.sum_add_distrib]

/-- Left distributivity for rectangular `CStarMatrix` multiplication. -/
theorem cstarMatrix_add_mul_rect {α β γ : Type*}
    [Fintype β] (A B : CStarMatrix α β ℂ)
    (C : CStarMatrix β γ ℂ) :
    (A + B) * C = A * C + B * C := by
  ext i j
  simp [CStarMatrix.mul_apply, add_mul, Finset.sum_add_distrib]

/-- Pull a scalar through the right factor of a rectangular multiplication. -/
theorem cstarMatrix_mul_smul_rect {α β γ : Type*}
    [Fintype β] (a : ℂ) (A : CStarMatrix α β ℂ)
    (B : CStarMatrix β γ ℂ) :
    A * (a • B) = a • (A * B) := by
  ext i j
  simp [CStarMatrix.mul_apply]
  calc
    (∑ x, A i x * (a * B x j))
        = ∑ x, a * (A i x * B x j) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = a * ∑ x, A i x * B x j := by
          rw [Finset.mul_sum]

/-- Pull a scalar through the left factor of a rectangular multiplication. -/
theorem cstarMatrix_smul_mul_rect {α β γ : Type*}
    [Fintype β] (a : ℂ) (A : CStarMatrix α β ℂ)
    (B : CStarMatrix β γ ℂ) :
    (a • A) * B = a • (A * B) := by
  ext i j
  simp [CStarMatrix.mul_apply]
  calc
    (∑ x, (a * A i x) * B x j)
        = ∑ x, a * (A i x * B x j) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = a * ∑ x, A i x * B x j := by
          rw [Finset.mul_sum]

/-- Right identity for rectangular `CStarMatrix` multiplication. -/
theorem cstarMatrix_mul_one_rect {α β : Type*}
    [Fintype β] [DecidableEq β] (A : CStarMatrix α β ℂ) :
    A * (1 : CStarMatrix β β ℂ) = A := by
  ext i j
  simp [CStarMatrix.mul_apply, CStarMatrix.one_apply]

/-- Left identity for rectangular `CStarMatrix` multiplication. -/
theorem cstarMatrix_one_mul_rect {α β : Type*}
    [Fintype α] [DecidableEq α] [DecidableEq β]
    (A : CStarMatrix α β ℂ) :
    (1 : CStarMatrix α α ℂ) * A = A := by
  ext i j
  simp [CStarMatrix.mul_apply, CStarMatrix.one_apply]

/-- If two square unit C⋆-matrices intertwine a rectangular matrix, then their
inverses intertwine the same rectangular matrix in the opposite direction.

This is a rectangular algebra adapter used by shifted-resolvent corner
arguments: from \(U V = V W\) we get \(U^{-1} V = V W^{-1}\). -/
theorem cstarMatrix_units_inv_mul_rect_eq_mul_units_inv_of_mul_eq
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (U : (CStarMatrix α α ℂ)ˣ) (W : (CStarMatrix β β ℂ)ˣ)
    (V : CStarMatrix α β ℂ)
    (hUV : (U : CStarMatrix α α ℂ) * V =
      V * (W : CStarMatrix β β ℂ)) :
    (↑U⁻¹ : CStarMatrix α α ℂ) * V =
      V * (↑W⁻¹ : CStarMatrix β β ℂ) := by
  have hleft :
      (↑U⁻¹ : CStarMatrix α α ℂ) * ((U : CStarMatrix α α ℂ) * V) =
        V := by
    have hUinv :
        (↑U⁻¹ : CStarMatrix α α ℂ) * (U : CStarMatrix α α ℂ) = 1 :=
      Units.inv_mul U
    calc
      (↑U⁻¹ : CStarMatrix α α ℂ) * ((U : CStarMatrix α α ℂ) * V) =
          ((↑U⁻¹ : CStarMatrix α α ℂ) * (U : CStarMatrix α α ℂ)) * V := by
            rw [← cstarMatrix_mul_assoc_rect]
      _ = (1 : CStarMatrix α α ℂ) * V := by
            rw [hUinv]
      _ = V := cstarMatrix_one_mul_rect V
  have hmid :
      V = ((↑U⁻¹ : CStarMatrix α α ℂ) * V) *
          (W : CStarMatrix β β ℂ) := by
    calc
      V = (↑U⁻¹ : CStarMatrix α α ℂ) *
          ((U : CStarMatrix α α ℂ) * V) := hleft.symm
      _ = (↑U⁻¹ : CStarMatrix α α ℂ) *
          (V * (W : CStarMatrix β β ℂ)) := by
            rw [hUV]
      _ = ((↑U⁻¹ : CStarMatrix α α ℂ) * V) *
          (W : CStarMatrix β β ℂ) := by
            rw [← cstarMatrix_mul_assoc_rect]
  have hWinv :
      (W : CStarMatrix β β ℂ) * (↑W⁻¹ : CStarMatrix β β ℂ) = 1 :=
    Units.mul_inv W
  calc
    (↑U⁻¹ : CStarMatrix α α ℂ) * V =
        ((↑U⁻¹ : CStarMatrix α α ℂ) * V) *
          (1 : CStarMatrix β β ℂ) := by
            rw [cstarMatrix_mul_one_rect]
    _ = ((↑U⁻¹ : CStarMatrix α α ℂ) * V) *
          ((W : CStarMatrix β β ℂ) *
            (↑W⁻¹ : CStarMatrix β β ℂ)) := by
            rw [hWinv]
    _ = (((↑U⁻¹ : CStarMatrix α α ℂ) * V) *
          (W : CStarMatrix β β ℂ)) *
            (↑W⁻¹ : CStarMatrix β β ℂ) := by
            exact (cstarMatrix_mul_assoc_rect
              ((↑U⁻¹ : CStarMatrix α α ℂ) * V)
              (W : CStarMatrix β β ℂ)
              (↑W⁻¹ : CStarMatrix β β ℂ)).symm
    _ = V * (↑W⁻¹ : CStarMatrix β β ℂ) := by
            rw [← hmid]

end NumStability
