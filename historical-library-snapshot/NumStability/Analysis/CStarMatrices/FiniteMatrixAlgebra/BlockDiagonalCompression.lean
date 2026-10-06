import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.BlockDiagonal
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ColumnPair
import NumStability.Analysis.MatrixAlgebra

/-!
# Analysis.CStarMatrices.FiniteMatrixAlgebra.BlockDiagonalCompression

R07 canonical `reusable` leaf. Declaration-level review groups 2 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.cstarMatrixBlockDiagonal_mul_columnPair`, `NumStability.cstarMatrixColumnPair_conjTranspose_mul_blockDiagonal_mul_columnPair`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


namespace NumStability

open scoped ComplexOrder MatrixOrder

/-- Multiplying `diag(T₁,T₂)` by `[A;B]` acts blockwise. -/
theorem cstarMatrixBlockDiagonal_mul_columnPair
    {ι : Type*} [Fintype ι]
    (T1 T2 A B : CStarMatrix ι ι ℂ) :
    cstarMatrixBlockDiagonal T1 T2 * cstarMatrixColumnPair A B =
      cstarMatrixColumnPair (T1 * A) (T2 * B) := by
  ext r j
  cases r with
  | inl i => simp [CStarMatrix.mul_apply, Fintype.sum_sum_type]
  | inr i => simp [CStarMatrix.mul_apply, Fintype.sum_sum_type]

/-- Compression of a block diagonal matrix by the block column `[A;B]`. -/
theorem cstarMatrixColumnPair_conjTranspose_mul_blockDiagonal_mul_columnPair
    {ι : Type*} [Fintype ι]
    (A B T1 T2 : CStarMatrix ι ι ℂ) :
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        cstarMatrixBlockDiagonal T1 T2 * cstarMatrixColumnPair A B =
      star A * T1 * A + star B * T2 * B := by
  ext i j
  simp [CStarMatrix.mul_apply, CStarMatrix.star_apply,
    Fintype.sum_sum_type, Finset.sum_mul]

end NumStability
