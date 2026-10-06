import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block
import NumStability.Analysis.MatrixAlgebra

/-!
# Analysis.CStarMatrices.FiniteMatrixAlgebra.ColumnPair

R07 canonical `reusable` leaf. Declaration-level review groups 6 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.cstarMatrixColumnPair`, `NumStability.cstarMatrixColumnPair_conjTranspose_mul_columnPair`, `NumStability.cstarMatrixColumnPair_conjTranspose_mul_self`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


namespace NumStability

open scoped ComplexOrder MatrixOrder

/-- Vertical pairing of two square C⋆-matrices, the block column `[A;B]`. -/
def cstarMatrixColumnPair {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) : CStarMatrix (ι ⊕ ι) ι ℂ :=
  CStarMatrix.ofMatrix fun r j =>
    match r with
    | Sum.inl i => A i j
    | Sum.inr i => B i j

@[simp]
theorem cstarMatrixColumnPair_inl {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) (i j : ι) :
    cstarMatrixColumnPair A B (Sum.inl i) j = A i j := by
  rfl

@[simp]
theorem cstarMatrixColumnPair_inr {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) (i j : ι) :
    cstarMatrixColumnPair A B (Sum.inr i) j = B i j := by
  rfl

/-- Multiplying two block columns gives the sum of the two block products. -/
theorem cstarMatrixColumnPair_conjTranspose_mul_columnPair
    {ι : Type*} [Fintype ι]
    (A B C D : CStarMatrix ι ι ℂ) :
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        cstarMatrixColumnPair C D =
      star A * C + star B * D := by
  ext i j
  simp [CStarMatrix.mul_apply, CStarMatrix.star_apply,
    Fintype.sum_sum_type]

/-- The normalization of the block column `[A;B]` is `AᴴA + BᴴB`. -/
theorem cstarMatrixColumnPair_conjTranspose_mul_self
    {ι : Type*} [Fintype ι]
    (A B : CStarMatrix ι ι ℂ) :
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        cstarMatrixColumnPair A B =
      star A * A + star B * B := by
  simpa using cstarMatrixColumnPair_conjTranspose_mul_columnPair A B A B

/-- If `AᴴA + BᴴB = I`, then the block column `[A;B]` is an isometry. -/
theorem cstarMatrixColumnPair_conjTranspose_mul_self_eq_one_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1) :
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
      cstarMatrixColumnPair A B = 1 := by
  rw [cstarMatrixColumnPair_conjTranspose_mul_self, hAB]

end NumStability
