import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.FiniteDimensional
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.RectangularMultiplication
import NumStability.Analysis.MatrixAlgebra

/-!
# Analysis.CStarMatrices.FiniteMatrixAlgebra.RectangularCompression

R07 canonical `reusable` leaf. Declaration-level review groups 7 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.cstarMatrixCompressionCLM`, `NumStability.cstarMatrixCompressionCLM_apply`, `NumStability.cstarMatrix_compression_add`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


namespace NumStability

open scoped ComplexOrder MatrixOrder

/-- Compression by a rectangular `CStarMatrix` distributes over addition. -/
theorem cstarMatrix_compression_add
    {α β : Type*} [Fintype α] [Fintype β]
    (V : CStarMatrix α β ℂ) (M N : CStarMatrix α α ℂ) :
    CStarMatrix.conjTranspose V * (M + N) * V =
      CStarMatrix.conjTranspose V * M * V +
        CStarMatrix.conjTranspose V * N * V := by
  rw [cstarMatrix_mul_add_rect, cstarMatrix_add_mul_rect]

/-- Compression by a rectangular `CStarMatrix` distributes over subtraction. -/
theorem cstarMatrix_compression_sub
    {α β : Type*} [Fintype α] [Fintype β]
    (V : CStarMatrix α β ℂ) (M N : CStarMatrix α α ℂ) :
    CStarMatrix.conjTranspose V * (M - N) * V =
      CStarMatrix.conjTranspose V * M * V -
        CStarMatrix.conjTranspose V * N * V := by
  rw [sub_eq_add_neg, cstarMatrix_mul_add_rect, cstarMatrix_add_mul_rect]
  have hneg :
      CStarMatrix.conjTranspose V * (-N) * V =
        -(CStarMatrix.conjTranspose V * N * V) := by
    ext i j
    simp [CStarMatrix.mul_apply]
  rw [hneg]
  rfl

/-- Compression by a rectangular `CStarMatrix` commutes with scalar
multiplication. -/
theorem cstarMatrix_compression_smul
    {α β : Type*} [Fintype α] [Fintype β]
    (V : CStarMatrix α β ℂ) (a : ℂ) (M : CStarMatrix α α ℂ) :
    CStarMatrix.conjTranspose V * (a • M) * V =
      a • (CStarMatrix.conjTranspose V * M * V) := by
  rw [cstarMatrix_mul_smul_rect, cstarMatrix_smul_mul_rect]

/-- Compression by a rectangular `CStarMatrix` commutes with real scalar
multiplication. -/
theorem cstarMatrix_compression_real_smul
    {α β : Type*} [Fintype α] [Fintype β]
    (V : CStarMatrix α β ℂ) (a : ℝ) (M : CStarMatrix α α ℂ) :
    CStarMatrix.conjTranspose V * (a • M) * V =
      a • (CStarMatrix.conjTranspose V * M * V) := by
  change CStarMatrix.conjTranspose V * ((a : ℂ) • M) * V =
    (a : ℂ) • (CStarMatrix.conjTranspose V * M * V)
  exact cstarMatrix_compression_smul V (a : ℂ) M

/-- Compression by a fixed rectangular `CStarMatrix` as a continuous complex
linear map. -/
noncomputable def cstarMatrixCompressionCLM
    {α β : Type*} [Fintype α] [Fintype β]
    (V : CStarMatrix α β ℂ) :
    CStarMatrix α α ℂ →L[ℂ] CStarMatrix β β ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => CStarMatrix.conjTranspose V * M * V
      map_add' := by
        intro M N
        exact cstarMatrix_compression_add V M N
      map_smul' := by
        intro c M
        exact cstarMatrix_compression_smul V c M }

@[simp]
theorem cstarMatrixCompressionCLM_apply
    {α β : Type*} [Fintype α] [Fintype β]
    (V : CStarMatrix α β ℂ) (M : CStarMatrix α α ℂ) :
    cstarMatrixCompressionCLM V M =
      CStarMatrix.conjTranspose V * M * V := rfl

/-- Compressing the identity by an isometry gives the identity. -/
theorem cstarMatrix_compression_one_of_conjTranspose_mul_self_eq_one
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (V : CStarMatrix α β ℂ)
    (hVV : CStarMatrix.conjTranspose V * V = (1 : CStarMatrix β β ℂ)) :
    CStarMatrix.conjTranspose V * (1 : CStarMatrix α α ℂ) * V =
      (1 : CStarMatrix β β ℂ) := by
  calc
    CStarMatrix.conjTranspose V * (1 : CStarMatrix α α ℂ) * V =
        CStarMatrix.conjTranspose V * V := by
          rw [cstarMatrix_mul_one_rect]
    _ = 1 := hVV

end NumStability
