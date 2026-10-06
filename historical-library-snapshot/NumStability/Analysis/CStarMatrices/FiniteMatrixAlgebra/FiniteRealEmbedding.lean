import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block
import NumStability.Analysis.MatrixAlgebra

/-!
# Analysis.CStarMatrices.FiniteMatrixAlgebra.FiniteRealEmbedding

R07 canonical `reusable` leaf. Declaration-level review groups 12 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.finiteComplexCStarMatrix`, `NumStability.finiteComplexCStarMatrix_add`, `NumStability.finiteComplexCStarMatrix_apply`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


namespace NumStability

open scoped ComplexOrder MatrixOrder

/-- Embed a repository-native finite real square matrix into the complex
`CStarMatrix` type used by mathlib's C⋆-algebraic functional calculus. -/
noncomputable def finiteComplexCStarMatrix {ι : Type*}
    (M : ι → ι → ℝ) : CStarMatrix ι ι ℂ :=
  CStarMatrix.ofMatrix (fun i j => (M i j : ℂ))

@[simp]
theorem finiteComplexCStarMatrix_apply {ι : Type*}
    (M : ι → ι → ℝ) (i j : ι) :
    finiteComplexCStarMatrix M i j = (M i j : ℂ) := rfl

/-- The complex C⋆-matrix embedding preserves zero. -/
@[simp]
theorem finiteComplexCStarMatrix_zero {ι : Type*} :
    finiteComplexCStarMatrix (fun _ _ : ι => 0) =
      (0 : CStarMatrix ι ι ℂ) := by
  ext i j
  simp

/-- The complex C⋆-matrix embedding preserves addition. -/
theorem finiteComplexCStarMatrix_add
    {ι : Type*} (M N : ι → ι → ℝ) :
    finiteComplexCStarMatrix (fun i j => M i j + N i j) =
      finiteComplexCStarMatrix M + finiteComplexCStarMatrix N := by
  ext i j
  simp

/-- The complex C⋆-matrix embedding preserves real scalar multiplication. -/
theorem finiteComplexCStarMatrix_smul
    {ι : Type*} (a : ℝ) (M : ι → ι → ℝ) :
    finiteComplexCStarMatrix (fun i j => a * M i j) =
      (a : ℂ) • finiteComplexCStarMatrix M := by
  ext i j
  simp

/-- The complex C⋆-matrix embedding preserves finite real matrix
multiplication. -/
theorem finiteComplexCStarMatrix_mul
    {ι : Type*} [Fintype ι] (M N : ι → ι → ℝ) :
    finiteComplexCStarMatrix (finiteMatMul M N) =
      finiteComplexCStarMatrix M * finiteComplexCStarMatrix N := by
  ext i j
  simp [finiteMatMul, CStarMatrix.mul_apply]

/-- Symmetric real finite matrices embed as self-adjoint complex C⋆-matrices. -/
theorem finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
    {ι : Type*} (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) :
    IsSelfAdjoint (finiteComplexCStarMatrix M) := by
  rw [isSelfAdjoint_iff]
  ext i j
  rw [CStarMatrix.star_apply]
  simp [hM j i]

/-- The complex C⋆-matrix embedding preserves finite real matrix subtraction. -/
theorem finiteComplexCStarMatrix_sub
    {ι : Type*} (M N : ι → ι → ℝ) :
    finiteComplexCStarMatrix (fun i j => M i j - N i j) =
      finiteComplexCStarMatrix M - finiteComplexCStarMatrix N := by
  ext i j
  simp

/-- The complex C⋆-matrix embedding preserves negation. -/
theorem finiteComplexCStarMatrix_neg
    {ι : Type*} (M : ι → ι → ℝ) :
    finiteComplexCStarMatrix (fun i j => -M i j) =
      -finiteComplexCStarMatrix M := by
  ext i j
  simp

/-- The complex C⋆-matrix embedding preserves finite sums. -/
theorem finiteComplexCStarMatrix_finset_sum
    {α ι : Type*} [DecidableEq α]
    (s : Finset α) (F : α → ι → ι → ℝ) :
    finiteComplexCStarMatrix (fun i j => s.sum (fun a => F a i j)) =
      s.sum (fun a => finiteComplexCStarMatrix (F a)) := by
  classical
  ext i j
  change ((s.sum fun a => F a i j : ℝ) : ℂ) =
    (s.sum fun a => finiteComplexCStarMatrix (F a)) i j
  revert i j
  refine Finset.induction_on s ?base ?step
  · intro i j
    simp
  · intro a s ha ih i j
    rw [Finset.sum_insert ha]
    rw [Finset.sum_insert ha]
    simp [ih i j]

/-- The finite real identity embeds as the complex C⋆-matrix identity. -/
theorem finiteComplexCStarMatrix_finiteIdMatrix
    {ι : Type*} [DecidableEq ι] :
    finiteComplexCStarMatrix (finiteIdMatrix : ι → ι → ℝ) =
      (1 : CStarMatrix ι ι ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [finiteIdMatrix]
  · simp [finiteIdMatrix, hij]

/-- Scalar multiples of the finite real identity embed as scalar multiples of
the complex C⋆-matrix identity. -/
theorem finiteComplexCStarMatrix_smul_finiteIdMatrix
    {ι : Type*} [DecidableEq ι] (a : ℝ) :
    finiteComplexCStarMatrix (fun i j : ι => a * finiteIdMatrix i j) =
      (a : ℂ) • (1 : CStarMatrix ι ι ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [finiteIdMatrix]
  · simp [finiteIdMatrix, hij]

end NumStability
