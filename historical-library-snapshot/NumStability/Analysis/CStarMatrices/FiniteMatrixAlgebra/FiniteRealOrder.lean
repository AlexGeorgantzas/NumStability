import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.FiniteRealEmbedding
import NumStability.Analysis.MatrixAlgebra

/-!
# Analysis.CStarMatrices.FiniteMatrixAlgebra.FiniteRealOrder

R07 canonical `reusable` leaf. Declaration-level review groups 3 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.finiteComplexCStarMatrix_add_smul_one_le_of_finiteLoewnerLe`, `NumStability.finiteComplexCStarMatrix_le_of_finiteLoewnerLe`, `NumStability.finiteComplexCStarMatrix_nonneg_of_finitePSD`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


namespace NumStability

open scoped ComplexOrder MatrixOrder

/-- A locally PSD real finite matrix embeds as a nonnegative complex
C⋆-matrix. -/
theorem finiteComplexCStarMatrix_nonneg_of_finitePSD
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) (hPSD : finitePSD M) :
    0 ≤ finiteComplexCStarMatrix M := by
  have hmat : Matrix.PosSemidef (M : Matrix ι ι ℝ) :=
    finitePSD.to_matrix_posSemidef M hM hPSD
  set_option linter.deprecated false in
  rw [Matrix.posSemidef_iff_eq_conjTranspose_mul_self] at hmat
  rcases hmat with ⟨B, hB⟩
  let C : CStarMatrix ι ι ℂ := finiteComplexCStarMatrix (fun i j => B i j)
  have h_eq : finiteComplexCStarMatrix M = star C * C := by
    ext i j
    have hij := congrArg (fun A : Matrix ι ι ℝ => A i j) hB
    rw [CStarMatrix.mul_apply]
    simp_rw [CStarMatrix.star_apply]
    simp [C, finiteComplexCStarMatrix, Matrix.mul_apply] at hij ⊢
    rw [hij]
    simp
  rw [h_eq, StarOrderedRing.nonneg_iff]
  exact AddSubmonoid.subset_closure ⟨C, rfl⟩

/-- A local finite Loewner inequality between symmetric real finite matrices
embeds as the complex C⋆-matrix spectral-order inequality. -/
theorem finiteComplexCStarMatrix_le_of_finiteLoewnerLe
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : ι → ι → ℝ)
    (hM : IsSymmetricFiniteMatrix M) (hN : IsSymmetricFiniteMatrix N)
    (hLe : finiteLoewnerLe M N) :
    finiteComplexCStarMatrix M ≤ finiteComplexCStarMatrix N := by
  have hDsym : IsSymmetricFiniteMatrix (fun i j => N i j - M i j) := by
    intro i j
    change N i j - M i j = N j i - M j i
    rw [hN i j, hM i j]
  have hDpsd : finitePSD (fun i j => N i j - M i j) :=
    (finiteLoewnerLe_iff_sub_finitePSD M N).mp hLe
  have hnonneg :=
    finiteComplexCStarMatrix_nonneg_of_finitePSD
      (fun i j => N i j - M i j) hDsym hDpsd
  rw [finiteComplexCStarMatrix_sub N M] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Adding the same scalar identity regularization preserves an embedded local
finite Loewner inequality. -/
theorem finiteComplexCStarMatrix_add_smul_one_le_of_finiteLoewnerLe
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : ι → ι → ℝ)
    (hM : IsSymmetricFiniteMatrix M) (hN : IsSymmetricFiniteMatrix N)
    (hLe : finiteLoewnerLe M N) (eps : ℝ) :
    finiteComplexCStarMatrix M + (eps : ℂ) • (1 : CStarMatrix ι ι ℂ) ≤
      finiteComplexCStarMatrix N + (eps : ℂ) • (1 : CStarMatrix ι ι ℂ) := by
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_right
      (finiteComplexCStarMatrix_le_of_finiteLoewnerLe M N hM hN hLe)
      ((eps : ℂ) • (1 : CStarMatrix ι ι ℂ))

end NumStability
