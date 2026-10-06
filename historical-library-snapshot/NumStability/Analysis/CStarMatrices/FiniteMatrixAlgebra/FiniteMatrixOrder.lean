import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block
import NumStability.Analysis.MatrixAlgebra

/-!
# Analysis.CStarMatrices.FiniteMatrixAlgebra.FiniteMatrixOrder

R07 canonical `reusable` leaf. Declaration-level review groups 2 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.cstarMatrix_le_of_matrix_le`, `NumStability.cstarMatrix_nonneg_of_matrix_posSemidef`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


namespace NumStability

open scoped ComplexOrder MatrixOrder

/-- Plain finite-matrix positive semidefiniteness gives spectral-order
nonnegativity of the corresponding complex `CStarMatrix`.

This is the complex counterpart of
`finiteComplexCStarMatrix_nonneg_of_finitePSD`.  It is a bridge lemma for
routes that prove a Loewner inequality by ordinary finite matrix arguments
and then need to return to the C⋆-matrix order used by functional calculus. -/
theorem cstarMatrix_nonneg_of_matrix_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : CStarMatrix ι ι ℂ}
    (hM : Matrix.PosSemidef (CStarMatrix.ofMatrix.symm M : Matrix ι ι ℂ)) :
    0 ≤ M := by
  set_option linter.deprecated false in
  rw [Matrix.posSemidef_iff_eq_conjTranspose_mul_self] at hM
  rcases hM with ⟨B, hB⟩
  let C : CStarMatrix ι ι ℂ := CStarMatrix.ofMatrix B
  have h_eq : M = star C * C := by
    apply CStarMatrix.ofMatrix.symm.injective
    simpa [C, CStarMatrix.mul_apply, CStarMatrix.conjTranspose_apply] using hB
  rw [h_eq, StarOrderedRing.nonneg_iff]
  exact AddSubmonoid.subset_closure ⟨C, rfl⟩

/-- Plain finite-matrix Loewner inequalities lift to spectral-order
inequalities of the corresponding complex `CStarMatrix` objects. -/
theorem cstarMatrix_le_of_matrix_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : (CStarMatrix.ofMatrix.symm A : Matrix ι ι ℂ) ≤
      CStarMatrix.ofMatrix.symm B) :
    A ≤ B := by
  have hpsd :
      Matrix.PosSemidef (CStarMatrix.ofMatrix.symm (B - A) : Matrix ι ι ℂ) := by
    have hmat := Matrix.le_iff.mp hAB
    simpa using hmat
  have hnon : 0 ≤ B - A := cstarMatrix_nonneg_of_matrix_posSemidef hpsd
  exact sub_nonneg.mp hnon

end NumStability
