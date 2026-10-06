import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.FiniteRealEmbedding
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.FiniteRealOrder
import NumStability.Analysis.MatrixAlgebra

/-!
# Analysis.CStarMatrices.FiniteMatrixAlgebra.StrictPositivity

R07 canonical `reusable` leaf. Declaration-level review groups 3 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.cstarMatrix_pos_real_smul_one_isStrictlyPositive`, `NumStability.cstarMatrix_unitary_conj_isStrictlyPositive`, `NumStability.finiteComplexCStarMatrix_add_pos_smul_one_isStrictlyPositive_of_finitePSD`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


namespace NumStability

open scoped ComplexOrder MatrixOrder

/-- A strictly positive real scalar multiple of the complex C⋆-matrix identity
is strictly positive. This is a standard positive regularization term. -/
theorem cstarMatrix_pos_real_smul_one_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι] {eps : ℝ} (heps : 0 < eps) :
    IsStrictlyPositive ((eps : ℂ) • (1 : CStarMatrix ι ι ℂ)) := by
  have hunit : IsUnit ((eps : ℂ) • (1 : CStarMatrix ι ι ℂ)) := by
    refine isUnit_iff_exists.mpr
      ⟨((eps : ℂ)⁻¹) • (1 : CStarMatrix ι ι ℂ), ?_⟩
    constructor
    · simp [Algebra.mul_smul_comm, smul_smul, heps.ne']
    · simp [Algebra.mul_smul_comm, smul_smul, heps.ne']
  have hnonneg : 0 ≤ ((eps : ℂ) • (1 : CStarMatrix ι ι ℂ)) := by
    rw [StarOrderedRing.nonneg_iff]
    refine AddSubmonoid.subset_closure
      ⟨((Real.sqrt eps : ℂ) • (1 : CStarMatrix ι ι ℂ)), ?_⟩
    have hsqrt :
        ((Real.sqrt eps : ℂ) * (Real.sqrt eps : ℂ)) = (eps : ℂ) := by
      rw [← sq]
      exact_mod_cast Real.sq_sqrt (le_of_lt heps)
    simp [Algebra.mul_smul_comm, smul_smul, hsqrt]
  exact hunit.isStrictlyPositive hnonneg

/-- Adding a strictly positive scalar identity regularization to an embedded
local PSD matrix gives a strictly positive complex C⋆-matrix. -/
theorem finiteComplexCStarMatrix_add_pos_smul_one_isStrictlyPositive_of_finitePSD
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) (hPSD : finitePSD M)
    {eps : ℝ} (heps : 0 < eps) :
    IsStrictlyPositive
      (finiteComplexCStarMatrix M + (eps : ℂ) • (1 : CStarMatrix ι ι ℂ)) := by
  have hnonneg : 0 ≤ finiteComplexCStarMatrix M :=
    finiteComplexCStarMatrix_nonneg_of_finitePSD M hM hPSD
  have hstrict :
      IsStrictlyPositive ((eps : ℂ) • (1 : CStarMatrix ι ι ℂ)) :=
    cstarMatrix_pos_real_smul_one_isStrictlyPositive heps
  exact IsStrictlyPositive.nonneg_add hnonneg hstrict

/-- Conjugation by a unitary finite C⋆-matrix preserves strict positivity. -/
theorem cstarMatrix_unitary_conj_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : unitary (CStarMatrix ι ι ℂ)) {T : CStarMatrix ι ι ℂ}
    (hT : IsStrictlyPositive T) :
    IsStrictlyPositive
      ((u : CStarMatrix ι ι ℂ) * T * star (u : CStarMatrix ι ι ℂ)) := by
  exact (Unitary.isUnit_coe (U := u)).isStrictlyPositive_star_right_conjugate_iff.mpr hT

end NumStability
