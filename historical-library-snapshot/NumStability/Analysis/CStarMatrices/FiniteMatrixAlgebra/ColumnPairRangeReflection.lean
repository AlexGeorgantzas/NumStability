import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ColumnPair
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ColumnPairRangeProjection
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ProjectionReflection
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.StrictPositivity
import NumStability.Analysis.MatrixAlgebra

/-!
# Analysis.CStarMatrices.FiniteMatrixAlgebra.ColumnPairRangeReflection

R07 canonical `reusable` leaf. Declaration-level review groups 8 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.cstarMatrixColumnPairRangeReflection`, `NumStability.cstarMatrixColumnPairRangeReflection_conj_isStrictlyPositive_of_sum`, `NumStability.cstarMatrixColumnPairRangeReflection_isSelfAdjoint`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


namespace NumStability

open scoped ComplexOrder MatrixOrder

/-- The range reflection `2VVᴴ - I` of the block column `V = [A;B]`. -/
noncomputable def cstarMatrixColumnPairRangeReflection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CStarMatrix ι ι ℂ) : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  cstarMatrixProjectionReflection (cstarMatrixColumnPairRangeProjection A B)

/-- The block-column range reflection is self-adjoint. -/
theorem cstarMatrixColumnPairRangeReflection_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CStarMatrix ι ι ℂ) :
    IsSelfAdjoint (cstarMatrixColumnPairRangeReflection A B) := by
  exact cstarMatrixProjectionReflection_isSelfAdjoint_of_isSelfAdjoint
    (cstarMatrixColumnPairRangeProjection A B)
    (cstarMatrixColumnPairRangeProjection_isSelfAdjoint A B)

/-- If `VᴴV = I`, then the range reflection `2VVᴴ - I` squares to identity. -/
theorem cstarMatrixColumnPairRangeReflection_mul_self_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1) :
    cstarMatrixColumnPairRangeReflection A B *
        cstarMatrixColumnPairRangeReflection A B =
      (1 : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := by
  exact cstarMatrixProjectionReflection_mul_self_of_idempotent
    (cstarMatrixColumnPairRangeProjection A B)
    (cstarMatrixColumnPairRangeProjection_mul_self_of_sum hAB)

/-- If `VᴴV = I`, then the block-column range reflection is a unit. -/
theorem cstarMatrixColumnPairRangeReflection_isUnit_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1) :
    IsUnit (cstarMatrixColumnPairRangeReflection A B) := by
  exact cstarMatrixProjectionReflection_isUnit_of_idempotent
    (cstarMatrixColumnPairRangeProjection A B)
    (cstarMatrixColumnPairRangeProjection_mul_self_of_sum hAB)

/-- If `VᴴV = I`, then the block-column range reflection is unitary. -/
theorem cstarMatrixColumnPairRangeReflection_mem_unitary_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1) :
    cstarMatrixColumnPairRangeReflection A B ∈
      unitary (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := by
  exact
    cstarMatrixProjectionReflection_mem_unitary_of_isSelfAdjoint_of_idempotent
      (cstarMatrixColumnPairRangeProjection A B)
      (cstarMatrixColumnPairRangeProjection_isSelfAdjoint A B)
      (cstarMatrixColumnPairRangeProjection_mul_self_of_sum hAB)

/-- If `VᴴV = I`, then the block-column range reflection fixes the block
column: `(2VVᴴ - I)V = V`. -/
theorem cstarMatrixColumnPairRangeReflection_mul_columnPair_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1) :
    cstarMatrixColumnPairRangeReflection A B *
        cstarMatrixColumnPair A B =
      cstarMatrixColumnPair A B := by
  exact cstarMatrixProjectionReflection_mul_of_mul_eq_self
    (cstarMatrixColumnPairRangeProjection A B)
    (cstarMatrixColumnPair A B)
    (cstarMatrixColumnPairRangeProjection_mul_columnPair_of_sum hAB)

/-- If `VᴴV = I`, then the block-column range reflection fixes the adjoint
block column on the right: `Vᴴ(2VVᴴ - I) = Vᴄ`. -/
theorem cstarMatrixColumnPair_conjTranspose_mul_rangeReflection_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1) :
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        cstarMatrixColumnPairRangeReflection A B =
      CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) := by
  exact cstarMatrix_mul_projectionReflection_of_mul_eq_self
    (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B))
    (cstarMatrixColumnPairRangeProjection A B)
    (cstarMatrixColumnPair_conjTranspose_mul_rangeProjection_of_sum hAB)

/-- The block-column range reflection preserves strict positivity by
conjugation whenever `VᴴV = I`. -/
theorem cstarMatrixColumnPairRangeReflection_conj_isStrictlyPositive_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    {T : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ}
    (hT : IsStrictlyPositive T) :
    IsStrictlyPositive
      (cstarMatrixColumnPairRangeReflection A B * T *
        star (cstarMatrixColumnPairRangeReflection A B)) := by
  let u : unitary (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :=
    ⟨cstarMatrixColumnPairRangeReflection A B,
      cstarMatrixColumnPairRangeReflection_mem_unitary_of_sum hAB⟩
  exact cstarMatrix_unitary_conj_isStrictlyPositive u hT

end NumStability
