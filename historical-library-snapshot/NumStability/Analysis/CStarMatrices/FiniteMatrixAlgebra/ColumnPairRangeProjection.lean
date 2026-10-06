import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ColumnPair
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.RectangularMultiplication
import NumStability.Analysis.MatrixAlgebra

/-!
# Analysis.CStarMatrices.FiniteMatrixAlgebra.ColumnPairRangeProjection

R07 canonical `reusable` leaf. Declaration-level review groups 5 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.cstarMatrixColumnPairRangeProjection`, `NumStability.cstarMatrixColumnPairRangeProjection_isSelfAdjoint`, `NumStability.cstarMatrixColumnPairRangeProjection_mul_columnPair_of_sum`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


namespace NumStability

open scoped ComplexOrder MatrixOrder

/-- The range projection `VVᴴ` of the block column `V = [A;B]`. -/
noncomputable def cstarMatrixColumnPairRangeProjection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CStarMatrix ι ι ℂ) : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  cstarMatrixColumnPair A B *
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B)

/-- The range projection `VVᴴ` is self-adjoint. -/
theorem cstarMatrixColumnPairRangeProjection_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CStarMatrix ι ι ℂ) :
    IsSelfAdjoint (cstarMatrixColumnPairRangeProjection A B) := by
  rw [isSelfAdjoint_iff]
  ext r c
  simp [cstarMatrixColumnPairRangeProjection, CStarMatrix.mul_apply,
    CStarMatrix.star_apply, CStarMatrix.conjTranspose_apply, mul_comm]

/-- If `VᴴV = I`, then the range matrix `VVᴴ` is idempotent. -/
theorem cstarMatrixColumnPairRangeProjection_mul_self_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1) :
    cstarMatrixColumnPairRangeProjection A B *
        cstarMatrixColumnPairRangeProjection A B =
      cstarMatrixColumnPairRangeProjection A B := by
  let V := cstarMatrixColumnPair A B
  have hV : CStarMatrix.conjTranspose V * V = 1 := by
    dsimp [V]
    exact cstarMatrixColumnPair_conjTranspose_mul_self_eq_one_of_sum hAB
  calc
    cstarMatrixColumnPairRangeProjection A B *
        cstarMatrixColumnPairRangeProjection A B =
        (V * CStarMatrix.conjTranspose V) *
          (V * CStarMatrix.conjTranspose V) := rfl
    _ = V * (CStarMatrix.conjTranspose V * V) *
          CStarMatrix.conjTranspose V := by
      rw [cstarMatrix_mul_assoc_rect V (CStarMatrix.conjTranspose V)
        (V * CStarMatrix.conjTranspose V)]
      rw [← cstarMatrix_mul_assoc_rect (CStarMatrix.conjTranspose V) V
        (CStarMatrix.conjTranspose V)]
      rw [← cstarMatrix_mul_assoc_rect V
        (CStarMatrix.conjTranspose V * V) (CStarMatrix.conjTranspose V)]
    _ = V * CStarMatrix.conjTranspose V := by
      rw [hV]
      rw [cstarMatrix_mul_one_rect V]
    _ = cstarMatrixColumnPairRangeProjection A B := rfl

/-- If `VᴴV = I`, then the range projection absorbs the block column:
`(VVᴴ)V = V`. -/
theorem cstarMatrixColumnPairRangeProjection_mul_columnPair_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1) :
    cstarMatrixColumnPairRangeProjection A B *
        cstarMatrixColumnPair A B =
      cstarMatrixColumnPair A B := by
  let V := cstarMatrixColumnPair A B
  have hV : CStarMatrix.conjTranspose V * V = 1 := by
    dsimp [V]
    exact cstarMatrixColumnPair_conjTranspose_mul_self_eq_one_of_sum hAB
  calc
    cstarMatrixColumnPairRangeProjection A B * cstarMatrixColumnPair A B =
        (V * CStarMatrix.conjTranspose V) * V := rfl
    _ = V * (CStarMatrix.conjTranspose V * V) := by
      rw [cstarMatrix_mul_assoc_rect V (CStarMatrix.conjTranspose V) V]
    _ = V := by
      rw [hV]
      exact cstarMatrix_mul_one_rect V

/-- If `VᴴV = I`, then the range projection absorbs the adjoint block column:
`Vᴴ(VVᴴ) = Vᴴ`. -/
theorem cstarMatrixColumnPair_conjTranspose_mul_rangeProjection_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1) :
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        cstarMatrixColumnPairRangeProjection A B =
      CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) := by
  let V := cstarMatrixColumnPair A B
  have hV : CStarMatrix.conjTranspose V * V = 1 := by
    dsimp [V]
    exact cstarMatrixColumnPair_conjTranspose_mul_self_eq_one_of_sum hAB
  calc
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        cstarMatrixColumnPairRangeProjection A B =
        CStarMatrix.conjTranspose V * (V * CStarMatrix.conjTranspose V) := rfl
    _ = (CStarMatrix.conjTranspose V * V) *
          CStarMatrix.conjTranspose V := by
      rw [← cstarMatrix_mul_assoc_rect (CStarMatrix.conjTranspose V) V
        (CStarMatrix.conjTranspose V)]
    _ = CStarMatrix.conjTranspose V := by
      rw [hV]
      exact cstarMatrix_one_mul_rect (CStarMatrix.conjTranspose V)

end NumStability
