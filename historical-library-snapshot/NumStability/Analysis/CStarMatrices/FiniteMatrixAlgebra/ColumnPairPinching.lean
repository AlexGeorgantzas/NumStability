import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ColumnPair
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ColumnPairRangeProjection
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ColumnPairRangeReflection
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.RectangularMultiplication
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ReflectionAverage
import NumStability.Analysis.MatrixAlgebra

/-!
# Analysis.CStarMatrices.FiniteMatrixAlgebra.ColumnPairPinching

R07 canonical `reusable` leaf. Declaration-level review groups 8 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.cstarMatrixColumnPair_conjTranspose_mul_eq_compression_mul_conjTranspose_of_commute`, `NumStability.cstarMatrixColumnPair_conjTranspose_mul_reflectionAverage_of_sum`, `NumStability.cstarMatrixColumnPair_mul_columnPair_eq_columnPair_compression_of_commute`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


namespace NumStability

open scoped ComplexOrder MatrixOrder

/-- Compressing the block-column reflection average gives the same matrix as
compressing the original block matrix.  This is the algebraic pinching
identity used before the nonlinear Jensen step. -/
theorem cstarMatrixColumnPair_reflectionAverage_compression_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    (D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) *
        cstarMatrixColumnPair A B =
      CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        D * cstarMatrixColumnPair A B := by
  exact cstarMatrix_reflectionAverage_compression_of_fixed
    (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B))
    (cstarMatrixColumnPairRangeReflection A B) D
    (cstarMatrixColumnPair A B)
    (cstarMatrixColumnPair_conjTranspose_mul_rangeReflection_of_sum hAB)
    (cstarMatrixColumnPairRangeReflection_mul_columnPair_of_sum hAB)

/-- The block-column reflection average is invariant under conjugation by the
range reflection. -/
theorem cstarMatrixColumnPair_reflectionAverage_conj_rangeReflection_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    (D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    cstarMatrixColumnPairRangeReflection A B *
        ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) *
        cstarMatrixColumnPairRangeReflection A B =
      (1 / 2 : ℂ) •
        (D + cstarMatrixColumnPairRangeReflection A B * D *
          cstarMatrixColumnPairRangeReflection A B) := by
  exact cstarMatrix_reflectionAverage_conj_of_involutive
    (cstarMatrixColumnPairRangeReflection A B) D
    (cstarMatrixColumnPairRangeReflection_mul_self_of_sum hAB)

/-- The block-column reflection average commutes with the range reflection. -/
theorem cstarMatrixColumnPair_reflectionAverage_commute_rangeReflection_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    (D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    cstarMatrixColumnPairRangeReflection A B *
        ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) =
      ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) *
        cstarMatrixColumnPairRangeReflection A B := by
  exact cstarMatrix_reflectionAverage_commute_of_involutive
    (cstarMatrixColumnPairRangeReflection A B) D
    (cstarMatrixColumnPairRangeReflection_mul_self_of_sum hAB)

/-- The block-column reflection average commutes with the range projection
`VVᴴ`. -/
theorem cstarMatrixColumnPair_reflectionAverage_commute_rangeProjection_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    (D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    cstarMatrixColumnPairRangeProjection A B *
        ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) =
      ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) *
        cstarMatrixColumnPairRangeProjection A B := by
  exact cstarMatrix_commute_projection_of_commute_reflection
    (cstarMatrixColumnPairRangeProjection A B)
    ((1 / 2 : ℂ) •
      (D + cstarMatrixColumnPairRangeReflection A B * D *
        cstarMatrixColumnPairRangeReflection A B))
    (cstarMatrixColumnPair_reflectionAverage_commute_rangeReflection_of_sum
      hAB D)

/-- If a block matrix commutes with the range projection \(VV^*\), then its
action on the block column factors through the compressed corner
`Vᴴ E V`. -/
theorem cstarMatrixColumnPair_mul_columnPair_eq_columnPair_compression_of_commute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    {E : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ}
    (hcomm :
      cstarMatrixColumnPairRangeProjection A B * E =
        E * cstarMatrixColumnPairRangeProjection A B) :
    E * cstarMatrixColumnPair A B =
      cstarMatrixColumnPair A B *
        (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
          E * cstarMatrixColumnPair A B) := by
  let V := cstarMatrixColumnPair A B
  let Vh := CStarMatrix.conjTranspose V
  let P := cstarMatrixColumnPairRangeProjection A B
  have hPV : P * V = V := by
    dsimp [P, V]
    exact cstarMatrixColumnPairRangeProjection_mul_columnPair_of_sum hAB
  calc
    E * cstarMatrixColumnPair A B = E * V := rfl
    _ = E * (P * V) := by
          rw [hPV]
    _ = (E * P) * V := by
          rw [← cstarMatrix_mul_assoc_rect E P V]
    _ = (P * E) * V := by
          rw [← hcomm]
    _ = ((V * Vh) * E) * V := rfl
    _ = (V * Vh) * (E * V) := by
          rw [cstarMatrix_mul_assoc_rect (V * Vh) E V]
    _ = V * (Vh * (E * V)) := by
          rw [← cstarMatrix_mul_assoc_rect V Vh (E * V)]
    _ = V * ((Vh * E) * V) := by
          rw [← cstarMatrix_mul_assoc_rect Vh E V]
    _ = cstarMatrixColumnPair A B *
          (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
            E * cstarMatrixColumnPair A B) := rfl

/-- If a block matrix commutes with the range projection \(VV^*\), then the
adjoint block row also factors through the compressed corner. -/
theorem cstarMatrixColumnPair_conjTranspose_mul_eq_compression_mul_conjTranspose_of_commute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    {E : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ}
    (hcomm :
      cstarMatrixColumnPairRangeProjection A B * E =
        E * cstarMatrixColumnPairRangeProjection A B) :
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) * E =
      (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
          E * cstarMatrixColumnPair A B) *
        CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) := by
  let V := cstarMatrixColumnPair A B
  let Vh := CStarMatrix.conjTranspose V
  let P := cstarMatrixColumnPairRangeProjection A B
  have hVhP : Vh * P = Vh := by
    dsimp [P, V, Vh]
    exact cstarMatrixColumnPair_conjTranspose_mul_rangeProjection_of_sum hAB
  calc
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) * E = Vh * E := rfl
    _ = (Vh * P) * E := by
          rw [hVhP]
    _ = Vh * (P * E) := by
          rw [cstarMatrix_mul_assoc_rect Vh P E]
    _ = Vh * (E * P) := by
          rw [hcomm]
    _ = (Vh * E) * P := by
          rw [← cstarMatrix_mul_assoc_rect Vh E P]
    _ = (Vh * E) * (V * Vh) := rfl
    _ = ((Vh * E) * V) * Vh := by
          rw [cstarMatrix_mul_assoc_rect (Vh * E) V Vh]
    _ = (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
          E * cstarMatrixColumnPair A B) *
        CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) := rfl

/-- The reflected block average acts on the block column through the same
compressed corner as the original block matrix. -/
theorem cstarMatrixColumnPair_reflectionAverage_mul_columnPair_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    (D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) *
        cstarMatrixColumnPair A B =
      cstarMatrixColumnPair A B *
        (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
          D * cstarMatrixColumnPair A B) := by
  let E : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
    (1 / 2 : ℂ) •
      (D + cstarMatrixColumnPairRangeReflection A B * D *
        cstarMatrixColumnPairRangeReflection A B)
  have hfactor :
      E * cstarMatrixColumnPair A B =
        cstarMatrixColumnPair A B *
          (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
            E * cstarMatrixColumnPair A B) := by
    exact cstarMatrixColumnPair_mul_columnPair_eq_columnPair_compression_of_commute
      hAB (cstarMatrixColumnPair_reflectionAverage_commute_rangeProjection_of_sum
        hAB D)
  have hcomp :=
    cstarMatrixColumnPair_reflectionAverage_compression_of_sum hAB D
  calc
    ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) *
        cstarMatrixColumnPair A B =
        E * cstarMatrixColumnPair A B := rfl
    _ = cstarMatrixColumnPair A B *
        (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
          E * cstarMatrixColumnPair A B) := hfactor
    _ = cstarMatrixColumnPair A B *
        (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
          D * cstarMatrixColumnPair A B) := by
          rw [hcomp]

/-- The reflected block average acts on the adjoint block row through the same
compressed corner as the original block matrix. -/
theorem cstarMatrixColumnPair_conjTranspose_mul_reflectionAverage_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hAB : star A * A + star B * B = 1)
    (D : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) =
      (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
          D * cstarMatrixColumnPair A B) *
        CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) := by
  let E : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
    (1 / 2 : ℂ) •
      (D + cstarMatrixColumnPairRangeReflection A B * D *
        cstarMatrixColumnPairRangeReflection A B)
  have hfactor :
      CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) * E =
        (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
            E * cstarMatrixColumnPair A B) *
          CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) := by
    exact cstarMatrixColumnPair_conjTranspose_mul_eq_compression_mul_conjTranspose_of_commute
      hAB (cstarMatrixColumnPair_reflectionAverage_commute_rangeProjection_of_sum
        hAB D)
  have hcomp :=
    cstarMatrixColumnPair_reflectionAverage_compression_of_sum hAB D
  calc
    CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
        ((1 / 2 : ℂ) •
          (D + cstarMatrixColumnPairRangeReflection A B * D *
            cstarMatrixColumnPairRangeReflection A B)) =
        CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) * E := rfl
    _ = (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
            E * cstarMatrixColumnPair A B) *
          CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) := hfactor
    _ = (CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) *
          D * cstarMatrixColumnPair A B) *
        CStarMatrix.conjTranspose (cstarMatrixColumnPair A B) := by
          rw [hcomp]

end NumStability
