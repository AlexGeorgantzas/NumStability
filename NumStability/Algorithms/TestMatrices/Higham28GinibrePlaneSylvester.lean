/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibrePlaneChart
import NumStability.Algorithms.TestMatrices.Higham28GinibreCharacteristicProduct
import Mathlib.RingTheory.Norm.Transitivity

/-! # Higham Chapter 28: the invariant-plane Sylvester determinant

This module evaluates the determinant of the nontrivial derivative block in
the affine invariant-two-plane chart.  For a deflated block `D` and a
represented two-dimensional action `C`, the Sylvester operator is

`X ↦ X C - D X`.

Its real determinant is exactly the determinant of the matrix obtained by
evaluating `charpoly C` at `D`.  The proof represents the operator as a
matrix of commuting polynomial blocks and applies the block determinant
theorem `Matrix.det_det`.

When `C` has negative discriminant, its two roots are a nonreal conjugate
pair.  Complexifying the determinant therefore turns it into the product of
the two corresponding characteristic polynomials of `D`.  The exact
real-Ginibre characteristic-product theorem then gives the unconditional
finite expectation.
-/

namespace NumStability

open MeasureTheory
open scoped BigOperators Polynomial

noncomputable section

local instance ginibrePlaneSylvesterBridgeModule (m : ℕ) :
    Module ℝ (Matrix (Fin m) (Fin 2) ℝ) :=
  @Matrix.module (Fin m) (Fin 2) ℝ ℝ inferInstance inferInstance inferInstance

private local instance ginibrePlaneSylvesterMeasurableSpace (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

/-- The Sylvester operator with independent deflated block `D` and
two-dimensional action `C`. -/
def ginibrePlaneSylvesterOperator {m : ℕ}
    (D : RSqMat m) (C : RSqMat 2) :
    Matrix (Fin m) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin m) (Fin 2) ℝ where
  toFun X := X * C - D * X
  map_add' X Y := by
    simp [Matrix.add_mul, Matrix.mul_add, sub_eq_add_neg]
    abel
  map_smul' r X := by
    simp [Matrix.smul_mul, Matrix.mul_smul, smul_sub]

/-- Coordinates in the standard matrix basis are ordinary matrix entries. -/
theorem ginibrePlane_stdBasis_repr_apply
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℝ) (i : m) (j : n) :
    (Matrix.stdBasis ℝ m n).repr M (i, j) = M i j := by
  simp [Matrix.stdBasis]

theorem ginibrePlane_stdBasis_repr_apply_pair
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℝ) (ij : m × n) :
    (Matrix.stdBasis ℝ m n).repr M ij = M ij.1 ij.2 := by
  rcases ij with ⟨i, j⟩
  exact ginibrePlane_stdBasis_repr_apply M i j

/-- The standard-basis matrix coefficient of the Sylvester operator. -/
theorem ginibrePlaneSylvesterOperator_toMatrix_apply {m : ℕ}
    (D : RSqMat m) (C : RSqMat 2) (ia jb : Fin m × Fin 2) :
    LinearMap.toMatrix (Matrix.stdBasis ℝ (Fin m) (Fin 2))
        (Matrix.stdBasis ℝ (Fin m) (Fin 2))
        (ginibrePlaneSylvesterOperator D C) ia jb =
      (if ia.1 = jb.1 then C jb.2 ia.2 else 0) -
        (if ia.2 = jb.2 then D ia.1 jb.1 else 0) := by
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  rw [LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single]
  simp only [ginibrePlaneSylvesterOperator, LinearMap.coe_mk,
    AddHom.coe_mk, map_sub, Finsupp.sub_apply]
  rw [ginibrePlane_stdBasis_repr_apply_pair,
    ginibrePlane_stdBasis_repr_apply_pair]
  fin_cases b
  · by_cases h : a = 0 <;>
      simp [Matrix.mul_apply, Matrix.single_apply, eq_comm, h]
  · by_cases h : a = 1 <;>
      simp [Matrix.mul_apply, Matrix.single_apply, eq_comm, h]

/-- The `2 × 2` polynomial block matrix whose evaluation at `D` represents
the Sylvester operator. -/
def ginibrePlaneSylvesterPolynomialBlock (C : RSqMat 2) :
    Matrix (Fin 2) (Fin 2) ℝ[X] :=
  fun a b => Polynomial.C (C b a) -
    if a = b then Polynomial.X else 0

/-- Evaluation of a real polynomial at a real square matrix. -/
def ginibrePlanePolynomialEvalMatrix {m : ℕ} (D : RSqMat m) :
    ℝ[X] →+* RSqMat m :=
  (Polynomial.aeval D).toRingHom

theorem ginibrePlanePolynomialEvalMatrix_block_apply {m : ℕ}
    (D : RSqMat m) (C : RSqMat 2)
    (a b : Fin 2) (i j : Fin m) :
    ginibrePlanePolynomialEvalMatrix D
        (ginibrePlaneSylvesterPolynomialBlock C a b) i j =
      (if i = j then C b a else 0) -
        (if a = b then D i j else 0) := by
  by_cases hab : a = b <;>
    simp [ginibrePlanePolynomialEvalMatrix,
      ginibrePlaneSylvesterPolynomialBlock, hab,
      Matrix.algebraMap_matrix_apply]

/-- The flattened polynomial-block matrix representing the Sylvester
operator, with column coordinate first. -/
def ginibrePlaneSylvesterBlockMatrix {m : ℕ}
    (D : RSqMat m) (C : RSqMat 2) :
    Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℝ :=
  Matrix.comp (Fin 2) (Fin 2) (Fin m) (Fin m) ℝ
    ((ginibrePlaneSylvesterPolynomialBlock C).map
      (ginibrePlanePolynomialEvalMatrix D))

/-- Reindexing the polynomial block matrix gives the ordinary
standard-basis matrix of the Sylvester operator. -/
theorem ginibrePlaneSylvesterOperator_toMatrix_eq_reindex_block {m : ℕ}
    (D : RSqMat m) (C : RSqMat 2) :
    LinearMap.toMatrix (Matrix.stdBasis ℝ (Fin m) (Fin 2))
        (Matrix.stdBasis ℝ (Fin m) (Fin 2))
        (ginibrePlaneSylvesterOperator D C) =
      Matrix.reindex (Equiv.prodComm (Fin 2) (Fin m))
        (Equiv.prodComm (Fin 2) (Fin m))
        (ginibrePlaneSylvesterBlockMatrix D C) := by
  ext ia jb
  rw [ginibrePlaneSylvesterOperator_toMatrix_apply]
  simp [ginibrePlaneSylvesterBlockMatrix, Matrix.reindex_apply,
    Matrix.comp_apply, ginibrePlanePolynomialEvalMatrix_block_apply]

/-- The determinant of the polynomial block matrix is `charpoly C`. -/
theorem ginibrePlaneSylvesterPolynomialBlock_det (C : RSqMat 2) :
    (ginibrePlaneSylvesterPolynomialBlock C).det = C.charpoly := by
  rw [Matrix.det_fin_two, Matrix.charpoly_fin_two]
  simp [ginibrePlaneSylvesterPolynomialBlock, Matrix.trace,
    Matrix.det_fin_two]
  ring

/-- Exact algebraic Sylvester determinant identity, with no spectral
assumption:

`det(X ↦ XC-DX) = det(charpoly(C) evaluated at D)`.
-/
theorem ginibrePlaneSylvesterOperator_det_eq_charpoly_aeval {m : ℕ}
    (D : RSqMat m) (C : RSqMat 2) :
    (@LinearMap.det (Matrix (Fin m) (Fin 2) ℝ) inferInstance ℝ
      inferInstance (ginibrePlaneSylvesterBridgeModule m))
        (ginibrePlaneSylvesterOperator D C) =
      ((Polynomial.aeval D) C.charpoly).det := by
  rw [← @LinearMap.det_toMatrix
    (Matrix (Fin m) (Fin 2) ℝ) inferInstance
    (Fin m × Fin 2) inferInstance inferInstance ℝ inferInstance
    (ginibrePlaneSylvesterBridgeModule m)
    (Matrix.stdBasis ℝ (Fin m) (Fin 2))
    (ginibrePlaneSylvesterOperator D C)]
  calc
    ((LinearMap.toMatrix (Matrix.stdBasis ℝ (Fin m) (Fin 2))
        (Matrix.stdBasis ℝ (Fin m) (Fin 2)))
        (ginibrePlaneSylvesterOperator D C)).det =
        (Matrix.reindex (Equiv.prodComm (Fin 2) (Fin m))
          (Equiv.prodComm (Fin 2) (Fin m))
          (ginibrePlaneSylvesterBlockMatrix D C)).det := by
      exact congrArg Matrix.det
        (ginibrePlaneSylvesterOperator_toMatrix_eq_reindex_block D C)
    _ = (ginibrePlaneSylvesterBlockMatrix D C).det :=
      Matrix.det_reindex_self (Equiv.prodComm (Fin 2) (Fin m)) _
    _ = (ginibrePlanePolynomialEvalMatrix D
          (ginibrePlaneSylvesterPolynomialBlock C).det).det := by
      exact (Matrix.det_det (ginibrePlaneSylvesterPolynomialBlock C)
        (ginibrePlanePolynomialEvalMatrix D)).symm
    _ = ((Polynomial.aeval D) C.charpoly).det := by
      rw [ginibrePlaneSylvesterPolynomialBlock_det]
      rfl

/-- The chart's actual Sylvester block satisfies the same no-premise
characteristic-polynomial evaluation identity. -/
theorem ginibrePlaneSylvesterLinearMap_det_eq_charpoly_aeval {m : ℕ}
    (q : GinibrePlaneChartCoordinates m) :
    (@LinearMap.det (Matrix (Fin m) (Fin 2) ℝ) inferInstance ℝ
      inferInstance (ginibrePlaneSylvesterBridgeModule m))
        (ginibrePlaneSylvesterLinearMap q) =
      ((Polynomial.aeval (ginibrePlaneChartDeflatedBlock q))
        (ginibrePlaneChartAction q).charpoly).det := by
  simpa [ginibrePlaneSylvesterOperator, ginibrePlaneSylvesterLinearMap] using
    ginibrePlaneSylvesterOperator_det_eq_charpoly_aeval
      (ginibrePlaneChartDeflatedBlock q) (ginibrePlaneChartAction q)

/-- The discriminant of the characteristic polynomial of a real `2 × 2`
matrix. -/
def ginibrePlaneActionDiscriminant (C : RSqMat 2) : ℝ :=
  C.trace ^ 2 - 4 * C.det

/-- The upper-half-plane root of `charpoly C` when the discriminant is
negative. -/
def ginibrePlaneActionUpperRoot (C : RSqMat 2) : ℂ :=
  ⟨C.trace / 2, Real.sqrt (-ginibrePlaneActionDiscriminant C) / 2⟩

theorem ginibrePlaneActionUpperRoot_add_conj (C : RSqMat 2) :
    ginibrePlaneActionUpperRoot C +
        starRingEnd ℂ (ginibrePlaneActionUpperRoot C) =
      Complex.ofReal C.trace := by
  apply Complex.ext
  · simp [ginibrePlaneActionUpperRoot]
  · simp [ginibrePlaneActionUpperRoot]

theorem ginibrePlaneActionUpperRoot_mul_conj
    (C : RSqMat 2) (hdisc : ginibrePlaneActionDiscriminant C < 0) :
    ginibrePlaneActionUpperRoot C *
        starRingEnd ℂ (ginibrePlaneActionUpperRoot C) =
      Complex.ofReal C.det := by
  have hrad : 0 ≤ -ginibrePlaneActionDiscriminant C :=
    le_of_lt (neg_pos.mpr hdisc)
  have hsqrt : Real.sqrt (-ginibrePlaneActionDiscriminant C) ^ 2 =
      -ginibrePlaneActionDiscriminant C := Real.sq_sqrt hrad
  apply Complex.ext
  · simp [ginibrePlaneActionUpperRoot, Complex.mul_re]
    unfold ginibrePlaneActionDiscriminant at hsqrt ⊢
    nlinarith
  · simp [ginibrePlaneActionUpperRoot, Complex.mul_im]
    ring

/-- Explicit evaluation of the quadratic characteristic polynomial at a
matrix. -/
theorem ginibrePlane_charpoly_aeval_fin_two {m : ℕ}
    (D : RSqMat m) (C : RSqMat 2) :
    (Polynomial.aeval D) C.charpoly =
      D ^ 2 - C.trace • D + C.det • (1 : RSqMat m) := by
  rw [Matrix.charpoly_fin_two]
  simp [map_sub, map_add, map_mul, map_pow, Algebra.smul_def]

/-- Over `ℂ`, a negative-discriminant `2 × 2` characteristic polynomial
factors at the explicit upper root and its conjugate. -/
theorem ginibrePlane_charpoly_map_complex_factor
    (C : RSqMat 2) (hdisc : ginibrePlaneActionDiscriminant C < 0) :
    C.charpoly.map Complex.ofRealHom =
      (Polynomial.X - Polynomial.C (ginibrePlaneActionUpperRoot C)) *
        (Polynomial.X - Polynomial.C
          (starRingEnd ℂ (ginibrePlaneActionUpperRoot C))) := by
  have hsum := ginibrePlaneActionUpperRoot_add_conj C
  have hprod := ginibrePlaneActionUpperRoot_mul_conj C hdisc
  rw [Matrix.charpoly_fin_two]
  simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  have hsum' : Complex.ofRealHom C.trace =
      ginibrePlaneActionUpperRoot C +
        starRingEnd ℂ (ginibrePlaneActionUpperRoot C) := by
    simpa using hsum.symm
  have hprod' : Complex.ofRealHom C.det =
      ginibrePlaneActionUpperRoot C *
        starRingEnd ℂ (ginibrePlaneActionUpperRoot C) := by
    simpa using hprod.symm
  rw [hsum', hprod']
  simp only [map_add, map_mul]
  ring

/-- Complexification commutes with matrix polynomial evaluation. -/
theorem ginibrePlane_map_aeval_charpoly_complex {m : ℕ}
    (D : RSqMat m) (C : RSqMat 2) :
    ((Polynomial.aeval D) C.charpoly).map Complex.ofReal =
      (Polynomial.aeval (D.map Complex.ofReal))
        (C.charpoly.map Complex.ofRealHom) := by
  let ψ : RSqMat m →+* Matrix (Fin m) (Fin m) ℂ :=
    Complex.ofRealHom.mapMatrix
  have hcomm :
      (algebraMap ℂ (Matrix (Fin m) (Fin m) ℂ)).comp Complex.ofRealHom =
        ψ.comp (algebraMap ℝ (RSqMat m)) := by
    ext r i j
    by_cases hij : i = j <;>
      simp [ψ, Matrix.algebraMap_matrix_apply, hij]
  exact Polynomial.map_aeval_eq_aeval_map hcomm C.charpoly D

/-- The complexified quadratic matrix polynomial is the product of its two
linear conjugate factors. -/
theorem ginibrePlane_charpoly_aeval_map_complex_eq_product {m : ℕ}
    (D : RSqMat m) (C : RSqMat 2)
    (hdisc : ginibrePlaneActionDiscriminant C < 0) :
    ((Polynomial.aeval D) C.charpoly).map Complex.ofReal =
      (Matrix.scalar (Fin m) (ginibrePlaneActionUpperRoot C) -
          D.map Complex.ofReal) *
        (Matrix.scalar (Fin m)
            (starRingEnd ℂ (ginibrePlaneActionUpperRoot C)) -
          D.map Complex.ofReal) := by
  rw [ginibrePlane_map_aeval_charpoly_complex]
  rw [ginibrePlane_charpoly_map_complex_factor C hdisc]
  simp [Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def,
    Matrix.scalar_apply]
  have hz : D.map Complex.ofReal -
        Matrix.diagonal (fun _ : Fin m => ginibrePlaneActionUpperRoot C) =
      -(Matrix.diagonal
          (fun _ : Fin m => ginibrePlaneActionUpperRoot C) -
        D.map Complex.ofReal) := by
    abel
  have hw : D.map Complex.ofReal -
        Matrix.diagonal (fun _ : Fin m =>
          starRingEnd ℂ (ginibrePlaneActionUpperRoot C)) =
      -(Matrix.diagonal (fun _ : Fin m =>
          starRingEnd ℂ (ginibrePlaneActionUpperRoot C)) -
        D.map Complex.ofReal) := by
    abel
  rw [hz, hw, neg_mul_neg]

/-- Pointwise conjugate characteristic-product form of the real Sylvester
determinant. -/
theorem ginibrePlaneSylvesterOperator_det_complex_eq_characteristicProduct
    {m : ℕ} (D : RSqMat m) (C : RSqMat 2)
    (hdisc : ginibrePlaneActionDiscriminant C < 0) :
    Complex.ofReal
        ((@LinearMap.det (Matrix (Fin m) (Fin 2) ℝ) inferInstance ℝ
          inferInstance (ginibrePlaneSylvesterBridgeModule m))
          (ginibrePlaneSylvesterOperator D C)) =
      (Matrix.scalar (Fin m) (ginibrePlaneActionUpperRoot C) -
          D.map Complex.ofReal).det *
        (Matrix.scalar (Fin m)
            (starRingEnd ℂ (ginibrePlaneActionUpperRoot C)) -
          D.map Complex.ofReal).det := by
  rw [ginibrePlaneSylvesterOperator_det_eq_charpoly_aeval]
  calc
    Complex.ofReal (((Polynomial.aeval D) C.charpoly).det) =
        (((Polynomial.aeval D) C.charpoly).map Complex.ofReal).det := by
      exact RingHom.map_det Complex.ofRealHom
        ((Polynomial.aeval D) C.charpoly)
    _ = ((Matrix.scalar (Fin m) (ginibrePlaneActionUpperRoot C) -
            D.map Complex.ofReal) *
          (Matrix.scalar (Fin m)
              (starRingEnd ℂ (ginibrePlaneActionUpperRoot C)) -
            D.map Complex.ofReal)).det := by
      rw [ginibrePlane_charpoly_aeval_map_complex_eq_product D C hdisc]
    _ = _ := Matrix.det_mul _ _

/-- The chart Sylvester block itself has the conjugate
characteristic-product form. -/
theorem ginibrePlaneSylvesterLinearMap_det_complex_eq_characteristicProduct
    {m : ℕ} (q : GinibrePlaneChartCoordinates m)
    (hdisc : ginibrePlaneActionDiscriminant
      (ginibrePlaneChartAction q) < 0) :
    Complex.ofReal
        ((@LinearMap.det (Matrix (Fin m) (Fin 2) ℝ) inferInstance ℝ
          inferInstance (ginibrePlaneSylvesterBridgeModule m))
          (ginibrePlaneSylvesterLinearMap q)) =
      (Matrix.scalar (Fin m)
          (ginibrePlaneActionUpperRoot (ginibrePlaneChartAction q)) -
        (ginibrePlaneChartDeflatedBlock q).map Complex.ofReal).det *
      (Matrix.scalar (Fin m)
          (starRingEnd ℂ
            (ginibrePlaneActionUpperRoot (ginibrePlaneChartAction q))) -
        (ginibrePlaneChartDeflatedBlock q).map Complex.ofReal).det := by
  simpa [ginibrePlaneSylvesterOperator, ginibrePlaneSylvesterLinearMap] using
    ginibrePlaneSylvesterOperator_det_complex_eq_characteristicProduct
      (ginibrePlaneChartDeflatedBlock q) (ginibrePlaneChartAction q) hdisc

/-- Exact expectation of the invariant-plane Sylvester determinant for an
independent standard real-Ginibre deflated block.  It depends on `C` only
through `det C`:

`𝔼_D det(X ↦ XC-DX) = m! ∑_{k=0}^m det(C)^k/k!`.
-/
theorem integral_realGinibre_ginibrePlaneSylvesterOperator_det
    {m : ℕ} (C : RSqMat 2)
    (hdisc : ginibrePlaneActionDiscriminant C < 0) :
    (∫ D : RSqMat m,
        (@LinearMap.det (Matrix (Fin m) (Fin 2) ℝ) inferInstance ℝ
          inferInstance (ginibrePlaneSylvesterBridgeModule m))
          (ginibrePlaneSylvesterOperator D C)
      ∂realGinibreMeasure m) =
      (m.factorial : ℝ) *
        ∑ k ∈ Finset.range (m + 1),
          C.det ^ k / (k.factorial : ℝ) := by
  apply Complex.ofReal_injective
  calc
    Complex.ofReal
        (∫ D : RSqMat m,
          (@LinearMap.det (Matrix (Fin m) (Fin 2) ℝ) inferInstance ℝ
            inferInstance (ginibrePlaneSylvesterBridgeModule m))
            (ginibrePlaneSylvesterOperator D C)
          ∂realGinibreMeasure m) =
        ∫ D : RSqMat m,
          Complex.ofReal
            ((@LinearMap.det (Matrix (Fin m) (Fin 2) ℝ) inferInstance ℝ
              inferInstance (ginibrePlaneSylvesterBridgeModule m))
              (ginibrePlaneSylvesterOperator D C))
          ∂realGinibreMeasure m := by
      exact (integral_complex_ofReal
        (μ := realGinibreMeasure m)
        (f := fun D : RSqMat m =>
          (@LinearMap.det (Matrix (Fin m) (Fin 2) ℝ) inferInstance ℝ
            inferInstance (ginibrePlaneSylvesterBridgeModule m))
            (ginibrePlaneSylvesterOperator D C))).symm
    _ = ∫ D : RSqMat m,
          (Matrix.scalar (Fin m) (ginibrePlaneActionUpperRoot C) -
              D.map Complex.ofReal).det *
            (Matrix.scalar (Fin m)
                (starRingEnd ℂ (ginibrePlaneActionUpperRoot C)) -
              D.map Complex.ofReal).det
          ∂realGinibreMeasure m := by
      apply integral_congr_ae
      filter_upwards with D
      exact
        ginibrePlaneSylvesterOperator_det_complex_eq_characteristicProduct
          D C hdisc
    _ = (m.factorial : ℂ) *
          ∑ k ∈ Finset.range (m + 1),
            (ginibrePlaneActionUpperRoot C *
              starRingEnd ℂ (ginibrePlaneActionUpperRoot C)) ^ k /
                (k.factorial : ℂ) :=
      integral_realGinibre_characteristicProduct_conj m
        (ginibrePlaneActionUpperRoot C)
    _ = Complex.ofReal
          ((m.factorial : ℝ) *
            ∑ k ∈ Finset.range (m + 1),
              C.det ^ k / (k.factorial : ℝ)) := by
      rw [ginibrePlaneActionUpperRoot_mul_conj C hdisc]
      norm_num

end

end NumStability
