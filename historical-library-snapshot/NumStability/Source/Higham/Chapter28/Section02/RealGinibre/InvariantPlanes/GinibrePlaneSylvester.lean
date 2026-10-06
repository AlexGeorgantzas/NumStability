import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Sym.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Topology.Instances.Matrix
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra

/-!
# Chapter28 Section02 RealGinibre InvariantPlanes GinibrePlaneSylvester

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibrePlaneSylvester` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open MeasureTheory

open scoped BigOperators Polynomial

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

/-- The determinant of the polynomial block matrix is `charpoly C`. -/
theorem ginibrePlaneSylvesterPolynomialBlock_det (C : RSqMat 2) :
    (ginibrePlaneSylvesterPolynomialBlock C).det = C.charpoly := by
  rw [Matrix.det_fin_two, Matrix.charpoly_fin_two]
  simp [ginibrePlaneSylvesterPolynomialBlock, Matrix.trace,
    Matrix.det_fin_two]
  ring

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

end NumStability

end
