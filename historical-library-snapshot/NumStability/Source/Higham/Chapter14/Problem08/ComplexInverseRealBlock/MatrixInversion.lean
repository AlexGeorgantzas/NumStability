import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Chapter14 Problem08 ComplexInverseRealBlock MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham, 2nd ed., Chapter 14, Problem 14.8:
    real block representation of a complex matrix `A = B + i C`, using the
    product index `Fin 2 x Fin n` for the source `2n x 2n` matrix
    `[[B, -C], [C, B]]`. -/
noncomputable def higham14_problem14_8_realBlockMatrix {n : ℕ}
    (A : CMatrix n n) :
    (Fin 2 × Fin n) → (Fin 2 × Fin n) → ℝ :=
  fun p q =>
    if p.1 = (0 : Fin 2) then
      if q.1 = (0 : Fin 2) then (A p.2 q.2).re else -(A p.2 q.2).im
    else
      if q.1 = (0 : Fin 2) then (A p.2 q.2).im else (A p.2 q.2).re

/-- Pack a real `2n` vector, indexed as real and imaginary blocks, into a
    complex vector. -/
noncomputable def higham14_problem14_8_realToComplexVec {n : ℕ}
    (x : Fin 2 × Fin n → ℝ) : CVec n :=
  fun i => ((x ((0 : Fin 2), i) : ℝ) : ℂ) +
    Complex.I * ((x ((1 : Fin 2), i) : ℝ) : ℂ)

/-- Unpack a complex vector into its real and imaginary blocks. -/
noncomputable def higham14_problem14_8_complexToRealVec {n : ℕ}
    (z : CVec n) : Fin 2 × Fin n → ℝ :=
  fun p => if p.1 = (0 : Fin 2) then (z p.2).re else (z p.2).im

/-- The real part of the Hermitian quadratic form `z^* A z`, written with the
    repository's concrete complex matrix-vector action. -/
noncomputable def higham14_problem14_8_complexQuadraticForm {n : ℕ}
    (A : CMatrix n n) (z : CVec n) : ℝ :=
  (∑ i : Fin n, star (z i) * complexMatrixVecMul A z i).re

/-- Product-indexed symmetric positive definite predicate for the real block
    matrix in Problem 14.8.  This is the `Fin 2 x Fin n` version of the
    source's `2n x 2n` SPD statement. -/
def higham14_problem14_8_realBlockSymPosDef {n : ℕ}
    (M : (Fin 2 × Fin n) → (Fin 2 × Fin n) → ℝ) : Prop :=
  IsSymmetricFiniteMatrix M ∧
    ∀ x : Fin 2 × Fin n → ℝ, (∃ p : Fin 2 × Fin n, x p ≠ 0) →
      0 < finiteQuadraticForm M x

/-- Source-facing Hermitian positive definite predicate for the complex input
    matrix in Problem 14.8.  Positivity is stated as positivity of the real
    part of `z^* A z`. -/
def higham14_problem14_8_complexHermitianPosDef {n : ℕ}
    (A : CMatrix n n) : Prop :=
  (∀ i j : Fin n, A i j = star (A j i)) ∧
    ∀ z : CVec n, (∃ i : Fin n, z i ≠ 0) →
      0 < higham14_problem14_8_complexQuadraticForm A z

lemma higham14_problem14_8_complexToRealVec_realToComplexVec {n : ℕ}
    (x : Fin 2 × Fin n → ℝ) :
    higham14_problem14_8_complexToRealVec
      (higham14_problem14_8_realToComplexVec x) = x := by
  funext p
  rcases p with ⟨b, i⟩
  cases b using Fin.cases with
  | zero =>
      simp [higham14_problem14_8_complexToRealVec,
        higham14_problem14_8_realToComplexVec]
  | succ b =>
      cases b using Fin.cases with
      | zero =>
          simp [higham14_problem14_8_complexToRealVec,
            higham14_problem14_8_realToComplexVec]
      | succ b => exact Fin.elim0 b

lemma higham14_problem14_8_realToComplexVec_complexToRealVec {n : ℕ}
    (z : CVec n) :
    higham14_problem14_8_realToComplexVec
      (higham14_problem14_8_complexToRealVec z) = z := by
  funext i
  apply Complex.ext <;>
    simp [higham14_problem14_8_complexToRealVec,
      higham14_problem14_8_realToComplexVec]

/-- Matrix-vector action of the real block matrix is exactly the real/imaginary
    unpacking of the complex matrix-vector action. -/
theorem higham14_problem14_8_realBlockMatrix_finiteMatVec_eq_complexToRealVec
    {n : ℕ} (A : CMatrix n n) (x : Fin 2 × Fin n → ℝ) :
    finiteMatVec (higham14_problem14_8_realBlockMatrix A) x =
      higham14_problem14_8_complexToRealVec
        (complexMatrixVecMul A (higham14_problem14_8_realToComplexVec x)) := by
  funext p
  rcases p with ⟨b, i⟩
  cases b using Fin.cases with
  | zero =>
      simp [finiteMatVec, higham14_problem14_8_realBlockMatrix,
        higham14_problem14_8_complexToRealVec,
        higham14_problem14_8_realToComplexVec, complexMatrixVecMul,
        Fintype.sum_prod_type, Finset.sum_add_distrib, mul_add, sub_eq_add_neg]
  | succ b =>
      cases b using Fin.cases with
      | zero =>
          simp [finiteMatVec, higham14_problem14_8_realBlockMatrix,
            higham14_problem14_8_complexToRealVec,
            higham14_problem14_8_realToComplexVec, complexMatrixVecMul,
            Fintype.sum_prod_type, Finset.sum_add_distrib, mul_add]
      | succ b => exact Fin.elim0 b

/-- Problem 14.8, inverse transfer, right-inverse direction:
    if `Ainv` is a right inverse of the complex matrix `A`, then the real block
    matrix of `Ainv` is a right inverse of the real block matrix of `A`. -/
theorem higham14_problem14_8_realBlockMatrix_rightInverse_of_complex
    {n : ℕ} {A Ainv : CMatrix n n}
    (h : IsComplexMatrixRightInverse A Ainv) :
    ∀ x : Fin 2 × Fin n → ℝ,
      finiteMatVec (higham14_problem14_8_realBlockMatrix A)
        (finiteMatVec (higham14_problem14_8_realBlockMatrix Ainv) x) = x := by
  intro x
  rw [higham14_problem14_8_realBlockMatrix_finiteMatVec_eq_complexToRealVec,
    higham14_problem14_8_realBlockMatrix_finiteMatVec_eq_complexToRealVec,
    higham14_problem14_8_realToComplexVec_complexToRealVec, h,
    higham14_problem14_8_complexToRealVec_realToComplexVec]

/-- Problem 14.8, inverse transfer, left-inverse direction:
    if `Ainv` is a left inverse of the complex matrix `A`, then the real block
    matrix of `Ainv` is a left inverse of the real block matrix of `A`. -/
theorem higham14_problem14_8_realBlockMatrix_leftInverse_of_complex
    {n : ℕ} {A Ainv : CMatrix n n}
    (h : IsComplexMatrixLeftInverse A Ainv) :
    ∀ x : Fin 2 × Fin n → ℝ,
      finiteMatVec (higham14_problem14_8_realBlockMatrix Ainv)
        (finiteMatVec (higham14_problem14_8_realBlockMatrix A) x) = x := by
  intro x
  rw [higham14_problem14_8_realBlockMatrix_finiteMatVec_eq_complexToRealVec,
    higham14_problem14_8_realBlockMatrix_finiteMatVec_eq_complexToRealVec,
    higham14_problem14_8_realToComplexVec_complexToRealVec, h,
    higham14_problem14_8_complexToRealVec_realToComplexVec]

/-- Problem 14.8, two-sided inverse transfer for the real block matrix
    `[[Re A, -Im A], [Im A, Re A]]`. -/
theorem higham14_problem14_8_realBlockMatrix_inverse_of_complex
    {n : ℕ} {A Ainv : CMatrix n n}
    (h : IsComplexMatrixInverse A Ainv) :
    (∀ x : Fin 2 × Fin n → ℝ,
      finiteMatVec (higham14_problem14_8_realBlockMatrix Ainv)
        (finiteMatVec (higham14_problem14_8_realBlockMatrix A) x) = x) ∧
    (∀ x : Fin 2 × Fin n → ℝ,
      finiteMatVec (higham14_problem14_8_realBlockMatrix A)
        (finiteMatVec (higham14_problem14_8_realBlockMatrix Ainv) x) = x) := by
  exact ⟨higham14_problem14_8_realBlockMatrix_leftInverse_of_complex h.1,
    higham14_problem14_8_realBlockMatrix_rightInverse_of_complex h.2⟩

/-- The real block quadratic form is the real part of `z^* A z`, where
    `z` is the complex vector packed from the real and imaginary blocks. -/
theorem higham14_problem14_8_realBlockMatrix_quadratic_eq_complexQuadratic
    {n : ℕ} (A : CMatrix n n) (x : Fin 2 × Fin n → ℝ) :
    finiteQuadraticForm (higham14_problem14_8_realBlockMatrix A) x =
      higham14_problem14_8_complexQuadraticForm A
        (higham14_problem14_8_realToComplexVec x) := by
  unfold finiteQuadraticForm higham14_problem14_8_complexQuadraticForm
  rw [higham14_problem14_8_realBlockMatrix_finiteMatVec_eq_complexToRealVec]
  simp [higham14_problem14_8_complexToRealVec,
    higham14_problem14_8_realToComplexVec, complexMatrixVecMul,
    Fintype.sum_prod_type, Finset.sum_add_distrib, mul_add, sub_eq_add_neg]
  ring

lemma higham14_problem14_8_realBlockMatrix_symmetric_of_hermitian
    {n : ℕ} {A : CMatrix n n}
    (hHerm : ∀ i j : Fin n, A i j = star (A j i)) :
    IsSymmetricFiniteMatrix (higham14_problem14_8_realBlockMatrix A) := by
  intro p q
  rcases p with ⟨bp, i⟩
  rcases q with ⟨bq, j⟩
  cases bp using Fin.cases with
  | zero =>
      cases bq using Fin.cases with
      | zero =>
          change (A i j).re = (A j i).re
          simpa using congrArg Complex.re (hHerm i j)
      | succ bq =>
          cases bq using Fin.cases with
          | zero =>
              change -(A i j).im = (A j i).im
              have him : (A i j).im = -(A j i).im := by
                simpa using congrArg Complex.im (hHerm i j)
              linarith
          | succ bq => exact Fin.elim0 bq
  | succ bp =>
      cases bp using Fin.cases with
      | zero =>
          cases bq using Fin.cases with
          | zero =>
              change (A i j).im = -(A j i).im
              simpa using congrArg Complex.im (hHerm i j)
          | succ bq =>
              cases bq using Fin.cases with
              | zero =>
                  change (A i j).re = (A j i).re
                  simpa using congrArg Complex.re (hHerm i j)
              | succ bq => exact Fin.elim0 bq
      | succ bp => exact Fin.elim0 bp

lemma higham14_problem14_8_realToComplexVec_ne_zero_of_real_ne_zero
    {n : ℕ} {x : Fin 2 × Fin n → ℝ} {p : Fin 2 × Fin n}
    (hp : x p ≠ 0) :
    ∃ i : Fin n, higham14_problem14_8_realToComplexVec x i ≠ 0 := by
  rcases p with ⟨b, i⟩
  refine ⟨i, ?_⟩
  intro hz
  apply hp
  cases b using Fin.cases with
  | zero =>
      have hre := congrArg Complex.re hz
      simpa [higham14_problem14_8_realToComplexVec] using hre
  | succ b =>
      cases b using Fin.cases with
      | zero =>
          have him := congrArg Complex.im hz
          simpa [higham14_problem14_8_realToComplexVec] using him
      | succ b => exact Fin.elim0 b

/-- Problem 14.8, Hermitian positive definite transfer:
    if the complex matrix is Hermitian positive definite, then its real block
    representation `[[Re A, -Im A], [Im A, Re A]]` is SPD, in product-indexed
    `2n` form. -/
theorem higham14_problem14_8_realBlockMatrix_symPosDef_of_complexHermitianPosDef
    {n : ℕ} {A : CMatrix n n}
    (hA : higham14_problem14_8_complexHermitianPosDef A) :
    higham14_problem14_8_realBlockSymPosDef
      (higham14_problem14_8_realBlockMatrix A) := by
  constructor
  · exact higham14_problem14_8_realBlockMatrix_symmetric_of_hermitian hA.1
  · intro x hx
    rw [higham14_problem14_8_realBlockMatrix_quadratic_eq_complexQuadratic]
    rcases hx with ⟨p, hp⟩
    exact hA.2 (higham14_problem14_8_realToComplexVec x)
      (higham14_problem14_8_realToComplexVec_ne_zero_of_real_ne_zero hp)

end NumStability
