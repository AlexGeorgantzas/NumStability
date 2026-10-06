import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.TestMatrices.Pascal.Basic
import NumStability.Analysis.TestMatrices.Pascal.Exact
import NumStability.Analysis.TestMatrices.Pascal.PascalSpectral
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11

/-!
# Chapter28 Section04 Pascal PascalSpectral

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28PascalSpectral` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators Matrix.Norms.L2Operator

/-- The final index in Mathlib's canonically sorted eigenvalue list. -/
noncomputable def pascalSmallestSortedIndex (n : ℕ) :
    Fin (Fintype.card (Fin (n + 1))) :=
  Fin.cast (by simp) (Fin.last n)

/-- The matrix-index label corresponding to the final sorted eigenvalue. -/
noncomputable def pascalSmallestEigenIndex (n : ℕ) : Fin (n + 1) :=
  (Fintype.equivOfCardEq
    (Fintype.card_fin (Fintype.card (Fin (n + 1)))))
    (pascalSmallestSortedIndex n)

/-- The smallest eigenvalue of the order-`n+1` symmetric Pascal matrix. -/
noncomputable def pascalSmallestEigenvalue (n : ℕ) : ℝ :=
  finiteHermitianEigenvalues (pascalMatrix (n + 1))
    (pascalMatrix_isSymmetricFiniteMatrix (n + 1))
    (pascalSmallestEigenIndex n)

/-- A unit eigenvector belonging to `pascalSmallestEigenvalue`. -/
noncomputable def pascalSmallestEigenvector (n : ℕ) : RVec (n + 1) :=
  ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian
      (pascalMatrix (n + 1))
      (pascalMatrix_isSymmetricFiniteMatrix (n + 1))).eigenvectorBasis
        (pascalSmallestEigenIndex n))

/-- The selected eigenvalue is the final entry of the sorted Hermitian list. -/
theorem pascalSmallestEigenvalue_eq_eigenvalues₀ (n : ℕ) :
    pascalSmallestEigenvalue n =
      (IsSymmetricFiniteMatrix.to_matrix_isHermitian
        (pascalMatrix (n + 1))
        (pascalMatrix_isSymmetricFiniteMatrix (n + 1))).eigenvalues₀
          (pascalSmallestSortedIndex n) := by
  simp [pascalSmallestEigenvalue, finiteHermitianEigenvalues,
    pascalSmallestEigenIndex, Matrix.IsHermitian.eigenvalues]

/-- Every Pascal eigenvalue is at least the selected final sorted value. -/
theorem pascalSmallestEigenvalue_le (n : ℕ) (i : Fin (n + 1)) :
    pascalSmallestEigenvalue n ≤
      finiteHermitianEigenvalues (pascalMatrix (n + 1))
        (pascalMatrix_isSymmetricFiniteMatrix (n + 1)) i := by
  let hP := IsSymmetricFiniteMatrix.to_matrix_isHermitian
    (pascalMatrix (n + 1)) (pascalMatrix_isSymmetricFiniteMatrix (n + 1))
  let e : Fin (Fintype.card (Fin (n + 1))) ≃ Fin (n + 1) :=
    Fintype.equivOfCardEq
      (Fintype.card_fin (Fintype.card (Fin (n + 1))))
  have hle : e.symm i ≤ pascalSmallestSortedIndex n := by
    apply Fin.le_iff_val_le_val.mpr
    have hlt := (e.symm i).isLt
    simp [pascalSmallestSortedIndex] at hlt ⊢
    omega
  have hanti := hP.eigenvalues₀_antitone hle
  simpa [pascalSmallestEigenvalue_eq_eigenvalues₀, finiteHermitianEigenvalues,
    Matrix.IsHermitian.eigenvalues, e, hP] using hanti

/-- The selected vector has repository Euclidean norm one. -/
theorem vecNorm2_pascalSmallestEigenvector (n : ℕ) :
    vecNorm2 (pascalSmallestEigenvector n) = 1 := by
  have hsq :=
    finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
      (pascalMatrix (n + 1))
      (pascalMatrix_isSymmetricFiniteMatrix (n + 1))
      (pascalSmallestEigenIndex n)
  change vecNorm2Sq (pascalSmallestEigenvector n) = 1 at hsq
  have hnormsq := vecNorm2_sq (pascalSmallestEigenvector n)
  have hnonneg := vecNorm2_nonneg (pascalSmallestEigenvector n)
  nlinarith

/-- The selected unit vector is nonzero. -/
theorem pascalSmallestEigenvector_ne_zero (n : ℕ) :
    pascalSmallestEigenvector n ≠ 0 := by
  intro hzero
  have hnorm := vecNorm2_pascalSmallestEigenvector n
  rw [hzero] at hnorm
  simp [vecNorm2, vecNorm2Sq] at hnorm

/-- The selected pair is an actual Pascal eigenpair. -/
theorem pascalMatrix_mulVec_smallestEigenvector (n : ℕ) :
    Matrix.mulVec (pascalMatrix (n + 1))
        (pascalSmallestEigenvector n) =
      pascalSmallestEigenvalue n • pascalSmallestEigenvector n := by
  simpa [pascalSmallestEigenvector, pascalSmallestEigenvalue,
    finiteMatVec, matMulVec] using
    finiteMatVec_finiteHermitianEigenvector_eq
      (pascalMatrix (n + 1))
      (pascalMatrix_isSymmetricFiniteMatrix (n + 1))
      (pascalSmallestEigenIndex n)

/-- Positive definiteness makes the selected smallest eigenvalue positive. -/
theorem pascalSmallestEigenvalue_pos (n : ℕ) :
    0 < pascalSmallestEigenvalue n := by
  let v := pascalSmallestEigenvector n
  have hv : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact pascalSmallestEigenvector_ne_zero n (funext h)
  have hq := pascalMatrix_quadratic_pos (n + 1) v hv
  have heig :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      (pascalMatrix (n + 1))
      (pascalMatrix_isSymmetricFiniteMatrix (n + 1))
      (pascalSmallestEigenIndex n)
  have hunit :=
    finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
      (pascalMatrix (n + 1))
      (pascalMatrix_isSymmetricFiniteMatrix (n + 1))
      (pascalSmallestEigenIndex n)
  have heig' : finiteQuadraticForm (pascalMatrix (n + 1)) v =
      pascalSmallestEigenvalue n * finiteVecNorm2Sq v := by
    simpa [v, pascalSmallestEigenvector, pascalSmallestEigenvalue] using heig
  have hunit' : finiteVecNorm2Sq v = 1 := by
    simpa [v, pascalSmallestEigenvector] using hunit
  have hq' : 0 < finiteQuadraticForm (pascalMatrix (n + 1)) v := by
    simpa [finiteQuadraticForm_eq_sum_sum] using hq
  rw [heig', hunit'] at hq'
  simpa using hq'

/-- The explicit inverse of the Pascal matrix used in the norm formula. -/
noncomputable def pascalInverseMatrix (n : ℕ) : RSqMat n :=
  (signedPascal n).transpose * signedPascal n

theorem pascalMatrix_pascalInverseMatrix_isInverse (n : ℕ) :
    IsInverse n (pascalMatrix n) (pascalInverseMatrix n) := by
  constructor
  · intro i j
    have h := congrArg (fun M : RSqMat n => M i j)
      (signedGram_mul_pascalMatrix n)
    simpa [pascalInverseMatrix, Matrix.mul_apply, idMatrix] using h
  · intro i j
    have h := congrArg (fun M : RSqMat n => M i j)
      (pascalMatrix_mul_signedGram n)
    simpa [pascalInverseMatrix, Matrix.mul_apply, idMatrix] using h

/-- The explicit Pascal inverse is symmetric. -/
theorem pascalInverseMatrix_isSymmetricFiniteMatrix (n : ℕ) :
    IsSymmetricFiniteMatrix (pascalInverseMatrix n) := by
  apply IsSymmetricFiniteMatrix_of_eq_rectMatMul_transpose_self (signedPascal n)
  rfl

/-- The explicit Pascal inverse is positive semidefinite. -/
theorem pascalInverseMatrix_finitePSD (n : ℕ) :
    finitePSD (pascalInverseMatrix n) := by
  apply finitePSD_of_eq_rectMatMul_transpose_self (signedPascal n)
  rfl

/-- Exact l2 operator norm submultiplicativity in repository notation. -/
theorem opNorm2_matrix_mul_le {n : ℕ} (A B : RSqMat n) :
    opNorm2 (A * B) ≤ opNorm2 A * opNorm2 B := by
  letI := Matrix.instL2OpNormedAddCommGroup
    (m := Fin n) (n := Fin n) (𝕜 := ℝ)
  simpa [opNorm2] using Matrix.l2_opNorm_mul
    (A : Matrix (Fin n) (Fin n) ℝ) B

/-- Real transpose preserves the exact l2 operator norm. -/
theorem opNorm2_transpose_eq {n : ℕ} (A : RSqMat n) :
    opNorm2 A.transpose = opNorm2 A := by
  letI := Matrix.instL2OpNormedAddCommGroup
    (m := Fin n) (n := Fin n) (𝕜 := ℝ)
  simpa [opNorm2, Matrix.conjTranspose_apply] using
    Matrix.l2_opNorm_conjTranspose (A : Matrix (Fin n) (Fin n) ℝ)

/-- Exact norm of a real Gram product. -/
theorem opNorm2_transpose_mul_self (n : ℕ) (A : RSqMat n) :
    opNorm2 (A.transpose * A) = opNorm2 A * opNorm2 A := by
  letI := Matrix.instL2OpNormedAddCommGroup
    (m := Fin n) (n := Fin n) (𝕜 := ℝ)
  simpa [opNorm2, Matrix.conjTranspose_apply] using
    Matrix.l2_opNorm_conjTranspose_mul_self
      (A : Matrix (Fin n) (Fin n) ℝ)

/-- Exact norm of the oppositely ordered real Gram product. -/
theorem opNorm2_mul_transpose (n : ℕ) (A : RSqMat n) :
    opNorm2 (A * A.transpose) = opNorm2 A * opNorm2 A := by
  calc
    opNorm2 (A * A.transpose) =
        opNorm2 ((A.transpose).transpose * A.transpose) := by simp
    _ = opNorm2 A.transpose * opNorm2 A.transpose :=
      opNorm2_transpose_mul_self n A.transpose
    _ = opNorm2 A * opNorm2 A := by rw [opNorm2_transpose_eq]

/-- The alternating-sign diagonal is orthogonal. -/
theorem pascalSignDiagonal_isOrthogonal (n : ℕ) :
    IsOrthogonal n (pascalSignDiagonal n) := by
  have hT : matTranspose (pascalSignDiagonal n) = pascalSignDiagonal n := by
    ext i j
    have h := congrArg (fun M : RSqMat n => M i j)
      (pascalSignDiagonal_transpose n)
    simpa [matTranspose] using h
  rw [IsOrthogonal, hT]
  constructor <;> intro i j
  · have h := congrArg (fun M : RSqMat n => M i j)
      (pascalSignDiagonal_mul_self n)
    simpa [Matrix.mul_apply] using h
  · have h := congrArg (fun M : RSqMat n => M i j)
      (pascalSignDiagonal_mul_self n)
    simpa [Matrix.mul_apply] using h

/-- Right multiplication by the alternating-sign diagonal preserves the
exact operator 2-norm of the Pascal lower factor. -/
theorem opNorm2_signedPascal_eq_pascalLower (n : ℕ) :
    opNorm2 (signedPascal n) = opNorm2 (pascalLower n) := by
  let L := pascalLower n
  let D := pascalSignDiagonal n
  let S := signedPascal n
  have hD : opNorm2 D ≤ 1 :=
    opNorm2_le_of_opNorm2Le D zero_le_one
      (pascalSignDiagonal_isOrthogonal n).opNorm2Le_one
  have hS : S = L * D := by
    simpa [S, L, D] using signedPascal_eq_lower_mul_signDiagonal n
  have hSD : S * D = L := by
    calc
      S * D = (L * D) * D := by rw [hS]
      _ = L * (D * D) := by rw [Matrix.mul_assoc]
      _ = L := by
        rw [show D * D = 1 by
          simpa [D] using pascalSignDiagonal_mul_self n, Matrix.mul_one]
  apply le_antisymm
  · calc
      opNorm2 S = opNorm2 (L * D) := by rw [hS]
      _ ≤ opNorm2 L * opNorm2 D := opNorm2_matrix_mul_le L D
      _ ≤ opNorm2 L * 1 :=
        mul_le_mul_of_nonneg_left hD (opNorm2_nonneg L)
      _ = opNorm2 L := by ring
  · calc
      opNorm2 L = opNorm2 (S * D) := by rw [hSD]
      _ ≤ opNorm2 S * opNorm2 D := opNorm2_matrix_mul_le S D
      _ ≤ opNorm2 S * 1 :=
        mul_le_mul_of_nonneg_left hD (opNorm2_nonneg S)
      _ = opNorm2 S := by ring

/-- The Pascal matrix and its explicit inverse have equal operator 2-norm.
Both are Gram products; their factors differ only by an orthogonal sign
diagonal and by transposition. -/
theorem opNorm2_pascalInverseMatrix_eq_pascalMatrix (n : ℕ) :
    opNorm2 (pascalInverseMatrix n) = opNorm2 (pascalMatrix n) := by
  calc
    opNorm2 (pascalInverseMatrix n) =
        opNorm2 (signedPascal n) * opNorm2 (signedPascal n) := by
      simpa [pascalInverseMatrix] using
        opNorm2_transpose_mul_self n (signedPascal n)
    _ = opNorm2 (pascalLower n) * opNorm2 (pascalLower n) := by
      rw [opNorm2_signedPascal_eq_pascalLower]
    _ = opNorm2 (pascalMatrix n) := by
      rw [pascalMatrix_eq_lower_mul_transpose,
        opNorm2_mul_transpose]

/-- Higham's optimal rank-one Pascal perturbation `-lambda_min v v^T`. -/
noncomputable def pascalOptimalSingularizingPerturbation (n : ℕ) :
    RSqMat (n + 1) :=
  fun i j => -pascalSmallestEigenvalue n *
    pascalSmallestEigenvector n i * pascalSmallestEigenvector n j

/-- The optimal perturbation cancels the smallest-eigenvalue action. -/
theorem pascalOptimalSingularizingPerturbation_mulVec (n : ℕ) :
    Matrix.mulVec (pascalOptimalSingularizingPerturbation n)
        (pascalSmallestEigenvector n) =
      -(pascalSmallestEigenvalue n • pascalSmallestEigenvector n) := by
  ext i
  simp only [Matrix.mulVec, pascalOptimalSingularizingPerturbation,
    Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  change (∑ j : Fin (n + 1),
      (-pascalSmallestEigenvalue n * pascalSmallestEigenvector n i *
        pascalSmallestEigenvector n j) * pascalSmallestEigenvector n j) =
    -(pascalSmallestEigenvalue n * pascalSmallestEigenvector n i)
  have hsq : ∑ j : Fin (n + 1), pascalSmallestEigenvector n j ^ 2 = 1 := by
    simpa [vecNorm2Sq] using
      (show vecNorm2Sq (pascalSmallestEigenvector n) = 1 by
        rw [← vecNorm2_sq, vecNorm2_pascalSmallestEigenvector]
        norm_num)
  rw [show (∑ j : Fin (n + 1),
      (-pascalSmallestEigenvalue n * pascalSmallestEigenvector n i *
        pascalSmallestEigenvector n j) * pascalSmallestEigenvector n j) =
      (-pascalSmallestEigenvalue n * pascalSmallestEigenvector n i) *
        ∑ j : Fin (n + 1), pascalSmallestEigenvector n j ^ 2 by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring]
  rw [hsq]
  ring

/-- The rank-one update makes the Pascal matrix singular, with the selected
unit eigenvector as an explicit nonzero kernel vector. -/
theorem pascalOptimalPerturbation_has_nonzero_kernel (n : ℕ) :
    ∃ z : RVec (n + 1), z ≠ 0 ∧
      Matrix.mulVec
        (pascalMatrix (n + 1) + pascalOptimalSingularizingPerturbation n) z = 0 := by
  refine ⟨pascalSmallestEigenvector n,
    pascalSmallestEigenvector_ne_zero n, ?_⟩
  rw [Matrix.add_mulVec, pascalMatrix_mulVec_smallestEigenvector,
    pascalOptimalSingularizingPerturbation_mulVec]
  simp

end NumStability
