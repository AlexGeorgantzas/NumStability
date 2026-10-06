import NumStability.Algorithms.TestMatrices.Higham28Contracts
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.PerturbationTheory

namespace NumStability

open scoped BigOperators Matrix.Norms.L2Operator

/-! # Higham Chapter 28: the optimal Pascal singularizing perturbation

This file closes the spectral part of the perturbation statement on p. 520.
The smallest eigenpair is selected from Mathlib's decreasingly ordered
Hermitian spectrum.  No eigenpair, minimality, or norm identity is assumed.
-/

private theorem vecNorm2_module_smul {n : ℕ} (a : ℝ) (x : RVec n) :
    vecNorm2 (a • x) = |a| * vecNorm2 x := by
  simpa only [Pi.smul_apply, smul_eq_mul] using vecNorm2_smul a x

private theorem vecNorm2_module_neg {n : ℕ} (x : RVec n) :
    vecNorm2 (-x) = vecNorm2 x := by
  simpa only [Pi.neg_apply] using vecNorm2_neg x

/-- Symmetry of the explicit Pascal matrix in the generic finite-matrix
vocabulary used by the Hermitian spectral bridge. -/
theorem pascalMatrix_isSymmetricFiniteMatrix (n : ℕ) :
    IsSymmetricFiniteMatrix (pascalMatrix n) :=
  (pascalMatrix_isSymPosDef_explicit n).1

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

/-- The smallest Pascal eigenvalue gives the exact inverse operator norm. -/
theorem opNorm2_pascalInverseMatrix_eq_inv_smallestEigenvalue (n : ℕ) :
    opNorm2 (pascalInverseMatrix (n + 1)) =
      (pascalSmallestEigenvalue n)⁻¹ := by
  let P := pascalMatrix (n + 1)
  let Pinv := pascalInverseMatrix (n + 1)
  let lam := pascalSmallestEigenvalue n
  let v := pascalSmallestEigenvector n
  have hlam : 0 < lam := pascalSmallestEigenvalue_pos n
  have hmin : ∀ i : Fin (n + 1),
      lam ≤ finiteHermitianEigenvalues P
        (pascalMatrix_isSymmetricFiniteMatrix (n + 1)) i := by
    intro i
    exact pascalSmallestEigenvalue_le n i
  have hLower : finiteLoewnerLe
      (fun i j : Fin (n + 1) => lam * finiteIdMatrix i j) P :=
    finiteLoewnerLe_smul_id_of_le_finiteHermitianEigenvalues
      P (pascalMatrix_isSymmetricFiniteMatrix (n + 1)) hmin
  have hRight : IsRightInverse (n + 1) P Pinv :=
    (pascalMatrix_pascalInverseMatrix_isInverse (n + 1)).2
  have hPinvUpper : finiteLoewnerLe Pinv
      (fun i j : Fin (n + 1) => lam⁻¹ * finiteIdMatrix i j) :=
    finiteLoewnerLe_right_inverse_upper_of_smul_id_le
      P Pinv hlam hLower hRight
  have hInvNonneg : 0 ≤ lam⁻¹ := le_of_lt (inv_pos.mpr hlam)
  have hOpLePred : finiteOpNorm2Le Pinv lam⁻¹ :=
    finiteOpNorm2Le_of_finitePSD_of_finiteLoewnerLe_smul_id
      Pinv hInvNonneg
      (pascalInverseMatrix_isSymmetricFiniteMatrix (n + 1))
      (pascalInverseMatrix_finitePSD (n + 1)) hPinvUpper
  have hUpper : opNorm2 Pinv ≤ lam⁻¹ :=
    opNorm2_le_of_finiteOpNorm2Le Pinv hInvNonneg hOpLePred
  have hvunit : vecNorm2 v = 1 := vecNorm2_pascalSmallestEigenvector n
  have heig : Matrix.mulVec P v = lam • v :=
    pascalMatrix_mulVec_smallestEigenvector n
  have hPinvEig : Matrix.mulVec Pinv v = lam⁻¹ • v := by
    have h := congrArg (fun z => Matrix.mulVec Pinv z) heig
    change Matrix.mulVec Pinv (Matrix.mulVec P v) =
      Matrix.mulVec Pinv (lam • v) at h
    have hInvP : (Pinv : RSqMat (n + 1)) * P = 1 := by
      simpa [P, Pinv, pascalInverseMatrix] using signedGram_mul_pascalMatrix (n + 1)
    have hscaled : Matrix.mulVec Pinv (lam • v) =
        lam • Matrix.mulVec Pinv v := by
      exact Matrix.mulVec_smul _ _ _
    rw [Matrix.mulVec_mulVec, hInvP, Matrix.one_mulVec, hscaled] at h
    ext i
    have hi := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
    calc
      Matrix.mulVec Pinv v i = lam⁻¹ * (lam * Matrix.mulVec Pinv v i) := by
        field_simp [ne_of_gt hlam]
      _ = lam⁻¹ * v i := by rw [← hi]
  have hAction := opNorm2Le_opNorm2 Pinv v
  change vecNorm2 (Matrix.mulVec Pinv v) ≤ opNorm2 Pinv * vecNorm2 v at hAction
  rw [hPinvEig, vecNorm2_module_smul, hvunit] at hAction
  have hLowerNorm : lam⁻¹ ≤ opNorm2 Pinv := by
    simpa [abs_of_pos (inv_pos.mpr hlam)] using hAction
  exact le_antisymm hUpper hLowerNorm

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

/-- Exact operator norm of the optimal rank-one perturbation. -/
theorem opNorm2_pascalOptimalSingularizingPerturbation (n : ℕ) :
    opNorm2 (pascalOptimalSingularizingPerturbation n) =
      pascalSmallestEigenvalue n := by
  let lam := pascalSmallestEigenvalue n
  let v := pascalSmallestEigenvector n
  have hlam : 0 ≤ lam := le_of_lt (pascalSmallestEigenvalue_pos n)
  have hv : vecNorm2 v = 1 := vecNorm2_pascalSmallestEigenvector n
  have hEq : pascalOptimalSingularizingPerturbation n =
      residualRankOnePerturbation (n + 1) (-lam • v) v := by
    have hvsq : vecNorm2Sq v = 1 := by
      rw [← vecNorm2_sq, hv]
      norm_num
    ext i j
    simp [pascalOptimalSingularizingPerturbation,
      residualRankOnePerturbation, hvsq, lam, v]
  have hPred := opNorm2Le_residualRankOnePerturbation
    (n + 1) (-lam • v) v (by simpa [hv])
  have hratio : vecNorm2 (-lam • v) / vecNorm2 v = lam := by
    rw [vecNorm2_module_smul, hv]
    simp [abs_of_nonneg hlam]
  rw [hratio] at hPred
  have hUpper : opNorm2 (pascalOptimalSingularizingPerturbation n) ≤ lam := by
    rw [hEq]
    apply opNorm2_le_of_opNorm2Le _ hlam
    exact hPred
  have hAction := opNorm2Le_opNorm2
    (pascalOptimalSingularizingPerturbation n) v
  have hmul := pascalOptimalSingularizingPerturbation_mulVec n
  change Matrix.mulVec (pascalOptimalSingularizingPerturbation n) v =
      -(lam • v) at hmul
  change vecNorm2 (Matrix.mulVec
      (pascalOptimalSingularizingPerturbation n) v) ≤
    opNorm2 (pascalOptimalSingularizingPerturbation n) * vecNorm2 v at hAction
  rw [hmul, vecNorm2_module_neg, vecNorm2_module_smul, hv] at hAction
  have hLower : lam ≤ opNorm2 (pascalOptimalSingularizingPerturbation n) := by
    simpa [abs_of_nonneg hlam] using hAction
  exact le_antisymm hUpper hLower

/-- Every perturbation that makes the Pascal matrix singular has norm at
least the reciprocal norm of its explicit inverse. -/
theorem pascal_singularizing_perturbation_norm_lower_bound
    (n : ℕ) (E : RSqMat (n + 1))
    (hsing : ∃ z : RVec (n + 1), z ≠ 0 ∧
      Matrix.mulVec (pascalMatrix (n + 1) + E) z = 0) :
    (opNorm2 (pascalInverseMatrix (n + 1)))⁻¹ ≤ opNorm2 E := by
  obtain ⟨z, hz, hkernel⟩ := hsing
  have hznorm : 0 < vecNorm2 z := by
    have hne : vecNorm2 z ≠ 0 := by
      intro hzero
      apply hz
      funext i
      exact (vecNorm2_eq_zero_iff z).mp hzero i
    exact lt_of_le_of_ne (vecNorm2_nonneg z) (Ne.symm hne)
  let y : RVec (n + 1) := fun i => (vecNorm2 z)⁻¹ * z i
  have hyunit : vecNorm2 y = 1 := vecNorm2_inv_smul_self_of_pos z hznorm
  have hcancel : Matrix.mulVec (pascalMatrix (n + 1)) y =
      -Matrix.mulVec E y := by
    have hk : Matrix.mulVec (pascalMatrix (n + 1)) z =
        -Matrix.mulVec E z := by
      rw [Matrix.add_mulVec] at hkernel
      exact eq_neg_of_add_eq_zero_left hkernel
    have hy : y = (vecNorm2 z)⁻¹ • z := by
      ext i
      simp [y]
    rw [hy, Matrix.mulVec_smul, Matrix.mulVec_smul, hk]
    simp
  have hLower := opNorm2_inv_recip_le_vecNorm2_matMulVec_of_isRightInverse
    (pascalMatrix (n + 1)) (pascalInverseMatrix (n + 1))
    (pascalMatrix_pascalInverseMatrix_isInverse (n + 1)).2 hyunit
  have hUpper := opNorm2Le_opNorm2 E y
  change (opNorm2 (pascalInverseMatrix (n + 1)))⁻¹ ≤
    vecNorm2 (Matrix.mulVec (pascalMatrix (n + 1)) y) at hLower
  change vecNorm2 (Matrix.mulVec E y) ≤ opNorm2 E * vecNorm2 y at hUpper
  rw [hcancel, vecNorm2_module_neg] at hLower
  rw [hyunit, mul_one] at hUpper
  exact hLower.trans hUpper

/-- The rank-one eigenvector perturbation attains the exact distance to
singularity in operator 2-norm. -/
theorem pascalOptimalPerturbation_is_operator2_minimal (n : ℕ) :
    opNorm2 (pascalOptimalSingularizingPerturbation n) =
        (opNorm2 (pascalInverseMatrix (n + 1)))⁻¹ ∧
      ∀ E : RSqMat (n + 1),
        (∃ z : RVec (n + 1), z ≠ 0 ∧
          Matrix.mulVec (pascalMatrix (n + 1) + E) z = 0) →
        opNorm2 (pascalOptimalSingularizingPerturbation n) ≤ opNorm2 E := by
  have hInv := opNorm2_pascalInverseMatrix_eq_inv_smallestEigenvalue n
  have hlam := pascalSmallestEigenvalue_pos n
  have hnorm := opNorm2_pascalOptimalSingularizingPerturbation n
  have hvalue : opNorm2 (pascalOptimalSingularizingPerturbation n) =
      (opNorm2 (pascalInverseMatrix (n + 1)))⁻¹ := by
    calc
      opNorm2 (pascalOptimalSingularizingPerturbation n) =
          pascalSmallestEigenvalue n := hnorm
      _ = ((pascalSmallestEigenvalue n)⁻¹)⁻¹ :=
          (inv_inv (pascalSmallestEigenvalue n)).symm
      _ = (opNorm2 (pascalInverseMatrix (n + 1)))⁻¹ := by rw [hInv]
  constructor
  · exact hvalue
  · intro E hsing
    rw [hvalue]
    exact pascal_singularizing_perturbation_norm_lower_bound n E hsing

end NumStability
