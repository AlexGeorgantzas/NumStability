-- Algorithms/Sylvester/Higham16VecNorm.lean
--
-- Vec/Frobenius norm bridges for Higham, Accuracy and Stability of
-- Numerical Algorithms, 2nd ed., Chapter 16.

import NumStability.Algorithms.Sylvester.Higham16PerturbationSigmaMin
import NumStability.Algorithms.Sylvester.Higham16PsiSigmaMin
import NumStability.Algorithms.Sylvester.Higham16LyapunovSigmaMin
import NumStability.Algorithms.Sylvester.Higham16
import NumStability.Algorithms.Sylvester.Higham16Spectrum

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2):
    vectorization is an isometry from the Frobenius squared norm to the
    Euclidean squared norm over the product index used by `Matrix.vec`. -/
theorem finiteVecNorm2Sq_vec_eq_frobNormSq (m n : Nat)
    (A : Matrix (Fin m) (Fin n) Real) :
    finiteVecNorm2Sq (Matrix.vec A) = frobNormSq A := by
  unfold finiteVecNorm2Sq frobNormSq
  calc
    (Finset.univ.sum fun p : Prod (Fin n) (Fin m) => Matrix.vec A p ^ 2)
        = Finset.univ.sum
            (fun j : Fin n => Finset.univ.sum (fun i : Fin m => A i j ^ 2)) := by
            change
              (Finset.univ.sum fun p : Prod (Fin n) (Fin m) =>
                A p.2 p.1 ^ 2) =
              Finset.univ.sum
                (fun j : Fin n => Finset.univ.sum (fun i : Fin m => A i j ^ 2))
            rw [Fintype.sum_prod_type' (fun j i => A i j ^ 2)]
    _ = Finset.univ.sum
            (fun i : Fin m => Finset.univ.sum (fun j : Fin n => A i j ^ 2)) := by
            rw [Finset.sum_comm]

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2):
    vectorization is an isometry from the Frobenius norm to the Euclidean norm
    over the product index used by `Matrix.vec`. -/
theorem finiteVecNorm2_vec_eq_frobNorm (m n : Nat)
    (A : Matrix (Fin m) (Fin n) Real) :
    finiteVecNorm2 (Matrix.vec A) = frobNorm A := by
  unfold finiteVecNorm2
  rw [finiteVecNorm2Sq_vec_eq_frobNormSq m n A,
    frobNorm_eq_sqrt_frobNormSq]

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2): source-numbered
    alias for the squared Frobenius/`vec` Euclidean norm isometry. -/
alias H16_eq16_2_finiteVecNorm2Sq_vec_eq_frobNormSq :=
  finiteVecNorm2Sq_vec_eq_frobNormSq

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2): source-numbered
    alias for the Frobenius/`vec` Euclidean norm isometry. -/
alias H16_eq16_2_finiteVecNorm2_vec_eq_frobNorm :=
  finiteVecNorm2_vec_eq_frobNorm

/-- Finite Gram matrix `P^T P` for an arbitrary finite index type.  This local
    Chapter 16 helper keeps the printed product-index vec coefficient without
    reindexing it through `Fin (n*n)`. -/
noncomputable def finiteMatrixGram {ι : Type*} [Fintype ι]
    (P : Matrix ι ι Real) : ι -> ι -> Real :=
  fun i j => Finset.sum Finset.univ fun k : ι => P k i * P k j

/-- The finite Gram matrix `P^T P` is symmetric. -/
theorem isSymmetricFiniteMatrix_finiteMatrixGram
    {ι : Type*} [Fintype ι] (P : Matrix ι ι Real) :
    IsSymmetricFiniteMatrix (finiteMatrixGram P) := by
  intro i j
  unfold finiteMatrixGram
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- Gram quadratic-form identity over an arbitrary finite index type:
    `x^T P^T P x = ||P x||_2^2`. -/
theorem finiteQuadraticForm_finiteMatrixGram_eq_finiteVecNorm2Sq_mulVec
    {ι : Type*} [Fintype ι] (P : Matrix ι ι Real) (x : ι -> Real) :
    finiteQuadraticForm (finiteMatrixGram P) x =
      finiteVecNorm2Sq (Matrix.mulVec P x) := by
  have hmv : forall i : ι,
      finiteMatVec (finiteMatrixGram P) x i =
        Finset.sum Finset.univ
          (fun k : ι => P k i * Matrix.mulVec P x k) := by
    intro i
    unfold finiteMatVec finiteMatrixGram Matrix.mulVec dotProduct
    calc
      (Finset.univ.sum fun j : ι =>
          (Finset.univ.sum fun k : ι => P k i * P k j) * x j)
          = Finset.univ.sum fun j : ι =>
              Finset.univ.sum fun k : ι => (P k i * P k j) * x j := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.sum_mul]
      _ = Finset.univ.sum fun k : ι =>
              Finset.univ.sum fun j : ι => (P k i * P k j) * x j := by
              rw [Finset.sum_comm]
      _ = Finset.univ.sum fun k : ι =>
              P k i * Finset.univ.sum fun j : ι => P k j * x j := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
  unfold finiteQuadraticForm finiteVecNorm2Sq
  calc
    (Finset.univ.sum fun i : ι => x i * finiteMatVec (finiteMatrixGram P) x i)
        = Finset.univ.sum fun i : ι =>
            x i *
              Finset.univ.sum
                (fun k : ι => P k i * Matrix.mulVec P x k) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hmv i]
    _ = Finset.univ.sum fun i : ι =>
          Finset.univ.sum fun k : ι =>
            x i * (P k i * Matrix.mulVec P x k) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
    _ = Finset.univ.sum fun k : ι =>
          Finset.univ.sum fun i : ι =>
            x i * (P k i * Matrix.mulVec P x k) := by
            rw [Finset.sum_comm]
    _ = Finset.univ.sum fun k : ι =>
          Matrix.mulVec P x k *
            Finset.univ.sum fun i : ι => P k i * x i := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = Finset.univ.sum fun k : ι =>
          Matrix.mulVec P x k * Matrix.mulVec P x k := by
            apply Finset.sum_congr rfl
            intro k _
            unfold Matrix.mulVec dotProduct
            rw [mul_comm]
    _ = Finset.univ.sum fun k : ι => Matrix.mulVec P x k ^ 2 := by
            apply Finset.sum_congr rfl
            intro k _
            ring

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2): source-numbered
    alias for the product-index Gram identity `x^T P^T P x = ||P x||_2^2`. -/
alias H16_eq16_2_finiteQuadraticForm_finiteMatrixGram_eq_finiteVecNorm2Sq_mulVec :=
  finiteQuadraticForm_finiteMatrixGram_eq_finiteVecNorm2Sq_mulVec

/-- Singular-value lower-bound certificate for an arbitrary finite-index real
    matrix, stated with the repository's generic finite Euclidean norm. -/
theorem finiteMatrixGram_sigmaMin_mul_finiteVecNorm2_le_mulVec
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι Real) {lam : Real} (hlam : 0 <= lam)
    (hEig : forall a : ι,
      lam <= finiteHermitianEigenvalues (finiteMatrixGram P)
        (isSymmetricFiniteMatrix_finiteMatrixGram P) a)
    (x : ι -> Real) :
    Real.sqrt lam * finiteVecNorm2 x <=
      finiteVecNorm2 (Matrix.mulVec P x) := by
  have hray :=
    rayleigh_lower_bound_of_le_finiteHermitianEigenvalues
      (finiteMatrixGram P) (isSymmetricFiniteMatrix_finiteMatrixGram P)
      hEig x
  have hleft_sq :
      (Real.sqrt lam * finiteVecNorm2 x) ^ 2 =
        lam * finiteVecNorm2Sq x := by
    rw [mul_pow, Real.sq_sqrt hlam, finiteVecNorm2_sq]
  have hright_sq :
      finiteVecNorm2 (Matrix.mulVec P x) ^ 2 =
        finiteVecNorm2Sq (Matrix.mulVec P x) :=
    finiteVecNorm2_sq _
  have hsq :
      (Real.sqrt lam * finiteVecNorm2 x) ^ 2 <=
        finiteVecNorm2 (Matrix.mulVec P x) ^ 2 := by
    rw [hleft_sq, hright_sq,
      <- finiteQuadraticForm_finiteMatrixGram_eq_finiteVecNorm2Sq_mulVec P x]
    exact hray
  exact le_of_sq_le_sq_of_nonneg (finiteVecNorm2_nonneg _) hsq

/-- A scalar-identity Loewner lower bound controls every locally named
    Hermitian eigenvalue from below.  This is the lower-side companion to
    `finiteHermitianEigenvalues_le_of_finiteLoewnerLe_smul_id`. -/
theorem le_finiteHermitianEigenvalues_of_finiteLoewnerLe_smul_id
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι -> ι -> Real) (hM : IsSymmetricFiniteMatrix M) {c : Real}
    (hLe : finiteLoewnerLe (fun i j => c * finiteIdMatrix i j) M) (a : ι) :
    c <= finiteHermitianEigenvalues M hM a := by
  let v : ι -> Real :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian M hM).eigenvectorBasis a)
  have hq := hLe v
  have heig :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      M hM a
  have hnorm :=
    finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one M hM a
  change finiteQuadraticForm (fun i j => c * finiteIdMatrix i j) v <=
    finiteQuadraticForm M v at hq
  rw [finiteQuadraticForm_smul_finiteIdMatrix, heig, hnorm] at hq
  simpa using hq

/-- A concrete sigma-min norm lower bound for `P` implies the corresponding
    lower bound on every eigenvalue of its finite Gram matrix `P^T P`. -/
theorem finiteMatrixGram_eigenvalues_ge_of_sigmaMin_lower_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι Real) {sigma : Real} (hsigma : 0 <= sigma)
    (hCoeff : forall x : ι -> Real,
      sigma * finiteVecNorm2 x <= finiteVecNorm2 (Matrix.mulVec P x)) :
    forall a : ι,
      sigma ^ 2 <= finiteHermitianEigenvalues (finiteMatrixGram P)
        (isSymmetricFiniteMatrix_finiteMatrixGram P) a := by
  intro a
  refine
    le_finiteHermitianEigenvalues_of_finiteLoewnerLe_smul_id
      (finiteMatrixGram P) (isSymmetricFiniteMatrix_finiteMatrixGram P) ?_ a
  intro x
  have hcoeff := hCoeff x
  have hleft_nonneg : 0 <= sigma * finiteVecNorm2 x :=
    mul_nonneg hsigma (finiteVecNorm2_nonneg x)
  have hright_nonneg : 0 <= finiteVecNorm2 (Matrix.mulVec P x) :=
    finiteVecNorm2_nonneg _
  have habs :
      |sigma * finiteVecNorm2 x| <=
        |finiteVecNorm2 (Matrix.mulVec P x)| := by
    simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using hcoeff
  have hsq :
      (sigma * finiteVecNorm2 x) ^ 2 <=
        finiteVecNorm2 (Matrix.mulVec P x) ^ 2 :=
    (sq_le_sq).mpr habs
  have hsq_bound :
      sigma ^ 2 * finiteVecNorm2Sq x <=
        finiteVecNorm2Sq (Matrix.mulVec P x) := by
    simpa [mul_pow, finiteVecNorm2_sq] using hsq
  change finiteQuadraticForm
      (fun i j : ι => sigma ^ 2 * finiteIdMatrix i j) x <=
    finiteQuadraticForm (finiteMatrixGram P) x
  rw [finiteQuadraticForm_smul_finiteIdMatrix,
    finiteQuadraticForm_finiteMatrixGram_eq_finiteVecNorm2Sq_mulVec]
  exact hsq_bound

/-- A positive finite Euclidean lower-bound certificate for a square matrix
    rules out a nonzero kernel vector, hence gives determinant nonsingularity.
    This is the generic finite-index bridge used by the Chapter 16 vec/Kronecker
    coefficient wrappers. -/
theorem finiteMatrix_det_ne_zero_of_sigmaMin_lower_bound
    {idx : Type*} [Fintype idx] [DecidableEq idx]
    (P : Matrix idx idx Real) {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : idx -> Real,
      sigma * finiteVecNorm2 x <= finiteVecNorm2 (Matrix.mulVec P x)) :
    P.det ≠ 0 := by
  intro hdet
  obtain ⟨x, hxne, hxzero⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hnorm_ne : finiteVecNorm2 x ≠ 0 := by
    intro hnorm
    apply hxne
    funext i
    exact (finiteVecNorm2_eq_zero_iff x).mp hnorm i
  have hnorm_pos : 0 < finiteVecNorm2 x :=
    lt_of_le_of_ne (finiteVecNorm2_nonneg x) (Ne.symm hnorm_ne)
  have hprod_pos : 0 < sigma * finiteVecNorm2 x :=
    mul_pos hsigma hnorm_pos
  have hmul_zero : finiteVecNorm2 (Matrix.mulVec P x) = 0 := by
    rw [hxzero]
    exact finiteVecNorm2_zero
  have hzero : sigma * finiteVecNorm2 x <= 0 := by
    simpa [hmul_zero] using hCoeff x
  exact (not_le_of_gt hprod_pos) hzero

/-- A positive lower bound on every finite-Gram eigenvalue gives determinant
    nonsingularity of the original square matrix. -/
theorem finiteMatrix_det_ne_zero_of_gram_eigenvalues
    {idx : Type*} [Fintype idx] [DecidableEq idx]
    (P : Matrix idx idx Real) {lam : Real} (hlam : 0 < lam)
    (hEig : forall a : idx,
      lam <= finiteHermitianEigenvalues (finiteMatrixGram P)
        (isSymmetricFiniteMatrix_finiteMatrixGram P) a) :
    P.det ≠ 0 := by
  exact
    finiteMatrix_det_ne_zero_of_sigmaMin_lower_bound P
      (Real.sqrt_pos.mpr hlam)
      (finiteMatrixGram_sigmaMin_mul_finiteVecNorm2_le_mulVec
        P (le_of_lt hlam) hEig)

/-- A concrete left inverse with a finite operator-2 bound gives the inverse
    action bound on the original product-index matrix.  This is a reusable
    bridge from exact inverse certificates to the `P`-coefficient route, without
    assuming a sigma-min theorem as a hypothesis. -/
theorem finiteVecNorm2_le_mul_mulVec_of_left_inverse_finiteOpNorm2Le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Pinv : Matrix ι ι Real) {M : Real}
    (hLeft : Pinv * P = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    forall x : ι -> Real,
      finiteVecNorm2 x <= M * finiteVecNorm2 (Matrix.mulVec P x) := by
  classical
  have hLeftFinite : finiteMatMul Pinv P = finiteIdMatrix := by
    ext i j
    have hentry :=
      congrArg (fun Q : Matrix ι ι Real => Q i j) hLeft
    simpa [finiteMatMul, finiteIdMatrix, Matrix.mul_apply] using hentry
  intro x
  have hPx : Matrix.mulVec P x = finiteMatVec P x := by
    ext i
    rfl
  have hrecover :
      finiteMatVec Pinv (Matrix.mulVec P x) = x := by
    calc
      finiteMatVec Pinv (Matrix.mulVec P x)
          = finiteMatVec Pinv (finiteMatVec P x) := by rw [hPx]
      _ = finiteMatVec (finiteMatMul Pinv P) x := by
          rw [finiteMatVec_finiteMatMul]
      _ = finiteMatVec finiteIdMatrix x := by rw [hLeftFinite]
      _ = x := finiteMatVec_finiteIdMatrix x
  have hbound := hPinv (Matrix.mulVec P x)
  simpa [hrecover] using hbound

/-- A concrete left inverse with operator-2 radius `M` gives the coefficient
    sigma-min lower bound with `sigma = 1 / M`.  This is the product-index
    route needed once an arbitrary nondiagonal vec/Kronecker inverse has been
    constructed and norm-bounded. -/
theorem finiteMatrix_sigmaMin_of_left_inverse_finiteOpNorm2Le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Pinv : Matrix ι ι Real) {M : Real} (hM : 0 < M)
    (hLeft : Pinv * P = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    forall x : ι -> Real,
      (1 / M) * finiteVecNorm2 x <= finiteVecNorm2 (Matrix.mulVec P x) := by
  intro x
  have hinvBound :=
    finiteVecNorm2_le_mul_mulVec_of_left_inverse_finiteOpNorm2Le
      P Pinv hLeft hPinv x
  have hcomm :
      finiteVecNorm2 x <= finiteVecNorm2 (Matrix.mulVec P x) * M := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hinvBound
  have hdiv : finiteVecNorm2 x / M <= finiteVecNorm2 (Matrix.mulVec P x) :=
    (div_le_iff₀ hM).mpr hcomm
  simpa [one_div, div_eq_inv_mul] using hdiv

/-- A concrete left inverse with operator-2 radius `M` gives a lower bound
    `(1 / M)^2` on every eigenvalue of the finite Gram matrix `P^T P`. -/
theorem finiteMatrixGram_eigenvalues_ge_of_left_inverse_finiteOpNorm2Le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Pinv : Matrix ι ι Real) {M : Real} (hM : 0 < M)
    (hLeft : Pinv * P = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    forall a : ι,
      (1 / M) ^ 2 <= finiteHermitianEigenvalues (finiteMatrixGram P)
        (isSymmetricFiniteMatrix_finiteMatrixGram P) a := by
  exact
    finiteMatrixGram_eigenvalues_ge_of_sigmaMin_lower_bound P
      (by positivity)
      (finiteMatrix_sigmaMin_of_left_inverse_finiteOpNorm2Le
        P Pinv hM hLeft hPinv)

/-- A concrete left inverse with operator-2 radius `M` gives determinant
    nonsingularity of the original finite matrix through the same lower-bound
    certificate used by the Chapter 16 vec/Kronecker estimates. -/
theorem finiteMatrix_det_ne_zero_of_left_inverse_finiteOpNorm2Le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Pinv : Matrix ι ι Real) {M : Real} (hM : 0 < M)
    (hLeft : Pinv * P = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    P.det ≠ 0 := by
  exact
    finiteMatrix_det_ne_zero_of_sigmaMin_lower_bound P
      (one_div_pos.mpr hM)
      (finiteMatrix_sigmaMin_of_left_inverse_finiteOpNorm2Le
        P Pinv hM hLeft hPinv)

/-- A determinant nonsingularity certificate for a finite square matrix makes
    its `mulVec` action injective.  This is the exact linear-algebra bridge used
    below for Chapter 16 vectorized coefficient systems. -/
theorem finiteMatrix_mulVec_injective_of_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι Real) (hdet : P.det ≠ 0) :
    Function.Injective (Matrix.mulVec P) := by
  intro x y hxy
  have h := congrArg (Matrix.mulVec P⁻¹) hxy
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact h

/-- A determinant nonsingularity certificate gives the exact trivial-kernel
    statement for the finite matrix `mulVec` action. -/
theorem finiteMatrix_mulVec_eq_zero_iff_of_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι Real) (hdet : P.det ≠ 0) (x : ι -> Real) :
    Matrix.mulVec P x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hzero :
        Matrix.mulVec P x = Matrix.mulVec P (0 : ι -> Real) := by
      simpa using hx
    exact (finiteMatrix_mulVec_injective_of_det_ne_zero P hdet) hzero
  · intro hx
    simp [hx]

/-- A determinant nonsingularity certificate for a finite square matrix makes
    its `mulVec` action surjective, using Mathlib's nonsingular inverse. -/
theorem finiteMatrix_mulVec_surjective_of_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι Real) (hdet : P.det ≠ 0) :
    Function.Surjective (Matrix.mulVec P) := by
  intro c
  refine ⟨Matrix.mulVec P⁻¹ c, ?_⟩
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

/-- A determinant nonsingularity certificate makes Mathlib's nonsingular
    inverse a left inverse on vectors. -/
theorem finiteMatrix_nonsingInv_mulVec_mulVec_of_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι Real) (hdet : P.det ≠ 0) (x : ι -> Real) :
    Matrix.mulVec P⁻¹ (Matrix.mulVec P x) = x := by
  rw [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

/-- A determinant nonsingularity certificate makes Mathlib's nonsingular
    inverse a right inverse on vectors, giving an explicit exact solve. -/
theorem finiteMatrix_mulVec_nonsingInv_mulVec_of_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι Real) (hdet : P.det ≠ 0) (c : ι -> Real) :
    Matrix.mulVec P (Matrix.mulVec P⁻¹ c) = c := by
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

/-- A determinant nonsingularity certificate identifies every exact solution
    of a finite matrix equation with the nonsingular-inverse solution. -/
theorem finiteMatrix_eq_nonsingInv_mulVec_of_mulVec_eq_of_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι Real) (hdet : P.det ≠ 0)
    {x c : ι -> Real} (hx : Matrix.mulVec P x = c) :
    x = Matrix.mulVec P⁻¹ c := by
  calc
    x = Matrix.mulVec P⁻¹ (Matrix.mulVec P x) := by
        exact (finiteMatrix_nonsingInv_mulVec_mulVec_of_det_ne_zero
          P hdet x).symm
    _ = Matrix.mulVec P⁻¹ c := by rw [hx]

/-- A determinant nonsingularity certificate identifies the finite matrix
    equation exactly with the nonsingular-inverse vector formula. -/
theorem finiteMatrix_mulVec_eq_iff_eq_nonsingInv_mulVec_of_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι Real) (hdet : P.det ≠ 0)
    {x c : ι -> Real} :
    Matrix.mulVec P x = c ↔ x = Matrix.mulVec P⁻¹ c := by
  constructor
  · intro hx
    exact
      finiteMatrix_eq_nonsingInv_mulVec_of_mulVec_eq_of_det_ne_zero
        P hdet hx
  · intro hx
    rw [hx]
    exact finiteMatrix_mulVec_nonsingInv_mulVec_of_det_ne_zero P hdet c

/-- A determinant nonsingularity certificate gives a unique exact solution
    certificate whose witness is Mathlib's nonsingular-inverse vector formula. -/
theorem existsUnique_finiteMatrix_nonsingInv_mulVec_solution_of_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι Real) (hdet : P.det ≠ 0) (c : ι -> Real) :
    ∃! x : ι -> Real,
      Matrix.mulVec P x = c ∧ x = Matrix.mulVec P⁻¹ c := by
  refine ⟨Matrix.mulVec P⁻¹ c, ?_, ?_⟩
  · exact ⟨finiteMatrix_mulVec_nonsingInv_mulVec_of_det_ne_zero P hdet c, rfl⟩
  · intro y hy
    exact
      (finiteMatrix_mulVec_eq_iff_eq_nonsingInv_mulVec_of_det_ne_zero
        P hdet).mp hy.1

/-- A determinant nonsingularity certificate for a finite square matrix makes
    its `mulVec` action bijective. -/
theorem finiteMatrix_mulVec_bijective_of_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι Real) (hdet : P.det ≠ 0) :
    Function.Bijective (Matrix.mulVec P) :=
  ⟨finiteMatrix_mulVec_injective_of_det_ne_zero P hdet,
    finiteMatrix_mulVec_surjective_of_det_ne_zero P hdet⟩

/-- A determinant nonsingularity certificate for a finite square matrix gives
    existence and uniqueness for every exact vector right-hand side. -/
theorem existsUnique_finiteMatrix_mulVec_of_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι Real) (hdet : P.det ≠ 0) (c : ι -> Real) :
    ∃! x : ι -> Real, Matrix.mulVec P x = c := by
  have hinj := finiteMatrix_mulVec_injective_of_det_ne_zero P hdet
  have hsurj := finiteMatrix_mulVec_surjective_of_det_ne_zero P hdet
  obtain ⟨x, hx⟩ := hsurj c
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hinj (by rw [hy, hx])

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.1)-(16.3):
    determinant nonsingularity of the Sylvester vec/Kronecker coefficient
    gives a unique exact real Sylvester matrix solution for every right-hand
    side. -/
theorem existsUnique_isSylvesterSolutionRect_of_sylvesterVecCoeff_det_ne_zero
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n) (C : RMatFn m n)
    (hdet : Matrix.det (sylvesterVecCoeff m n A B) ≠ 0) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  obtain ⟨x, hx, huniq⟩ :=
    existsUnique_finiteMatrix_mulVec_of_det_ne_zero
      (sylvesterVecCoeff m n A B) hdet (Matrix.vec C)
  obtain ⟨X, hXvec⟩ := Matrix.vec_bijective.surjective x
  refine ⟨X, ?_, ?_⟩
  · exact
      (sylvester_vec_system_iff_solution m n A B C X).mp
        (by rw [hXvec]; exact hx)
  · intro Y hY
    apply Matrix.vec_inj.mp
    have hYvec :
        Matrix.mulVec (sylvesterVecCoeff m n A B) (Matrix.vec Y) =
          Matrix.vec C :=
      (sylvester_vec_system_iff_solution m n A B C Y).mpr hY
    rw [huniq (Matrix.vec Y) hYvec, hXvec]

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.1)-(16.3):
    source-numbered alias for the determinant-to-matrix Sylvester unique-solve
    bridge. -/
theorem H16_eq16_3_existsUnique_isSylvesterSolutionRect_of_sylvesterVecCoeff_det_ne_zero
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n) (C : RMatFn m n)
    (hdet : Matrix.det (sylvesterVecCoeff m n A B) ≠ 0) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) :=
  existsUnique_isSylvesterSolutionRect_of_sylvesterVecCoeff_det_ne_zero
    m n A B C hdet

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3): no common
    supplied complex right eigenpair for the complexified real factors makes
    the real Sylvester vec coefficient action injective. -/
theorem sylvesterVecCoeff_mulVec_injective_of_no_common_complex_eigenpair
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : ∀ μ : Complex,
      ¬ ((∃ y : Fin m → Complex,
            y ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex A) y = fun i => μ * y i) ∧
          (∃ z : Fin n → Complex,
            z ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex B) z = fun j => μ * z j))) :
    Function.Injective (Matrix.mulVec (sylvesterVecCoeff m n A B)) := by
  exact
    finiteMatrix_mulVec_injective_of_det_ne_zero
      (sylvesterVecCoeff m n A B)
      (sylvesterVecCoeff_det_ne_zero_of_no_common_complex_eigenpair m n A B hno)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3): no common
    supplied complex right eigenpair for the complexified real factors gives
    the exact zero-kernel characterization for the real Sylvester vec
    coefficient. -/
theorem sylvesterVecCoeff_mulVec_eq_zero_iff_of_no_common_complex_eigenpair
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : ∀ μ : Complex,
      ¬ ((∃ y : Fin m → Complex,
            y ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex A) y = fun i => μ * y i) ∧
          (∃ z : Fin n → Complex,
            z ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex B) z = fun j => μ * z j)))
    (x : Prod (Fin n) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff m n A B) x = 0 ↔ x = 0 := by
  exact
    finiteMatrix_mulVec_eq_zero_iff_of_det_ne_zero
      (sylvesterVecCoeff m n A B)
      (sylvesterVecCoeff_det_ne_zero_of_no_common_complex_eigenpair m n A B hno)
      x

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3): no common
    supplied complex right eigenpair for the complexified real factors makes
    the real Sylvester vec coefficient action surjective. -/
theorem sylvesterVecCoeff_mulVec_surjective_of_no_common_complex_eigenpair
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : ∀ μ : Complex,
      ¬ ((∃ y : Fin m → Complex,
            y ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex A) y = fun i => μ * y i) ∧
          (∃ z : Fin n → Complex,
            z ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex B) z = fun j => μ * z j))) :
    Function.Surjective (Matrix.mulVec (sylvesterVecCoeff m n A B)) := by
  exact
    finiteMatrix_mulVec_surjective_of_det_ne_zero
      (sylvesterVecCoeff m n A B)
      (sylvesterVecCoeff_det_ne_zero_of_no_common_complex_eigenpair m n A B hno)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3): no common
    supplied complex right eigenpair for the complexified real factors makes
    the real Sylvester vec coefficient solve bijective. -/
theorem sylvesterVecCoeff_mulVec_bijective_of_no_common_complex_eigenpair
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : ∀ μ : Complex,
      ¬ ((∃ y : Fin m → Complex,
            y ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex A) y = fun i => μ * y i) ∧
          (∃ z : Fin n → Complex,
            z ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex B) z = fun j => μ * z j))) :
    Function.Bijective (Matrix.mulVec (sylvesterVecCoeff m n A B)) := by
  exact
    finiteMatrix_mulVec_bijective_of_det_ne_zero
      (sylvesterVecCoeff m n A B)
      (sylvesterVecCoeff_det_ne_zero_of_no_common_complex_eigenpair m n A B hno)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3): no common
    supplied complex right eigenpair for the complexified real factors gives a
    unique vectorized real Sylvester coefficient solution for every right-hand
    side. -/
theorem existsUnique_sylvesterVecCoeff_mulVec_of_no_common_complex_eigenpair
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : ∀ μ : Complex,
      ¬ ((∃ y : Fin m → Complex,
            y ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex A) y = fun i => μ * y i) ∧
          (∃ z : Fin n → Complex,
            z ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex B) z = fun j => μ * z j)))
    (c : Prod (Fin n) (Fin m) -> Real) :
    ∃! x : Prod (Fin n) (Fin m) -> Real,
      Matrix.mulVec (sylvesterVecCoeff m n A B) x = c := by
  exact
    existsUnique_finiteMatrix_mulVec_of_det_ne_zero
      (sylvesterVecCoeff m n A B)
      (sylvesterVecCoeff_det_ne_zero_of_no_common_complex_eigenpair m n A B hno)
      c

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3): no common
    supplied complex right eigenpair for the complexified real factors gives a
    unique vectorized real Sylvester coefficient solution whose witness is
    Mathlib's nonsingular-inverse vector formula. -/
theorem existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_no_common_complex_eigenpair
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : ∀ μ : Complex,
      ¬ ((∃ y : Fin m → Complex,
            y ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex A) y = fun i => μ * y i) ∧
          (∃ z : Fin n → Complex,
            z ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex B) z = fun j => μ * z j)))
    (c : Prod (Fin n) (Fin m) -> Real) :
    ExistsUnique fun x : Prod (Fin n) (Fin m) -> Real =>
      Matrix.mulVec (sylvesterVecCoeff m n A B) x = c ∧
        x = Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B)) c := by
  exact
    existsUnique_finiteMatrix_nonsingInv_mulVec_solution_of_det_ne_zero
      (sylvesterVecCoeff m n A B)
      (sylvesterVecCoeff_det_ne_zero_of_no_common_complex_eigenpair m n A B hno)
      c

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.3):
    source-numbered alias for injectivity from supplied no-common complex
    right eigenpairs. -/
alias H16_eq16_3_sylvesterVecCoeff_mulVec_injective_of_no_common_complex_eigenpair :=
  sylvesterVecCoeff_mulVec_injective_of_no_common_complex_eigenpair

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.3):
    source-numbered alias for the zero-kernel characterization from supplied
    no-common complex right eigenpairs. -/
alias H16_eq16_3_sylvesterVecCoeff_mulVec_eq_zero_iff_of_no_common_complex_eigenpair :=
  sylvesterVecCoeff_mulVec_eq_zero_iff_of_no_common_complex_eigenpair

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.3):
    source-numbered alias for surjectivity from supplied no-common complex
    right eigenpairs. -/
alias H16_eq16_3_sylvesterVecCoeff_mulVec_surjective_of_no_common_complex_eigenpair :=
  sylvesterVecCoeff_mulVec_surjective_of_no_common_complex_eigenpair

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.3):
    source-numbered alias for bijectivity from supplied no-common complex
    right eigenpairs. -/
alias H16_eq16_3_sylvesterVecCoeff_mulVec_bijective_of_no_common_complex_eigenpair :=
  sylvesterVecCoeff_mulVec_bijective_of_no_common_complex_eigenpair

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.3):
    source-numbered alias for the unique vectorized coefficient solve from
    supplied no-common complex right eigenpairs. -/
alias H16_eq16_3_existsUnique_sylvesterVecCoeff_mulVec_of_no_common_complex_eigenpair :=
  existsUnique_sylvesterVecCoeff_mulVec_of_no_common_complex_eigenpair

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.3):
    source-numbered alias for the nonsingular-inverse vectorized solve witness
    from supplied no-common complex right eigenpairs. -/
alias H16_eq16_3_existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_no_common_complex_eigenpair :=
  existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_no_common_complex_eigenpair

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3), named
    spectral-separation form: no common complex right eigenvalue for the
    complexified real factors makes the real Sylvester vec coefficient action
    injective. -/
theorem sylvesterVecCoeff_mulVec_injective_of_no_common_complex_right_eigenvalue
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B)) :
    Function.Injective (Matrix.mulVec (sylvesterVecCoeff m n A B)) := by
  exact
    sylvesterVecCoeff_mulVec_injective_of_no_common_complex_eigenpair
      m n A B hno

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3), named
    spectral-separation form: no common complex right eigenvalue for the
    complexified real factors gives the exact zero-kernel characterization for
    the real Sylvester vec coefficient. -/
theorem sylvesterVecCoeff_mulVec_eq_zero_iff_of_no_common_complex_right_eigenvalue
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (x : Prod (Fin n) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff m n A B) x = 0 <-> x = 0 := by
  exact
    sylvesterVecCoeff_mulVec_eq_zero_iff_of_no_common_complex_eigenpair
      m n A B hno x

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3), named
    spectral-separation form: no common complex right eigenvalue for the
    complexified real factors makes the real Sylvester vec coefficient action
    surjective. -/
theorem sylvesterVecCoeff_mulVec_surjective_of_no_common_complex_right_eigenvalue
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B)) :
    Function.Surjective (Matrix.mulVec (sylvesterVecCoeff m n A B)) := by
  exact
    sylvesterVecCoeff_mulVec_surjective_of_no_common_complex_eigenpair
      m n A B hno

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3), named
    spectral-separation form: no common complex right eigenvalue for the
    complexified real factors makes the real Sylvester vec coefficient solve
    bijective. -/
theorem sylvesterVecCoeff_mulVec_bijective_of_no_common_complex_right_eigenvalue
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B)) :
    Function.Bijective (Matrix.mulVec (sylvesterVecCoeff m n A B)) := by
  exact
    sylvesterVecCoeff_mulVec_bijective_of_no_common_complex_eigenpair
      m n A B hno

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3), named
    spectral-separation form: no common complex right eigenvalue for the
    complexified real factors gives a unique vectorized real Sylvester
    coefficient solution for every right-hand side. -/
theorem existsUnique_sylvesterVecCoeff_mulVec_of_no_common_complex_right_eigenvalue
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (c : Prod (Fin n) (Fin m) -> Real) :
    ExistsUnique fun x : Prod (Fin n) (Fin m) -> Real =>
      Matrix.mulVec (sylvesterVecCoeff m n A B) x = c := by
  exact
    existsUnique_sylvesterVecCoeff_mulVec_of_no_common_complex_eigenpair
      m n A B hno c

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3), named
    spectral-separation form: no common complex right eigenvalue for the
    complexified real factors gives a unique vectorized solution whose witness
    is Mathlib's nonsingular-inverse vector formula. -/
theorem existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_no_common_complex_right_eigenvalue
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (c : Prod (Fin n) (Fin m) -> Real) :
    ExistsUnique fun x : Prod (Fin n) (Fin m) -> Real =>
      Matrix.mulVec (sylvesterVecCoeff m n A B) x = c ∧
        x = Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B)) c := by
  exact
    existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_no_common_complex_eigenpair
      m n A B hno c

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.3)-(16.6):
    source-numbered alias for the named no-common-complex-right-eigenvalue
    real vec/Kronecker unique-solve route. -/
theorem H16_eq16_3_existsUnique_sylvesterVecCoeff_mulVec_of_no_common_complex_right_eigenvalue
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (c : Prod (Fin n) (Fin m) -> Real) :
    ExistsUnique fun x : Prod (Fin n) (Fin m) -> Real =>
      Matrix.mulVec (sylvesterVecCoeff m n A B) x = c :=
  existsUnique_sylvesterVecCoeff_mulVec_of_no_common_complex_right_eigenvalue
    m n A B hno c

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.3)-(16.6):
    source-numbered alias for the named no-common-complex-right-eigenvalue
    real vec/Kronecker unique-solve route with the explicit nonsingular-inverse
    vector formula. -/
theorem H16_eq16_3_existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_no_common_complex_right_eigenvalue
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (c : Prod (Fin n) (Fin m) -> Real) :
    ExistsUnique fun x : Prod (Fin n) (Fin m) -> Real =>
      Matrix.mulVec (sylvesterVecCoeff m n A B) x = c ∧
        x = Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B)) c :=
  existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_no_common_complex_right_eigenvalue
    m n A B hno c

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.1)-(16.6): no common
    supplied complex right eigenpair for the complexified real factors gives a
    unique exact real Sylvester matrix solution for every right-hand side. -/
theorem existsUnique_isSylvesterSolutionRect_of_no_common_complex_eigenpair
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n) (C : RMatFn m n)
    (hno : ∀ μ : Complex,
      ¬ ((∃ y : Fin m → Complex,
            y ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex A) y = fun i => μ * y i) ∧
          (∃ z : Fin n → Complex,
            z ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex B) z = fun j => μ * z j))) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  obtain ⟨x, hx, huniq⟩ :=
    existsUnique_sylvesterVecCoeff_mulVec_of_no_common_complex_eigenpair
      m n A B hno (Matrix.vec C)
  obtain ⟨X, hXvec⟩ := Matrix.vec_bijective.surjective x
  refine ⟨X, ?_, ?_⟩
  · exact
      (sylvester_vec_system_iff_solution m n A B C X).mp
        (by rw [hXvec]; exact hx)
  · intro Y hY
    apply Matrix.vec_inj.mp
    have hYvec :
        Matrix.mulVec (sylvesterVecCoeff m n A B) (Matrix.vec Y) =
          Matrix.vec C :=
      (sylvester_vec_system_iff_solution m n A B C Y).mpr hY
    rw [huniq (Matrix.vec Y) hYvec, hXvec]

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.1)-(16.6):
    source-numbered alias for the exact matrix-equation unique-solve route
    from supplied no-common complex right eigenpairs. -/
alias H16_eq16_3_existsUnique_isSylvesterSolutionRect_of_no_common_complex_eigenpair :=
  existsUnique_isSylvesterSolutionRect_of_no_common_complex_eigenpair

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.1)-(16.6), named
    spectral-separation form: no common complex right eigenvalue for the
    complexified real factors gives a unique exact real Sylvester matrix
    solution for every right-hand side. -/
theorem existsUnique_isSylvesterSolutionRect_of_no_common_complex_right_eigenvalue
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n) (C : RMatFn m n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B)) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  exact existsUnique_isSylvesterSolutionRect_of_no_common_complex_eigenpair
    m n A B C hno

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.3)-(16.6):
    source-numbered alias for the named no-common-complex-right-eigenvalue
    exact real Sylvester matrix unique-solve route. -/
theorem H16_eq16_3_existsUnique_isSylvesterSolutionRect_of_no_common_complex_right_eigenvalue
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n) (C : RMatFn m n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B)) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) :=
  existsUnique_isSylvesterSolutionRect_of_no_common_complex_right_eigenvalue
    m n A B C hno

/-- A concrete left inverse and operator-2 radius for the printed Sylvester
    vec/Kronecker coefficient gives its sigma-min lower-bound route directly,
    without assuming the target coefficient lower-bound theorem. -/
theorem sylvesterVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      (1 / M) * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x) := by
  exact
    finiteMatrix_sigmaMin_of_left_inverse_finiteOpNorm2Le
      (sylvesterVecCoeff n n A B) Pinv hM hLeft hPinv

/-- A concrete left inverse and operator-2 radius for the printed Sylvester
    vec/Kronecker coefficient gives the corresponding finite Gram eigenvalue
    lower bound. -/
theorem sylvesterVecCoeff_gram_eigenvalues_ge_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    forall p : Prod (Fin n) (Fin n),
      (1 / M) ^ 2 <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p := by
  exact
    finiteMatrixGram_eigenvalues_ge_of_left_inverse_finiteOpNorm2Le
      (sylvesterVecCoeff n n A B) Pinv hM hLeft hPinv

/-- A concrete left inverse and operator-2 radius for the printed Lyapunov
    vec/Kronecker coefficient gives its sigma-min lower-bound route directly,
    without assuming the target coefficient lower-bound theorem. -/
theorem lyapunovVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      (1 / M) * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x) := by
  exact
    finiteMatrix_sigmaMin_of_left_inverse_finiteOpNorm2Le
      (lyapunovVecCoeff n A) Pinv hM hLeft hPinv

/-- A concrete left inverse and operator-2 radius for the printed Lyapunov
    vec/Kronecker coefficient gives the corresponding finite Gram eigenvalue
    lower bound. -/
theorem lyapunovVecCoeff_gram_eigenvalues_ge_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    forall p : Prod (Fin n) (Fin n),
      (1 / M) ^ 2 <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p := by
  exact
    finiteMatrixGram_eigenvalues_ge_of_left_inverse_finiteOpNorm2Le
      (lyapunovVecCoeff n A) Pinv hM hLeft hPinv

/-- Higham, 2nd ed., Chapter 16.1 and (16.23)-(16.26):
    a Gram-eigenvalue lower bound for the concrete vectorized Sylvester
    coefficient gives the coefficient lower bound used by the Chapter 16
    sigma-min wrappers. -/
theorem sylvesterVecCoeff_sigmaMin_of_gram_eigenvalues (n : Nat)
    (A B : Fin n -> Fin n -> Real) {lam : Real} (hlam : 0 <= lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      Real.sqrt lam * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x) := by
  intro x
  exact
    finiteMatrixGram_sigmaMin_mul_finiteVecNorm2_le_mulVec
      (sylvesterVecCoeff n n A B) hlam hEig x

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    a Gram-eigenvalue lower bound for the concrete vectorized Lyapunov
    coefficient gives the coefficient lower bound used by the Chapter 16
    Lyapunov sigma-min wrappers. -/
theorem lyapunovVecCoeff_sigmaMin_of_gram_eigenvalues (n : Nat)
    (A : Fin n -> Fin n -> Real) {lam : Real} (hlam : 0 <= lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      Real.sqrt lam * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x) := by
  intro x
  exact
    finiteMatrixGram_sigmaMin_mul_finiteVecNorm2_le_mulVec
      (lyapunovVecCoeff n A) hlam hEig x

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5):
    a positive sigma-min lower-bound certificate for the vec/Kronecker
    Sylvester coefficient implies determinant nonsingularity. -/
theorem sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin (n : Nat)
    (A B : Fin n -> Fin n -> Real) {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x)) :
    (sylvesterVecCoeff n n A B).det ≠ 0 := by
  exact
    finiteMatrix_det_ne_zero_of_sigmaMin_lower_bound
      (sylvesterVecCoeff n n A B) hsigma hCoeff

/-- Higham, 2nd ed., Chapter 16.1 and (16.23)-(16.26):
    a positive finite-Gram eigenvalue lower bound for the concrete vectorized
    Sylvester coefficient implies determinant nonsingularity. -/
theorem sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues (n : Nat)
    (A B : Fin n -> Fin n -> Real) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p) :
    (sylvesterVecCoeff n n A B).det ≠ 0 := by
  exact
    finiteMatrix_det_ne_zero_of_gram_eigenvalues
      (sylvesterVecCoeff n n A B) hlam hEig

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5):
    a concrete left inverse with finite operator-2 radius for the vec/Kronecker
    Sylvester coefficient implies determinant nonsingularity. -/
theorem sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    (sylvesterVecCoeff n n A B).det ≠ 0 := by
  exact
    finiteMatrix_det_ne_zero_of_left_inverse_finiteOpNorm2Le
      (sylvesterVecCoeff n n A B) Pinv hM hLeft hPinv

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a positive sigma-min lower-bound certificate for the vec/Kronecker
    Lyapunov coefficient implies determinant nonsingularity. -/
theorem lyapunovVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x)) :
    (lyapunovVecCoeff n A).det ≠ 0 := by
  exact
    finiteMatrix_det_ne_zero_of_sigmaMin_lower_bound
      (lyapunovVecCoeff n A) hsigma hCoeff

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a positive finite-Gram eigenvalue lower bound for the concrete vectorized
    Lyapunov coefficient implies determinant nonsingularity. -/
theorem lyapunovVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues (n : Nat)
    (A : Fin n -> Fin n -> Real) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p) :
    (lyapunovVecCoeff n A).det ≠ 0 := by
  exact
    finiteMatrix_det_ne_zero_of_gram_eigenvalues
      (lyapunovVecCoeff n A) hlam hEig

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a concrete left inverse with finite operator-2 radius for the vec/Kronecker
    Lyapunov coefficient implies determinant nonsingularity. -/
theorem lyapunovVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    (lyapunovVecCoeff n A).det ≠ 0 := by
  exact
    finiteMatrix_det_ne_zero_of_left_inverse_finiteOpNorm2Le
      (lyapunovVecCoeff n A) Pinv hM hLeft hPinv

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.6):
    source-numbered alias for the Sylvester concrete sigma-min determinant
    certificate. -/
alias H16_eq16_2_26_sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin :=
  sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.6):
    source-numbered alias for the Sylvester finite-Gram determinant
    certificate. -/
alias H16_eq16_2_26_sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues :=
  sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.6):
    source-numbered alias for the Sylvester concrete-left-inverse determinant
    certificate. -/
alias H16_eq16_2_26_sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le :=
  sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.27):
    source-numbered alias for the Lyapunov concrete sigma-min determinant
    certificate. -/
alias H16_eq16_2_27_lyapunovVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin :=
  lyapunovVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.27):
    source-numbered alias for the Lyapunov finite-Gram determinant
    certificate. -/
alias H16_eq16_2_27_lyapunovVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues :=
  lyapunovVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.27):
    source-numbered alias for the Lyapunov concrete-left-inverse determinant
    certificate. -/
alias H16_eq16_2_27_lyapunovVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le :=
  lyapunovVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5):
    determinant nonsingularity gives the exact trivial-kernel statement for the
    vectorized Sylvester coefficient. -/
theorem sylvesterVecCoeff_mulVec_eq_zero_iff_of_det_ne_zero
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (hdet : (sylvesterVecCoeff n n A B).det ≠ 0)
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B) x = 0 ↔ x = 0 := by
  exact
    finiteMatrix_mulVec_eq_zero_iff_of_det_ne_zero
      (sylvesterVecCoeff n n A B) hdet x

/-- Higham, 2nd ed., Chapter 16.1 and (16.23)-(16.26):
    a positive sigma-min certificate gives the exact trivial-kernel statement
    for the vectorized Sylvester coefficient. -/
theorem sylvesterVecCoeff_mulVec_eq_zero_iff_of_vecCoeff_sigmaMin (n : Nat)
    (A B : Fin n -> Fin n -> Real) {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B) x = 0 ↔ x = 0 := by
  exact
    sylvesterVecCoeff_mulVec_eq_zero_iff_of_det_ne_zero n A B
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin n A B hsigma hCoeff)
      x

/-- Higham, 2nd ed., Chapter 16.1 and (16.23)-(16.26):
    a positive finite-Gram eigenvalue certificate gives the exact
    trivial-kernel statement for the vectorized Sylvester coefficient. -/
theorem sylvesterVecCoeff_mulVec_eq_zero_iff_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A B : Fin n -> Fin n -> Real) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B) x = 0 ↔ x = 0 := by
  exact
    sylvesterVecCoeff_mulVec_eq_zero_iff_of_det_ne_zero n A B
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      x

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5):
    a concrete left inverse with finite operator-2 radius gives the exact
    trivial-kernel statement for the vectorized Sylvester coefficient. -/
theorem sylvesterVecCoeff_mulVec_eq_zero_iff_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B) x = 0 ↔ x = 0 := by
  exact
    sylvesterVecCoeff_mulVec_eq_zero_iff_of_det_ne_zero n A B
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      x

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    determinant nonsingularity gives the exact trivial-kernel statement for the
    vectorized Lyapunov coefficient. -/
theorem lyapunovVecCoeff_mulVec_eq_zero_iff_of_det_ne_zero
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (hdet : (lyapunovVecCoeff n A).det ≠ 0)
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A) x = 0 ↔ x = 0 := by
  exact
    finiteMatrix_mulVec_eq_zero_iff_of_det_ne_zero
      (lyapunovVecCoeff n A) hdet x

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a positive sigma-min certificate gives the exact trivial-kernel statement
    for the vectorized Lyapunov coefficient. -/
theorem lyapunovVecCoeff_mulVec_eq_zero_iff_of_vecCoeff_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A) x = 0 ↔ x = 0 := by
  exact
    lyapunovVecCoeff_mulVec_eq_zero_iff_of_det_ne_zero n A
      (lyapunovVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin n A hsigma hCoeff)
      x

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a positive finite-Gram eigenvalue certificate gives the exact
    trivial-kernel statement for the vectorized Lyapunov coefficient. -/
theorem lyapunovVecCoeff_mulVec_eq_zero_iff_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A : Fin n -> Fin n -> Real) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A) x = 0 ↔ x = 0 := by
  exact
    lyapunovVecCoeff_mulVec_eq_zero_iff_of_det_ne_zero n A
      (lyapunovVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A hlam hEig)
      x

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a concrete left inverse with finite operator-2 radius gives the exact
    trivial-kernel statement for the vectorized Lyapunov coefficient. -/
theorem lyapunovVecCoeff_mulVec_eq_zero_iff_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A) x = 0 ↔ x = 0 := by
  exact
    lyapunovVecCoeff_mulVec_eq_zero_iff_of_det_ne_zero n A
      (lyapunovVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)
      x

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5):
    a concrete left inverse with finite operator-2 radius makes the exact
    vectorized Sylvester coefficient solve bijective.  This is a determinant
    consequence of the supplied certificate, not an automatic inverse
    construction. -/
theorem sylvesterVecCoeff_mulVec_bijective_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    Function.Bijective (Matrix.mulVec (sylvesterVecCoeff n n A B)) := by
  exact
    finiteMatrix_mulVec_bijective_of_det_ne_zero
      (sylvesterVecCoeff n n A B)
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5):
    a concrete left inverse with finite operator-2 radius gives a unique exact
    vectorized Sylvester coefficient solution for every right-hand side. -/
theorem existsUnique_sylvesterVecCoeff_mulVec_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (sylvesterVecCoeff n n A B) x = c := by
  exact
    existsUnique_finiteMatrix_mulVec_of_det_ne_zero
      (sylvesterVecCoeff n n A B)
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      c

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a concrete left inverse with finite operator-2 radius makes the exact
    vectorized Lyapunov coefficient solve bijective.  This is a determinant
    consequence of the supplied certificate, not an automatic inverse
    construction. -/
theorem lyapunovVecCoeff_mulVec_bijective_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    Function.Bijective (Matrix.mulVec (lyapunovVecCoeff n A)) := by
  exact
    finiteMatrix_mulVec_bijective_of_det_ne_zero
      (lyapunovVecCoeff n A)
      (lyapunovVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a concrete left inverse with finite operator-2 radius gives a unique exact
    vectorized Lyapunov coefficient solution for every right-hand side. -/
theorem existsUnique_lyapunovVecCoeff_mulVec_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (lyapunovVecCoeff n A) x = c := by
  exact
    existsUnique_finiteMatrix_mulVec_of_det_ne_zero
      (lyapunovVecCoeff n A)
      (lyapunovVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)
      c

/-- Higham, 2nd ed., Chapter 16.1 and (16.23)-(16.26):
    a positive sigma-min certificate makes the exact vectorized Sylvester
    coefficient solve bijective.  This is a coefficient-matrix consequence of
    the supplied certificate, not a nondiagonal Kronecker spectral theorem. -/
theorem sylvesterVecCoeff_mulVec_bijective_of_vecCoeff_sigmaMin (n : Nat)
    (A B : Fin n -> Fin n -> Real) {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x)) :
    Function.Bijective (Matrix.mulVec (sylvesterVecCoeff n n A B)) := by
  exact
    finiteMatrix_mulVec_bijective_of_det_ne_zero
      (sylvesterVecCoeff n n A B)
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin n A B hsigma hCoeff)

/-- Higham, 2nd ed., Chapter 16.1 and (16.23)-(16.26):
    a positive sigma-min certificate gives a unique exact vectorized Sylvester
    coefficient solution for every vectorized right-hand side. -/
theorem existsUnique_sylvesterVecCoeff_mulVec_of_vecCoeff_sigmaMin (n : Nat)
    (A B : Fin n -> Fin n -> Real) {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (sylvesterVecCoeff n n A B) x = c := by
  exact
    existsUnique_finiteMatrix_mulVec_of_det_ne_zero
      (sylvesterVecCoeff n n A B)
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin n A B hsigma hCoeff)
      c

/-- Higham, 2nd ed., Chapter 16.1 and (16.23)-(16.26):
    a positive finite-Gram eigenvalue certificate makes the exact vectorized
    Sylvester coefficient solve bijective. -/
theorem sylvesterVecCoeff_mulVec_bijective_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A B : Fin n -> Fin n -> Real) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p) :
    Function.Bijective (Matrix.mulVec (sylvesterVecCoeff n n A B)) := by
  exact
    finiteMatrix_mulVec_bijective_of_det_ne_zero
      (sylvesterVecCoeff n n A B)
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)

/-- Higham, 2nd ed., Chapter 16.1 and (16.23)-(16.26):
    a positive finite-Gram eigenvalue certificate gives a unique exact
    vectorized Sylvester coefficient solution for every right-hand side. -/
theorem existsUnique_sylvesterVecCoeff_mulVec_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A B : Fin n -> Fin n -> Real) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (sylvesterVecCoeff n n A B) x = c := by
  exact
    existsUnique_finiteMatrix_mulVec_of_det_ne_zero
      (sylvesterVecCoeff n n A B)
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      c

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a positive sigma-min certificate makes the exact vectorized Lyapunov
    coefficient solve bijective. -/
theorem lyapunovVecCoeff_mulVec_bijective_of_vecCoeff_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x)) :
    Function.Bijective (Matrix.mulVec (lyapunovVecCoeff n A)) := by
  exact
    finiteMatrix_mulVec_bijective_of_det_ne_zero
      (lyapunovVecCoeff n A)
      (lyapunovVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin n A hsigma hCoeff)

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a positive sigma-min certificate gives a unique exact vectorized Lyapunov
    coefficient solution for every right-hand side. -/
theorem existsUnique_lyapunovVecCoeff_mulVec_of_vecCoeff_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (lyapunovVecCoeff n A) x = c := by
  exact
    existsUnique_finiteMatrix_mulVec_of_det_ne_zero
      (lyapunovVecCoeff n A)
      (lyapunovVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin n A hsigma hCoeff)
      c

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a positive finite-Gram eigenvalue certificate makes the exact vectorized
    Lyapunov coefficient solve bijective. -/
theorem lyapunovVecCoeff_mulVec_bijective_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A : Fin n -> Fin n -> Real) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p) :
    Function.Bijective (Matrix.mulVec (lyapunovVecCoeff n A)) := by
  exact
    finiteMatrix_mulVec_bijective_of_det_ne_zero
      (lyapunovVecCoeff n A)
      (lyapunovVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A hlam hEig)

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a positive finite-Gram eigenvalue certificate gives a unique exact
    vectorized Lyapunov coefficient solution for every right-hand side. -/
theorem existsUnique_lyapunovVecCoeff_mulVec_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A : Fin n -> Fin n -> Real) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (lyapunovVecCoeff n A) x = c := by
  exact
    existsUnique_finiteMatrix_mulVec_of_det_ne_zero
      (lyapunovVecCoeff n A)
      (lyapunovVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A hlam hEig)
      c

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied `SepLowerBound` certificate for `sep(A,-A^T)` gives the
    Frobenius sigma-min lower bound for the Lyapunov operator. -/
theorem lyapunovOp_sigmaMin_of_sepLowerBound (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma) :
    forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y) := by
  have hInv := lyapunovInverseOpBound_of_sepLowerBound n A sigma hSep.1 hSep
  intro Y
  have h := hInv Y
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hSep.1)
  calc
    sigma * frobNorm Y <=
        sigma * ((1 / sigma) * frobNorm (lyapunovOp n A Y)) := hmul
    _ = frobNorm (lyapunovOp n A Y) := by
      field_simp [ne_of_gt hSep.1]

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied `SepLowerBound` certificate for `sep(A,-A^T)` transfers through
    the vec/Frobenius isometry to the concrete vectorized Lyapunov coefficient
    sigma-min route. -/
theorem lyapunovVecCoeff_sigmaMin_of_sepLowerBound (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x) := by
  intro x
  let Y : Matrix (Fin n) (Fin n) Real := fun i j => x (j, i)
  have hvecY : Matrix.vec Y = x := by
    ext p
    rfl
  have hOp := lyapunovOp_sigmaMin_of_sepLowerBound n A sigma hSep Y
  let Amat : Matrix (Fin n) (Fin n) Real := A
  let Ymat : Matrix (Fin n) (Fin n) Real := Y
  have hLY :
      Amat * Ymat + Ymat * Matrix.transpose Amat = lyapunovOp n A Y := by
    ext i j
    simp [Amat, Ymat, Y, lyapunovOp, matMul, matTranspose, Matrix.mul_apply]
  rw [<- hvecY]
  rw [lyapunovVecCoeff_mulVec_vec n A Y,
    finiteVecNorm2_vec_eq_frobNorm n n Y, hLY,
    finiteVecNorm2_vec_eq_frobNorm n n (lyapunovOp n A Y)]
  exact hOp

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive lower bound on the exact infimum model `sep(A,-A^T)` transfers
    to the concrete vectorized Lyapunov coefficient sigma-min route. -/
theorem lyapunovVecCoeff_sigmaMin_of_pos_le_sylvesterSepInf (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A
      (fun i j => -matTranspose A i j)) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x) := by
  exact
    lyapunovVecCoeff_sigmaMin_of_sepLowerBound n A sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied `SepLowerBound` certificate for `sep(A,-A^T)` makes the
    concrete vectorized Lyapunov coefficient nonsingular through the sigma-min
    determinant route. -/
theorem lyapunovVecCoeff_det_ne_zero_of_sepLowerBound (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma) :
    (lyapunovVecCoeff n A).det ≠ 0 := by
  exact
    lyapunovVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin n A hSep.1
      (lyapunovVecCoeff_sigmaMin_of_sepLowerBound n A sigma hSep)

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive lower bound on the exact infimum model `sep(A,-A^T)` makes the
    concrete vectorized Lyapunov coefficient nonsingular. -/
theorem lyapunovVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A
      (fun i j => -matTranspose A i j)) :
    (lyapunovVecCoeff n A).det ≠ 0 := by
  exact
    lyapunovVecCoeff_det_ne_zero_of_sepLowerBound n A sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied `SepLowerBound` certificate for `sep(A,-A^T)` gives the exact
    trivial-kernel statement for the vectorized Lyapunov coefficient. -/
theorem lyapunovVecCoeff_mulVec_eq_zero_iff_of_sepLowerBound (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A) x = 0 ↔ x = 0 := by
  exact
    lyapunovVecCoeff_mulVec_eq_zero_iff_of_det_ne_zero n A
      (lyapunovVecCoeff_det_ne_zero_of_sepLowerBound n A sigma hSep) x

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive exact-`sylvesterSepInf` lower bound for `sep(A,-A^T)` gives the
    exact trivial-kernel statement for the vectorized Lyapunov coefficient. -/
theorem lyapunovVecCoeff_mulVec_eq_zero_iff_of_pos_le_sylvesterSepInf
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A
      (fun i j => -matTranspose A i j))
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A) x = 0 ↔ x = 0 := by
  exact
    lyapunovVecCoeff_mulVec_eq_zero_iff_of_det_ne_zero n A
      (lyapunovVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A sigma hsigma hle)
      x

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied `SepLowerBound` certificate for `sep(A,-A^T)` makes the exact
    vectorized Lyapunov coefficient solve bijective. -/
theorem lyapunovVecCoeff_mulVec_bijective_of_sepLowerBound (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma) :
    Function.Bijective (Matrix.mulVec (lyapunovVecCoeff n A)) := by
  exact
    finiteMatrix_mulVec_bijective_of_det_ne_zero
      (lyapunovVecCoeff n A)
      (lyapunovVecCoeff_det_ne_zero_of_sepLowerBound n A sigma hSep)

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied `SepLowerBound` certificate for `sep(A,-A^T)` gives a unique
    exact vectorized Lyapunov coefficient solution for every right-hand side. -/
theorem existsUnique_lyapunovVecCoeff_mulVec_of_sepLowerBound (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (lyapunovVecCoeff n A) x = c := by
  exact
    existsUnique_finiteMatrix_mulVec_of_det_ne_zero
      (lyapunovVecCoeff n A)
      (lyapunovVecCoeff_det_ne_zero_of_sepLowerBound n A sigma hSep)
      c

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive lower bound on the exact infimum model `sep(A,-A^T)` makes the
    exact vectorized Lyapunov coefficient solve bijective. -/
theorem lyapunovVecCoeff_mulVec_bijective_of_pos_le_sylvesterSepInf
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A
      (fun i j => -matTranspose A i j)) :
    Function.Bijective (Matrix.mulVec (lyapunovVecCoeff n A)) := by
  exact
    lyapunovVecCoeff_mulVec_bijective_of_sepLowerBound n A sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive lower bound on the exact infimum model `sep(A,-A^T)` gives a
    unique exact vectorized Lyapunov coefficient solution for every right-hand
    side. -/
theorem existsUnique_lyapunovVecCoeff_mulVec_of_pos_le_sylvesterSepInf
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A
      (fun i j => -matTranspose A i j))
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (lyapunovVecCoeff n A) x = c := by
  exact
    existsUnique_lyapunovVecCoeff_mulVec_of_sepLowerBound n A sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      c

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for `SepLowerBound(A,-A^T)` Lyapunov
    vectorized coefficient bijectivity. -/
alias H16_eq16_2_27_lyapunovVecCoeff_mulVec_bijective_of_sepLowerBound :=
  lyapunovVecCoeff_mulVec_bijective_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the `SepLowerBound(A,-A^T)` unique
    vectorized Lyapunov coefficient solve witness. -/
alias H16_eq16_2_27_existsUnique_lyapunovVecCoeff_mulVec_of_sepLowerBound :=
  existsUnique_lyapunovVecCoeff_mulVec_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for positive exact-`sep(A,-A^T)` Lyapunov
    vectorized coefficient bijectivity. -/
alias H16_eq16_2_27_lyapunovVecCoeff_mulVec_bijective_of_pos_le_sylvesterSepInf :=
  lyapunovVecCoeff_mulVec_bijective_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the positive exact-`sep(A,-A^T)` unique
    vectorized Lyapunov coefficient solve witness. -/
alias H16_eq16_2_27_existsUnique_lyapunovVecCoeff_mulVec_of_pos_le_sylvesterSepInf :=
  existsUnique_lyapunovVecCoeff_mulVec_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    with a supplied `SepLowerBound` certificate for `sep(A,-A^T)`, Mathlib's
    nonsingular inverse gives an explicit exact vectorized Lyapunov coefficient
    solution. -/
theorem lyapunovVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (c : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A)
        (Matrix.mulVec (Inv.inv (lyapunovVecCoeff n A)) c) =
      c := by
  have hdet := lyapunovVecCoeff_det_ne_zero_of_sepLowerBound n A sigma hSep
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv (lyapunovVecCoeff n A)
      (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    the nonsingular-inverse vector supplied by a `SepLowerBound` certificate is
    the unique exact Lyapunov coefficient solution for the right-hand side. -/
theorem existsUnique_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (lyapunovVecCoeff n A) x = c := by
  refine
    ⟨Matrix.mulVec (Inv.inv (lyapunovVecCoeff n A)) c,
      lyapunovVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound
        n A sigma hSep c, ?_⟩
  intro y hy
  have hdet := lyapunovVecCoeff_det_ne_zero_of_sepLowerBound n A sigma hSep
  calc
    y =
        Matrix.mulVec (Inv.inv (lyapunovVecCoeff n A))
          (Matrix.mulVec (lyapunovVecCoeff n A) y) := by
        symm
        rw [Matrix.mulVec_mulVec,
          Matrix.nonsing_inv_mul (lyapunovVecCoeff n A)
            (isUnit_iff_ne_zero.mpr hdet),
          Matrix.one_mulVec]
    _ = Matrix.mulVec (Inv.inv (lyapunovVecCoeff n A)) c := by
        rw [hy]

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    with a positive lower bound on `sep(A,-A^T)`, Mathlib's nonsingular
    inverse gives an explicit exact vectorized Lyapunov coefficient solution. -/
theorem lyapunovVecCoeff_nonsingInv_mulVec_solution_of_pos_le_sylvesterSepInf
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A
      (fun i j => -matTranspose A i j))
    (c : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A)
        (Matrix.mulVec (Inv.inv (lyapunovVecCoeff n A)) c) =
      c := by
  exact
    lyapunovVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound
      n A sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      c

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive lower bound on `sep(A,-A^T)` makes the nonsingular-inverse
    vector the unique exact Lyapunov coefficient solution. -/
theorem existsUnique_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_pos_le_sylvesterSepInf
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A
      (fun i j => -matTranspose A i j))
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (lyapunovVecCoeff n A) x = c := by
  exact
    existsUnique_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound
      n A sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      c

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the `SepLowerBound(A,-A^T)`
    nonsingular-inverse vectorized Lyapunov coefficient solution. -/
alias H16_eq16_2_27_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound :=
  lyapunovVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the `SepLowerBound(A,-A^T)` unique
    nonsingular-inverse vectorized Lyapunov coefficient solve witness. -/
alias H16_eq16_2_27_existsUnique_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound :=
  existsUnique_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the positive exact-`sep(A,-A^T)`
    nonsingular-inverse vectorized Lyapunov coefficient solution. -/
alias H16_eq16_2_27_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_pos_le_sylvesterSepInf :=
  lyapunovVecCoeff_nonsingInv_mulVec_solution_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the positive exact-`sep(A,-A^T)` unique
    nonsingular-inverse vectorized Lyapunov coefficient solve witness. -/
alias H16_eq16_2_27_existsUnique_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_pos_le_sylvesterSepInf :=
  existsUnique_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5):
    determinant nonsingularity exposes the exact nonsingular-inverse action for
    the vectorized Sylvester coefficient solve. -/
theorem sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (hdet : (sylvesterVecCoeff n n A B).det ≠ 0)
    (c : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)
        (Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ c) = c := by
  exact
    finiteMatrix_mulVec_nonsingInv_mulVec_of_det_ne_zero
      (sylvesterVecCoeff n n A B) hdet c

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    determinant nonsingularity exposes the exact nonsingular-inverse action for
    the vectorized Lyapunov coefficient solve. -/
theorem lyapunovVecCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (hdet : (lyapunovVecCoeff n A).det ≠ 0)
    (c : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A)
        (Matrix.mulVec (lyapunovVecCoeff n A)⁻¹ c) = c := by
  exact
    finiteMatrix_mulVec_nonsingInv_mulVec_of_det_ne_zero
      (lyapunovVecCoeff n A) hdet c

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5):
    determinant nonsingularity exposes the left action of the nonsingular
    inverse for the vectorized Sylvester coefficient. -/
theorem sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (hdet : (sylvesterVecCoeff n n A B).det ≠ 0)
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹
        (Matrix.mulVec (sylvesterVecCoeff n n A B) x) = x := by
  exact
    finiteMatrix_nonsingInv_mulVec_mulVec_of_det_ne_zero
      (sylvesterVecCoeff n n A B) hdet x

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    determinant nonsingularity exposes the left action of the nonsingular
    inverse for the vectorized Lyapunov coefficient. -/
theorem lyapunovVecCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (hdet : (lyapunovVecCoeff n A).det ≠ 0)
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A)⁻¹
        (Matrix.mulVec (lyapunovVecCoeff n A) x) = x := by
  exact
    finiteMatrix_nonsingInv_mulVec_mulVec_of_det_ne_zero
      (lyapunovVecCoeff n A) hdet x

/-- Higham, 2nd ed., Chapter 16.1 and (16.23)-(16.26):
    a positive sigma-min certificate gives the exact nonsingular-inverse solve
    action for the vectorized Sylvester coefficient. -/
theorem sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_vecCoeff_sigmaMin
    (n : Nat) (A B : Fin n -> Fin n -> Real) {sigma : Real}
    (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (c : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)
        (Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ c) = c := by
  exact
    sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
      n A B
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      c

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a positive sigma-min certificate gives the exact nonsingular-inverse solve
    action for the vectorized Lyapunov coefficient. -/
theorem lyapunovVecCoeff_mulVec_nonsingInv_mulVec_of_vecCoeff_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) {sigma : Real}
    (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    (c : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A)
        (Matrix.mulVec (lyapunovVecCoeff n A)⁻¹ c) = c := by
  exact
    lyapunovVecCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
      n A
      (lyapunovVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A hsigma hCoeff)
      c

/-- Higham, 2nd ed., Chapter 16.1 and (16.23)-(16.26):
    a positive sigma-min certificate gives the left action of the nonsingular
    inverse for the vectorized Sylvester coefficient. -/
theorem sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_vecCoeff_sigmaMin
    (n : Nat) (A B : Fin n -> Fin n -> Real) {sigma : Real}
    (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹
        (Matrix.mulVec (sylvesterVecCoeff n n A B) x) = x := by
  exact
    sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
      n A B
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      x

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a positive sigma-min certificate gives the left action of the nonsingular
    inverse for the vectorized Lyapunov coefficient. -/
theorem lyapunovVecCoeff_nonsingInv_mulVec_mulVec_of_vecCoeff_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) {sigma : Real}
    (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A)⁻¹
        (Matrix.mulVec (lyapunovVecCoeff n A) x) = x := by
  exact
    lyapunovVecCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
      n A
      (lyapunovVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A hsigma hCoeff)
      x

/-- Higham, 2nd ed., Chapter 16.1 and (16.23)-(16.26):
    a positive finite-Gram eigenvalue certificate gives the exact
    nonsingular-inverse solve action for the vectorized Sylvester coefficient. -/
theorem sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A B : Fin n -> Fin n -> Real) {lam : Real}
    (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (c : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)
        (Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ c) = c := by
  exact
    sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
      n A B
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      c

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a positive finite-Gram eigenvalue certificate gives the exact
    nonsingular-inverse solve action for the vectorized Lyapunov coefficient. -/
theorem lyapunovVecCoeff_mulVec_nonsingInv_mulVec_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A : Fin n -> Fin n -> Real) {lam : Real}
    (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (c : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A)
        (Matrix.mulVec (lyapunovVecCoeff n A)⁻¹ c) = c := by
  exact
    lyapunovVecCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
      n A
      (lyapunovVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A hlam hEig)
      c

/-- Higham, 2nd ed., Chapter 16.1 and (16.23)-(16.26):
    a positive finite-Gram eigenvalue certificate gives the left action of the
    nonsingular inverse for the vectorized Sylvester coefficient. -/
theorem sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A B : Fin n -> Fin n -> Real) {lam : Real}
    (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹
        (Matrix.mulVec (sylvesterVecCoeff n n A B) x) = x := by
  exact
    sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
      n A B
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      x

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a positive finite-Gram eigenvalue certificate gives the left action of the
    nonsingular inverse for the vectorized Lyapunov coefficient. -/
theorem lyapunovVecCoeff_nonsingInv_mulVec_mulVec_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A : Fin n -> Fin n -> Real) {lam : Real}
    (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A)⁻¹
        (Matrix.mulVec (lyapunovVecCoeff n A) x) = x := by
  exact
    lyapunovVecCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
      n A
      (lyapunovVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A hlam hEig)
      x

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5):
    a concrete left inverse with finite operator-2 radius gives the exact
    nonsingular-inverse solve action for the vectorized Sylvester coefficient. -/
theorem sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (c : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)
        (Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ c) = c := by
  exact
    sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
      n A B
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      c

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a concrete left inverse with finite operator-2 radius gives the exact
    nonsingular-inverse solve action for the vectorized Lyapunov coefficient. -/
theorem lyapunovVecCoeff_mulVec_nonsingInv_mulVec_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (c : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A)
        (Matrix.mulVec (lyapunovVecCoeff n A)⁻¹ c) = c := by
  exact
    lyapunovVecCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
      n A
      (lyapunovVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)
      c

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5):
    a concrete left inverse with finite operator-2 radius gives the left action
    of the nonsingular inverse for the vectorized Sylvester coefficient. -/
theorem sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹
        (Matrix.mulVec (sylvesterVecCoeff n n A B) x) = x := by
  exact
    sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
      n A B
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      x

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a concrete left inverse with finite operator-2 radius gives the left action
    of the nonsingular inverse for the vectorized Lyapunov coefficient. -/
theorem lyapunovVecCoeff_nonsingInv_mulVec_mulVec_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A)⁻¹
        (Matrix.mulVec (lyapunovVecCoeff n A) x) = x := by
  exact
    lyapunovVecCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
      n A
      (lyapunovVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)
      x

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5):
    determinant nonsingularity identifies any exact vectorized Sylvester
    coefficient solution with the nonsingular-inverse solution. -/
theorem sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_det_ne_zero
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (hdet : (sylvesterVecCoeff n n A B).det ≠ 0)
    {x c : Prod (Fin n) (Fin n) -> Real}
    (hx : Matrix.mulVec (sylvesterVecCoeff n n A B) x = c) :
    x = Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ c := by
  exact
    finiteMatrix_eq_nonsingInv_mulVec_of_mulVec_eq_of_det_ne_zero
      (sylvesterVecCoeff n n A B) hdet hx

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    determinant nonsingularity identifies any exact vectorized Lyapunov
    coefficient solution with the nonsingular-inverse solution. -/
theorem lyapunovVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_det_ne_zero
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (hdet : (lyapunovVecCoeff n A).det ≠ 0)
    {x c : Prod (Fin n) (Fin n) -> Real}
    (hx : Matrix.mulVec (lyapunovVecCoeff n A) x = c) :
    x = Matrix.mulVec (lyapunovVecCoeff n A)⁻¹ c := by
  exact
    finiteMatrix_eq_nonsingInv_mulVec_of_mulVec_eq_of_det_ne_zero
      (lyapunovVecCoeff n A) hdet hx

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied `SepLowerBound` certificate for `sep(A,-A^T)` instantiates the
    determinant-based left nonsingular-inverse action for the Lyapunov
    coefficient. -/
theorem lyapunovVecCoeff_nonsingInv_mulVec_mulVec_of_sepLowerBound
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (z : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A)⁻¹
        (Matrix.mulVec (lyapunovVecCoeff n A) z) =
      z := by
  exact
    lyapunovVecCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
      n A (lyapunovVecCoeff_det_ne_zero_of_sepLowerBound n A sigma hSep) z

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied `SepLowerBound` certificate for `sep(A,-A^T)` instantiates the
    determinant-based right nonsingular-inverse action for the Lyapunov
    coefficient. -/
theorem lyapunovVecCoeff_mulVec_nonsingInv_mulVec_of_sepLowerBound
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (rhs : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A)
        (Matrix.mulVec (lyapunovVecCoeff n A)⁻¹ rhs) =
      rhs := by
  exact
    lyapunovVecCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
      n A (lyapunovVecCoeff_det_ne_zero_of_sepLowerBound n A sigma hSep) rhs

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied `SepLowerBound` certificate for `sep(A,-A^T)` identifies any
    exact Lyapunov coefficient solution with the nonsingular-inverse vector. -/
theorem lyapunovVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_sepLowerBound
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    {z rhs : Prod (Fin n) (Fin n) -> Real}
    (hz : Matrix.mulVec (lyapunovVecCoeff n A) z = rhs) :
    z =
      Matrix.mulVec (lyapunovVecCoeff n A)⁻¹ rhs := by
  exact
    lyapunovVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_det_ne_zero
      n A (lyapunovVecCoeff_det_ne_zero_of_sepLowerBound n A sigma hSep) hz

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a Lyapunov operator sigma-min certificate transfers to the vectorized
    Lyapunov coefficient sigma-min route. -/
theorem lyapunovVecCoeff_sigmaMin_of_operator_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y)) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x) := by
  have hSep := SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin
  exact lyapunovVecCoeff_sigmaMin_of_sepLowerBound n A sigma hSep

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a Lyapunov operator sigma-min certificate makes the vectorized coefficient
    nonsingular. -/
theorem lyapunovVecCoeff_det_ne_zero_of_operator_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y)) :
    Not ((lyapunovVecCoeff n A).det = 0) := by
  have hSep := SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin
  exact lyapunovVecCoeff_det_ne_zero_of_sepLowerBound n A sigma hSep

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a Lyapunov operator sigma-min certificate makes the vectorized coefficient
    solve bijective. -/
theorem lyapunovVecCoeff_mulVec_bijective_of_operator_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y)) :
    Function.Bijective (Matrix.mulVec (lyapunovVecCoeff n A)) := by
  have hSep := SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin
  exact lyapunovVecCoeff_mulVec_bijective_of_sepLowerBound n A sigma hSep

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a Lyapunov operator sigma-min certificate gives unique vectorized
    coefficient solutions. -/
theorem existsUnique_lyapunovVecCoeff_mulVec_of_operator_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (c : Prod (Fin n) (Fin n) -> Real) :
    ExistsUnique (fun x : Prod (Fin n) (Fin n) -> Real =>
      Matrix.mulVec (lyapunovVecCoeff n A) x = c) := by
  have hSep := SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin
  exact existsUnique_lyapunovVecCoeff_mulVec_of_sepLowerBound n A sigma hSep c

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a Lyapunov operator sigma-min certificate gives the nonsingular-inverse
    vectorized coefficient solution. -/
theorem lyapunovVecCoeff_nonsingInv_mulVec_solution_of_operator_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (c : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A)
        (Matrix.mulVec (Inv.inv (lyapunovVecCoeff n A)) c) =
      c := by
  have hSep := SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin
  exact
    lyapunovVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound
      n A sigma hSep c

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a Lyapunov operator sigma-min certificate uniquely characterizes the
    nonsingular-inverse vectorized solution. -/
theorem existsUnique_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_operator_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (c : Prod (Fin n) (Fin n) -> Real) :
    ExistsUnique (fun x : Prod (Fin n) (Fin n) -> Real =>
      Matrix.mulVec (lyapunovVecCoeff n A) x = c) := by
  have hSep := SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin
  exact
    existsUnique_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound
      n A sigma hSep c

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a Lyapunov operator sigma-min certificate gives the right inverse action. -/
theorem lyapunovVecCoeff_mulVec_nonsingInv_mulVec_of_operator_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (rhs : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A)
        (Matrix.mulVec (Inv.inv (lyapunovVecCoeff n A)) rhs) =
      rhs := by
  have hSep := SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin
  exact
    lyapunovVecCoeff_mulVec_nonsingInv_mulVec_of_sepLowerBound
      n A sigma hSep rhs

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a Lyapunov operator sigma-min certificate gives the left inverse action. -/
theorem lyapunovVecCoeff_nonsingInv_mulVec_mulVec_of_operator_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (z : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (Inv.inv (lyapunovVecCoeff n A))
        (Matrix.mulVec (lyapunovVecCoeff n A) z) =
      z := by
  have hSep := SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin
  exact
    lyapunovVecCoeff_nonsingInv_mulVec_mulVec_of_sepLowerBound
      n A sigma hSep z

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a Lyapunov operator sigma-min certificate identifies exact vectorized
    solutions with the nonsingular-inverse vector. -/
theorem lyapunovVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_operator_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    {z rhs : Prod (Fin n) (Fin n) -> Real}
    (hz : Matrix.mulVec (lyapunovVecCoeff n A) z = rhs) :
    z =
      Matrix.mulVec (Inv.inv (lyapunovVecCoeff n A)) rhs := by
  have hSep := SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin
  exact
    lyapunovVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_sepLowerBound
      n A sigma hSep hz

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the Lyapunov coefficient sigma-min
    route from a supplied operator sigma-min certificate. -/
alias H16_eq16_2_27_lyapunovVecCoeff_sigmaMin_of_operator_sigmaMin :=
  lyapunovVecCoeff_sigmaMin_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for Lyapunov coefficient nonsingularity
    from a supplied operator sigma-min certificate. -/
alias H16_eq16_2_27_lyapunovVecCoeff_det_ne_zero_of_operator_sigmaMin :=
  lyapunovVecCoeff_det_ne_zero_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for Lyapunov coefficient bijectivity from a
    supplied operator sigma-min certificate. -/
alias H16_eq16_2_27_lyapunovVecCoeff_mulVec_bijective_of_operator_sigmaMin :=
  lyapunovVecCoeff_mulVec_bijective_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for unique Lyapunov coefficient solves
    from a supplied operator sigma-min certificate. -/
alias H16_eq16_2_27_existsUnique_lyapunovVecCoeff_mulVec_of_operator_sigmaMin :=
  existsUnique_lyapunovVecCoeff_mulVec_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the nonsingular-inverse Lyapunov
    coefficient solution from a supplied operator sigma-min certificate. -/
alias H16_eq16_2_27_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_operator_sigmaMin :=
  lyapunovVecCoeff_nonsingInv_mulVec_solution_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the unique nonsingular-inverse
    Lyapunov coefficient solve from a supplied operator sigma-min certificate. -/
alias H16_eq16_2_27_existsUnique_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_operator_sigmaMin :=
  existsUnique_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the right inverse action from a
    supplied operator sigma-min certificate. -/
alias H16_eq16_2_27_lyapunovVecCoeff_mulVec_nonsingInv_mulVec_of_operator_sigmaMin :=
  lyapunovVecCoeff_mulVec_nonsingInv_mulVec_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the left inverse action from a
    supplied operator sigma-min certificate. -/
alias H16_eq16_2_27_lyapunovVecCoeff_nonsingInv_mulVec_mulVec_of_operator_sigmaMin :=
  lyapunovVecCoeff_nonsingInv_mulVec_mulVec_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias identifying exact Lyapunov coefficient
    solutions with the nonsingular-inverse vector under a supplied operator
    sigma-min certificate. -/
alias H16_eq16_2_27_lyapunovVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_operator_sigmaMin :=
  lyapunovVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive exact-`sylvesterSepInf` lower bound for `sep(A,-A^T)`
    instantiates the determinant-based left nonsingular-inverse action. -/
theorem lyapunovVecCoeff_nonsingInv_mulVec_mulVec_of_pos_le_sylvesterSepInf
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A
      (fun i j => -matTranspose A i j))
    (z : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A)⁻¹
        (Matrix.mulVec (lyapunovVecCoeff n A) z) =
      z := by
  exact
    lyapunovVecCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
      n A
      (lyapunovVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A sigma hsigma hle)
      z

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive exact-`sylvesterSepInf` lower bound for `sep(A,-A^T)`
    instantiates the determinant-based right nonsingular-inverse action. -/
theorem lyapunovVecCoeff_mulVec_nonsingInv_mulVec_of_pos_le_sylvesterSepInf
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A
      (fun i j => -matTranspose A i j))
    (rhs : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (lyapunovVecCoeff n A)
        (Matrix.mulVec (lyapunovVecCoeff n A)⁻¹ rhs) =
      rhs := by
  exact
    lyapunovVecCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
      n A
      (lyapunovVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A sigma hsigma hle)
      rhs

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive exact-`sylvesterSepInf` lower bound for `sep(A,-A^T)` identifies
    any exact Lyapunov coefficient solution with the nonsingular-inverse
    vector. -/
theorem lyapunovVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_pos_le_sylvesterSepInf
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A
      (fun i j => -matTranspose A i j))
    {z rhs : Prod (Fin n) (Fin n) -> Real}
    (hz : Matrix.mulVec (lyapunovVecCoeff n A) z = rhs) :
    z =
      Matrix.mulVec (lyapunovVecCoeff n A)⁻¹ rhs := by
  exact
    lyapunovVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_det_ne_zero
      n A
      (lyapunovVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A sigma hsigma hle)
      hz

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the `SepLowerBound(A,-A^T)` left
    inverse action. -/
alias H16_eq16_2_27_lyapunovVecCoeff_nonsingInv_mulVec_mulVec_of_sepLowerBound :=
  lyapunovVecCoeff_nonsingInv_mulVec_mulVec_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the `SepLowerBound(A,-A^T)` right
    inverse action. -/
alias H16_eq16_2_27_lyapunovVecCoeff_mulVec_nonsingInv_mulVec_of_sepLowerBound :=
  lyapunovVecCoeff_mulVec_nonsingInv_mulVec_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias identifying exact Lyapunov coefficient
    solutions with the `SepLowerBound(A,-A^T)` nonsingular-inverse vector. -/
alias H16_eq16_2_27_lyapunovVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_sepLowerBound :=
  lyapunovVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the positive exact-`sep(A,-A^T)` left
    inverse action. -/
alias H16_eq16_2_27_lyapunovVecCoeff_nonsingInv_mulVec_mulVec_of_pos_le_sylvesterSepInf :=
  lyapunovVecCoeff_nonsingInv_mulVec_mulVec_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the positive exact-`sep(A,-A^T)` right
    inverse action. -/
alias H16_eq16_2_27_lyapunovVecCoeff_mulVec_nonsingInv_mulVec_of_pos_le_sylvesterSepInf :=
  lyapunovVecCoeff_mulVec_nonsingInv_mulVec_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias identifying exact Lyapunov coefficient
    solutions with the positive exact-infimum nonsingular-inverse vector. -/
alias H16_eq16_2_27_lyapunovVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_pos_le_sylvesterSepInf :=
  lyapunovVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and (16.23)-(16.26):
    a positive sigma-min certificate identifies any exact vectorized Sylvester
    coefficient solution with the nonsingular-inverse solution. -/
theorem sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_vecCoeff_sigmaMin
    (n : Nat) (A B : Fin n -> Fin n -> Real) {sigma : Real}
    (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    {x c : Prod (Fin n) (Fin n) -> Real}
    (hx : Matrix.mulVec (sylvesterVecCoeff n n A B) x = c) :
    x = Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ c := by
  exact
    sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_det_ne_zero
      n A B
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hx

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a positive sigma-min certificate identifies any exact vectorized Lyapunov
    coefficient solution with the nonsingular-inverse solution. -/
theorem lyapunovVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_vecCoeff_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) {sigma : Real}
    (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    {x c : Prod (Fin n) (Fin n) -> Real}
    (hx : Matrix.mulVec (lyapunovVecCoeff n A) x = c) :
    x = Matrix.mulVec (lyapunovVecCoeff n A)⁻¹ c := by
  exact
    lyapunovVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_det_ne_zero
      n A
      (lyapunovVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A hsigma hCoeff)
      hx

/-- Higham, 2nd ed., Chapter 16.1 and (16.23)-(16.26):
    a positive finite-Gram eigenvalue certificate identifies any exact
    vectorized Sylvester coefficient solution with the nonsingular-inverse
    solution. -/
theorem sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A B : Fin n -> Fin n -> Real) {lam : Real}
    (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    {x c : Prod (Fin n) (Fin n) -> Real}
    (hx : Matrix.mulVec (sylvesterVecCoeff n n A B) x = c) :
    x = Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ c := by
  exact
    sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_det_ne_zero
      n A B
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hx

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a positive finite-Gram eigenvalue certificate identifies any exact
    vectorized Lyapunov coefficient solution with the nonsingular-inverse
    solution. -/
theorem lyapunovVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A : Fin n -> Fin n -> Real) {lam : Real}
    (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    {x c : Prod (Fin n) (Fin n) -> Real}
    (hx : Matrix.mulVec (lyapunovVecCoeff n A) x = c) :
    x = Matrix.mulVec (lyapunovVecCoeff n A)⁻¹ c := by
  exact
    lyapunovVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_det_ne_zero
      n A
      (lyapunovVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A hlam hEig)
      hx

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5):
    a concrete left inverse with finite operator-2 radius identifies any exact
    vectorized Sylvester coefficient solution with the nonsingular-inverse
    solution. -/
theorem sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    {x c : Prod (Fin n) (Fin n) -> Real}
    (hx : Matrix.mulVec (sylvesterVecCoeff n n A B) x = c) :
    x = Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ c := by
  exact
    sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_det_ne_zero
      n A B
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hx

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a concrete left inverse with finite operator-2 radius identifies any exact
    vectorized Lyapunov coefficient solution with the nonsingular-inverse
    solution. -/
theorem lyapunovVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    {x c : Prod (Fin n) (Fin n) -> Real}
    (hx : Matrix.mulVec (lyapunovVecCoeff n A) x = c) :
    x = Matrix.mulVec (lyapunovVecCoeff n A)⁻¹ c := by
  exact
    lyapunovVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_det_ne_zero
      n A
      (lyapunovVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)
      hx

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5):
    determinant nonsingularity gives the unique vectorized Sylvester solution
    together with its explicit nonsingular-inverse formula. -/
theorem existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_det_ne_zero
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (hdet : (sylvesterVecCoeff n n A B).det ≠ 0)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (sylvesterVecCoeff n n A B) x = c ∧
        x = Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ c := by
  exact
    existsUnique_finiteMatrix_nonsingInv_mulVec_solution_of_det_ne_zero
      (sylvesterVecCoeff n n A B) hdet c

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    determinant nonsingularity gives the unique vectorized Lyapunov solution
    together with its explicit nonsingular-inverse formula. -/
theorem existsUnique_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_det_ne_zero
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (hdet : (lyapunovVecCoeff n A).det ≠ 0)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (lyapunovVecCoeff n A) x = c ∧
        x = Matrix.mulVec (lyapunovVecCoeff n A)⁻¹ c := by
  exact
    existsUnique_finiteMatrix_nonsingInv_mulVec_solution_of_det_ne_zero
      (lyapunovVecCoeff n A) hdet c

/-- Higham, 2nd ed., Chapter 16.1, equations (16.21)-(16.24):
    a positive sigma-min certificate gives the unique vectorized Sylvester
    solution together with its explicit nonsingular-inverse formula. -/
theorem existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_vecCoeff_sigmaMin
    (n : Nat) (A B : Fin n -> Fin n -> Real) {sigma : Real}
    (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (sylvesterVecCoeff n n A B) x = c ∧
        x = Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ c := by
  exact
    existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_det_ne_zero
      n A B
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      c

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a positive sigma-min certificate gives the unique vectorized Lyapunov
    solution together with its explicit nonsingular-inverse formula. -/
theorem existsUnique_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_vecCoeff_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) {sigma : Real}
    (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (lyapunovVecCoeff n A) x = c ∧
        x = Matrix.mulVec (lyapunovVecCoeff n A)⁻¹ c := by
  exact
    existsUnique_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_det_ne_zero
      n A
      (lyapunovVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A hsigma hCoeff)
      c

/-- Higham, 2nd ed., Chapter 16.1, equations (16.21)-(16.24):
    a positive finite-Gram eigenvalue certificate gives the unique vectorized
    Sylvester solution together with its explicit nonsingular-inverse formula. -/
theorem existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A B : Fin n -> Fin n -> Real) {lam : Real}
    (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (sylvesterVecCoeff n n A B) x = c ∧
        x = Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ c := by
  exact
    existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_det_ne_zero
      n A B
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      c

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a positive finite-Gram eigenvalue certificate gives the unique vectorized
    Lyapunov solution together with its explicit nonsingular-inverse formula. -/
theorem existsUnique_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A : Fin n -> Fin n -> Real) {lam : Real}
    (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (lyapunovVecCoeff n A) x = c ∧
        x = Matrix.mulVec (lyapunovVecCoeff n A)⁻¹ c := by
  exact
    existsUnique_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_det_ne_zero
      n A
      (lyapunovVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A hlam hEig)
      c

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5):
    a concrete left inverse with finite operator-2 radius gives the unique
    vectorized Sylvester solution together with its explicit
    nonsingular-inverse formula. -/
theorem existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (sylvesterVecCoeff n n A B) x = c ∧
        x = Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ c := by
  exact
    existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_det_ne_zero
      n A B
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      c

/-- Higham, 2nd ed., Chapter 16.2.1 and equation (16.27):
    a concrete left inverse with finite operator-2 radius gives the unique
    vectorized Lyapunov solution together with its explicit
    nonsingular-inverse formula. -/
theorem existsUnique_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (lyapunovVecCoeff n A) x = c ∧
        x = Matrix.mulVec (lyapunovVecCoeff n A)⁻¹ c := by
  exact
    existsUnique_lyapunovVecCoeff_nonsingInv_mulVec_solution_of_det_ne_zero
      n A
      (lyapunovVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)
      c

/-- Higham, 2nd ed., Chapter 16.1 and (16.23)-(16.26):
    a positive lower bound for the concrete vectorized Sylvester coefficient
    gives the operator lower bound consumed by the sigma-min Chapter 16
    perturbation and condition-number wrappers. -/
theorem sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x)) :
    forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y) := by
  intro Y
  have h := hCoeff (Matrix.vec Y)
  rw [sylvesterVecCoeff_mulVec_vec n n A B Y] at h
  rwa [finiteVecNorm2_vec_eq_frobNorm n n Y,
    sylvesterOpRect_square_eq_sylvesterOp n A B Y,
    finiteVecNorm2_vec_eq_frobNorm n n (sylvesterOp n A B Y)] at h

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.23)-(16.26):
    a supplied `SepLowerBound` certificate gives the Frobenius sigma-min lower
    bound for the Sylvester operator.  This is a certificate transfer from
    `sep(A,B)`, not an automatic spectral-separation theorem. -/
theorem sylvesterOp_sigmaMin_of_sepLowerBound (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A B sigma) :
    forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y) := by
  have hInv :=
    sylvesterInverseOpBound_of_sepLowerBound n A B sigma hSep.1 hSep
  intro Y
  have h := hInv Y
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hSep.1)
  calc
    sigma * frobNorm Y <=
        sigma * ((1 / sigma) * frobNorm (sylvesterOp n A B Y)) := hmul
    _ = frobNorm (sylvesterOp n A B Y) := by
      field_simp [ne_of_gt hSep.1]

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2), (16.23)-(16.26):
    a supplied `SepLowerBound` certificate transfers through the
    vec/Frobenius isometry to the concrete vectorized Sylvester coefficient
    sigma-min route. -/
theorem sylvesterVecCoeff_sigmaMin_of_sepLowerBound (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A B sigma) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x) := by
  intro x
  let Y : Fin n -> Fin n -> Real := fun i j => x (j, i)
  have hvecY : Matrix.vec Y = x := by
    ext p
    rfl
  have h :=
    sylvesterOp_sigmaMin_of_sepLowerBound n A B sigma hSep Y
  rw [<- hvecY]
  rw [sylvesterVecCoeff_mulVec_vec n n A B Y,
    finiteVecNorm2_vec_eq_frobNorm n n Y,
    sylvesterOpRect_square_eq_sylvesterOp n A B Y,
    finiteVecNorm2_vec_eq_frobNorm n n (sylvesterOp n A B Y)]
  exact h

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2), (16.23)-(16.26):
    a positive lower bound on the exact infimum model `sylvesterSepInf`
    transfers to the concrete vectorized Sylvester coefficient sigma-min
    route. -/
theorem sylvesterVecCoeff_sigmaMin_of_pos_le_sylvesterSepInf (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x) := by
  exact
    sylvesterVecCoeff_sigmaMin_of_sepLowerBound n A B sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hsigma hle)

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2)-(16.5):
    a supplied `SepLowerBound` certificate makes the concrete vectorized
    Sylvester coefficient nonsingular through the sigma-min determinant route. -/
theorem sylvesterVecCoeff_det_ne_zero_of_sepLowerBound (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A B sigma) :
    (sylvesterVecCoeff n n A B).det ≠ 0 := by
  exact
    sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin n A B hSep.1
      (sylvesterVecCoeff_sigmaMin_of_sepLowerBound n A B sigma hSep)

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2)-(16.5), (16.26):
    a positive lower bound on the exact infimum model `sylvesterSepInf`
    makes the concrete vectorized Sylvester coefficient nonsingular. -/
theorem sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B) :
    (sylvesterVecCoeff n n A B).det ≠ 0 := by
  exact
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hsigma hle)

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.4)-(16.8), (16.26):
    source `SepLowerBound` data supplies the internally chosen real-Schur
    active-block determinant package by way of the square vec/Kronecker
    determinant route. -/
theorem sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_sepLowerBound
    (n : Nat)
    (A B : RMatFn n n) (sigma : Real)
    (hSep : SepLowerBound n A B sigma) :
    exists (U R : RMatFn n n) (V S : RMatFn n n)
      (pA : Fin n -> Nat) (pB : Fin n -> Nat),
      IsOrthogonal n U /\
      IsOrthogonal n V /\
      A = rectMatMul U (rectMatMul R (matTranspose U)) /\
      B = rectMatMul V (rectMatMul S (matTranspose V)) /\
      Monotone pA /\
      (forall c : Nat, (Finset.univ.filter (fun i : Fin n => pA i = c)).card <= 2) /\
      (forall i j : Fin n, pA j < pA i -> R i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of R) pA /\
      Monotone pB /\
      (forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) /\
      (forall i j : Fin n, pB j < pB i -> S i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pB /\
      (forall p q : Fin n, q.val = p.val + 1 -> pB p = pB q ->
        IsAdjacentQuasiTriangularBlockFn n S p q /\
          Not (Matrix.det (sylvesterTwoColumnBlockCoeff n n R S p q) = 0)) := by
  exact
    sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_vecCoeff_det_ne_zero
      n n A B
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.4)-(16.8), (16.26),
    source-numbered alias for the exact real-Schur active-block determinant
    package from source `SepLowerBound` data. -/
alias H16_eq16_4_8_sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_sepLowerBound :=
  sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.4)-(16.8), (16.26):
    a positive lower bound on the exact `sylvesterSepInf` model supplies the
    internally chosen real-Schur active-block determinant package through the
    source `SepLowerBound` bridge. -/
theorem sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_pos_le_sylvesterSepInf
    (n : Nat)
    (A B : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B) :
    exists (U R : RMatFn n n) (V S : RMatFn n n)
      (pA : Fin n -> Nat) (pB : Fin n -> Nat),
      IsOrthogonal n U /\
      IsOrthogonal n V /\
      A = rectMatMul U (rectMatMul R (matTranspose U)) /\
      B = rectMatMul V (rectMatMul S (matTranspose V)) /\
      Monotone pA /\
      (forall c : Nat, (Finset.univ.filter (fun i : Fin n => pA i = c)).card <= 2) /\
      (forall i j : Fin n, pA j < pA i -> R i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of R) pA /\
      Monotone pB /\
      (forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) /\
      (forall i j : Fin n, pB j < pB i -> S i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pB /\
      (forall p q : Fin n, q.val = p.val + 1 -> pB p = pB q ->
        IsAdjacentQuasiTriangularBlockFn n S p q /\
          Not (Matrix.det (sylvesterTwoColumnBlockCoeff n n R S p q) = 0)) := by
  exact
    sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_sepLowerBound
      n A B sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hsigma hle)

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.4)-(16.8), (16.26),
    source-numbered alias for the exact real-Schur active-block determinant
    package from a positive lower bound on `sylvesterSepInf`. -/
alias H16_eq16_4_8_sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_pos_le_sylvesterSepInf :=
  sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.4)-(16.8), (16.26):
    a source `SepLowerBound` certificate feeds the exact real-Schur generated
    recursive-candidate route by first making the square vec/Kronecker
    Sylvester coefficient nonsingular.  This is an exact arithmetic bridge, not
    rounded Bartels-Stewart arithmetic or estimator production. -/
theorem exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_sepLowerBound
    (n : Nat)
    (A B : RMatFn n n) (C : RMatFn n n) (sigma : Real)
    (hSep : SepLowerBound n A B sigma) :
    exists (U R : RMatFn n n) (V S : RMatFn n n)
        (pA : Fin n -> Nat) (pB : Fin n -> Nat) (X : RMatFn n n),
      IsOrthogonal n U /\
      IsOrthogonal n V /\
      A = rectMatMul U (rectMatMul R (matTranspose U)) /\
      B = rectMatMul V (rectMatMul S (matTranspose V)) /\
      Monotone pA /\
      (forall c : Nat, (Finset.univ.filter (fun i : Fin n => pA i = c)).card <= 2) /\
      (forall i j : Fin n, pA j < pA i -> R i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of R) pA /\
      Monotone pB /\
      (forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) /\
      (forall i j : Fin n, pB j < pB i -> S i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pB /\
      IsSylvesterQuasiSchurGeneratedStepFormula n n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) X pB /\
      IsSylvesterSolutionRect n n A B C
        (rectMatMul U (rectMatMul X (matTranspose V))) :=
  exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_vecCoeff_det_ne_zero
    n n A B C
    (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.4)-(16.8), (16.26):
    original-coordinate unique solvability from a source `SepLowerBound`
    certificate and the exact real-Schur generated recursive-candidate route. -/
theorem existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_sepLowerBound_generated_step_formula_witness
    (n : Nat)
    (A B : RMatFn n n) (C : RMatFn n n) (sigma : Real)
    (hSep : SepLowerBound n A B sigma) :
    ExistsUnique (IsSylvesterSolutionRect n n A B C) :=
  existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_vecCoeff_det_ne_zero_generated_step_formula_witness
    n n A B C
    (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.4)-(16.8), (16.26),
    source-numbered alias for the exact real-Schur generated-step witness from
    a source `SepLowerBound` certificate. -/
theorem H16_eq16_4_8_exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_sepLowerBound
    (n : Nat)
    (A B : RMatFn n n) (C : RMatFn n n) (sigma : Real)
    (hSep : SepLowerBound n A B sigma) :
    exists (U R : RMatFn n n) (V S : RMatFn n n)
        (pA : Fin n -> Nat) (pB : Fin n -> Nat) (X : RMatFn n n),
      IsOrthogonal n U /\
      IsOrthogonal n V /\
      A = rectMatMul U (rectMatMul R (matTranspose U)) /\
      B = rectMatMul V (rectMatMul S (matTranspose V)) /\
      Monotone pA /\
      (forall c : Nat, (Finset.univ.filter (fun i : Fin n => pA i = c)).card <= 2) /\
      (forall i j : Fin n, pA j < pA i -> R i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of R) pA /\
      Monotone pB /\
      (forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) /\
      (forall i j : Fin n, pB j < pB i -> S i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pB /\
      IsSylvesterQuasiSchurGeneratedStepFormula n n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) X pB /\
      IsSylvesterSolutionRect n n A B C
        (rectMatMul U (rectMatMul X (matTranspose V))) :=
  exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_sepLowerBound
    n A B C sigma hSep

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.4)-(16.8), (16.26),
    source-numbered alias for original-coordinate unique solvability from a
    source `SepLowerBound` certificate. -/
theorem H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_sepLowerBound
    (n : Nat)
    (A B : RMatFn n n) (C : RMatFn n n) (sigma : Real)
    (hSep : SepLowerBound n A B sigma) :
    ExistsUnique (IsSylvesterSolutionRect n n A B C) :=
  existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_sepLowerBound_generated_step_formula_witness
    n A B C sigma hSep

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.4)-(16.8), (16.26):
    a positive lower bound on the exact `sylvesterSepInf` model feeds the
    exact real-Schur generated recursive-candidate route through the
    `SepLowerBound` bridge. -/
theorem exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_pos_le_sylvesterSepInf
    (n : Nat)
    (A B : RMatFn n n) (C : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B) :
    exists (U R : RMatFn n n) (V S : RMatFn n n)
        (pA : Fin n -> Nat) (pB : Fin n -> Nat) (X : RMatFn n n),
      IsOrthogonal n U /\
      IsOrthogonal n V /\
      A = rectMatMul U (rectMatMul R (matTranspose U)) /\
      B = rectMatMul V (rectMatMul S (matTranspose V)) /\
      Monotone pA /\
      (forall c : Nat, (Finset.univ.filter (fun i : Fin n => pA i = c)).card <= 2) /\
      (forall i j : Fin n, pA j < pA i -> R i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of R) pA /\
      Monotone pB /\
      (forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) /\
      (forall i j : Fin n, pB j < pB i -> S i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pB /\
      IsSylvesterQuasiSchurGeneratedStepFormula n n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) X pB /\
      IsSylvesterSolutionRect n n A B C
        (rectMatMul U (rectMatMul X (matTranspose V))) :=
  exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_sepLowerBound
    n A B C sigma
    (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hsigma hle)

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.4)-(16.8), (16.26):
    original-coordinate unique solvability from a positive lower bound on the
    exact `sylvesterSepInf` model and the exact real-Schur generated route. -/
theorem existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_pos_le_sylvesterSepInf_generated_step_formula_witness
    (n : Nat)
    (A B : RMatFn n n) (C : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B) :
    ExistsUnique (IsSylvesterSolutionRect n n A B C) :=
  existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_sepLowerBound_generated_step_formula_witness
    n A B C sigma
    (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hsigma hle)

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.4)-(16.8), (16.26),
    source-numbered alias for the exact real-Schur generated-step witness from
    a positive lower bound on `sylvesterSepInf`. -/
theorem H16_eq16_4_8_exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_pos_le_sylvesterSepInf
    (n : Nat)
    (A B : RMatFn n n) (C : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B) :
    exists (U R : RMatFn n n) (V S : RMatFn n n)
        (pA : Fin n -> Nat) (pB : Fin n -> Nat) (X : RMatFn n n),
      IsOrthogonal n U /\
      IsOrthogonal n V /\
      A = rectMatMul U (rectMatMul R (matTranspose U)) /\
      B = rectMatMul V (rectMatMul S (matTranspose V)) /\
      Monotone pA /\
      (forall c : Nat, (Finset.univ.filter (fun i : Fin n => pA i = c)).card <= 2) /\
      (forall i j : Fin n, pA j < pA i -> R i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of R) pA /\
      Monotone pB /\
      (forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) /\
      (forall i j : Fin n, pB j < pB i -> S i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pB /\
      IsSylvesterQuasiSchurGeneratedStepFormula n n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) X pB /\
      IsSylvesterSolutionRect n n A B C
        (rectMatMul U (rectMatMul X (matTranspose V))) :=
  exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_pos_le_sylvesterSepInf
    n A B C sigma hsigma hle

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.4)-(16.8), (16.26),
    source-numbered alias for original-coordinate unique solvability from a
    positive lower bound on `sylvesterSepInf`. -/
theorem H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_pos_le_sylvesterSepInf
    (n : Nat)
    (A B : RMatFn n n) (C : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B) :
    ExistsUnique (IsSylvesterSolutionRect n n A B C) :=
  existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_pos_le_sylvesterSepInf_generated_step_formula_witness
    n A B C sigma hsigma hle

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2)-(16.5), (16.26):
    a supplied `SepLowerBound` certificate gives the exact trivial-kernel
    statement for the vectorized Sylvester coefficient. -/
theorem sylvesterVecCoeff_mulVec_eq_zero_iff_of_sepLowerBound (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A B sigma)
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B) x = 0 ↔ x = 0 := by
  exact
    sylvesterVecCoeff_mulVec_eq_zero_iff_of_det_ne_zero n A B
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep) x

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2)-(16.5), (16.26):
    a positive lower bound on the exact infimum model `sylvesterSepInf` gives
    the exact trivial-kernel statement for the vectorized Sylvester
    coefficient. -/
theorem sylvesterVecCoeff_mulVec_eq_zero_iff_of_pos_le_sylvesterSepInf
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B)
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B) x = 0 ↔ x = 0 := by
  exact
    sylvesterVecCoeff_mulVec_eq_zero_iff_of_det_ne_zero n A B
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      x

/-- Higham, 2nd ed., Chapter 16.3, equation (16.26): source-numbered
    alias for the source `SepLowerBound` trivial-kernel route. -/
alias H16_eq16_26_sylvesterVecCoeff_mulVec_eq_zero_iff_of_sepLowerBound :=
  sylvesterVecCoeff_mulVec_eq_zero_iff_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.3, equation (16.26): source-numbered
    alias for the positive exact-infimum trivial-kernel route. -/
alias H16_eq16_26_sylvesterVecCoeff_mulVec_eq_zero_iff_of_pos_le_sylvesterSepInf :=
  sylvesterVecCoeff_mulVec_eq_zero_iff_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2)-(16.5), (16.26):
    a supplied `SepLowerBound` certificate makes the exact vectorized
    Sylvester coefficient solve bijective.  This is a determinant consequence
    of the supplied sep certificate, not an automatic eigenvalue-separation
    theorem. -/
theorem sylvesterVecCoeff_mulVec_bijective_of_sepLowerBound (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A B sigma) :
    Function.Bijective (Matrix.mulVec (sylvesterVecCoeff n n A B)) := by
  exact
    finiteMatrix_mulVec_bijective_of_det_ne_zero
      (sylvesterVecCoeff n n A B)
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2)-(16.5), (16.26):
    a supplied `SepLowerBound` certificate gives a unique exact vectorized
    Sylvester coefficient solution for every right-hand side. -/
theorem existsUnique_sylvesterVecCoeff_mulVec_of_sepLowerBound (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A B sigma)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (sylvesterVecCoeff n n A B) x = c := by
  exact
    existsUnique_finiteMatrix_mulVec_of_det_ne_zero
      (sylvesterVecCoeff n n A B)
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      c

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2)-(16.5), (16.26):
    a positive lower bound on the exact infimum model `sylvesterSepInf` makes
    the exact vectorized Sylvester coefficient solve bijective. -/
theorem sylvesterVecCoeff_mulVec_bijective_of_pos_le_sylvesterSepInf
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B) :
    Function.Bijective (Matrix.mulVec (sylvesterVecCoeff n n A B)) := by
  exact
    sylvesterVecCoeff_mulVec_bijective_of_sepLowerBound n A B sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hsigma hle)

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2)-(16.5), (16.26):
    a positive lower bound on the exact infimum model `sylvesterSepInf` gives a
    unique exact vectorized Sylvester coefficient solution for every
    right-hand side. -/
theorem existsUnique_sylvesterVecCoeff_mulVec_of_pos_le_sylvesterSepInf
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (sylvesterVecCoeff n n A B) x = c := by
  exact
    existsUnique_sylvesterVecCoeff_mulVec_of_sepLowerBound n A B sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hsigma hle)
      c

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.26): source-numbered alias for `SepLowerBound` vectorized
    coefficient bijectivity. -/
alias H16_eq16_2_26_sylvesterVecCoeff_mulVec_bijective_of_sepLowerBound :=
  sylvesterVecCoeff_mulVec_bijective_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.26): source-numbered alias for `SepLowerBound` vectorized unique
    solvability. -/
alias H16_eq16_2_26_existsUnique_sylvesterVecCoeff_mulVec_of_sepLowerBound :=
  existsUnique_sylvesterVecCoeff_mulVec_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.26): source-numbered alias for positive exact-infimum vectorized
    coefficient bijectivity. -/
alias H16_eq16_2_26_sylvesterVecCoeff_mulVec_bijective_of_pos_le_sylvesterSepInf :=
  sylvesterVecCoeff_mulVec_bijective_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.26): source-numbered alias for positive exact-infimum vectorized
    unique solvability. -/
alias H16_eq16_2_26_existsUnique_sylvesterVecCoeff_mulVec_of_pos_le_sylvesterSepInf :=
  existsUnique_sylvesterVecCoeff_mulVec_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2)-(16.5), (16.26):
    a supplied `SepLowerBound` certificate instantiates the determinant-based
    left nonsingular-inverse action for the vectorized Sylvester coefficient. -/
theorem sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_sepLowerBound
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A B sigma)
    (z : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹
        (Matrix.mulVec (sylvesterVecCoeff n n A B) z) =
      z := by
  exact
    sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
      n A B (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep) z

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2)-(16.5), (16.26):
    a supplied `SepLowerBound` certificate instantiates the determinant-based
    right nonsingular-inverse action for the vectorized Sylvester coefficient. -/
theorem sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_sepLowerBound
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A B sigma)
    (rhs : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)
        (Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ rhs) =
      rhs := by
  exact
    sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
      n A B (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep) rhs

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2)-(16.5), (16.26):
    a supplied `SepLowerBound` certificate identifies any exact Sylvester
    coefficient solution with the nonsingular-inverse vector. -/
theorem sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_sepLowerBound
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A B sigma)
    {z rhs : Prod (Fin n) (Fin n) -> Real}
    (hz : Matrix.mulVec (sylvesterVecCoeff n n A B) z = rhs) :
    z =
      Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ rhs := by
  exact
    sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_det_ne_zero
      n A B (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep) hz

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2)-(16.5), (16.26):
    a positive exact-`sylvesterSepInf` lower bound instantiates the
    determinant-based left nonsingular-inverse action. -/
theorem sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_pos_le_sylvesterSepInf
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B)
    (z : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹
        (Matrix.mulVec (sylvesterVecCoeff n n A B) z) =
      z := by
  exact
    sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
      n A B
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      z

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2)-(16.5), (16.26):
    a positive exact-`sylvesterSepInf` lower bound instantiates the
    determinant-based right nonsingular-inverse action. -/
theorem sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_pos_le_sylvesterSepInf
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B)
    (rhs : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)
        (Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ rhs) =
      rhs := by
  exact
    sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
      n A B
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      rhs

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2)-(16.5), (16.26):
    a positive exact-`sylvesterSepInf` lower bound identifies any exact
    Sylvester coefficient solution with the nonsingular-inverse vector. -/
theorem sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_pos_le_sylvesterSepInf
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B)
    {z rhs : Prod (Fin n) (Fin n) -> Real}
    (hz : Matrix.mulVec (sylvesterVecCoeff n n A B) z = rhs) :
    z =
      Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ rhs := by
  exact
    sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_det_ne_zero
      n A B
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hz

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.26): source-numbered alias for the `SepLowerBound` left inverse action. -/
alias H16_eq16_2_26_sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_sepLowerBound :=
  sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.26): source-numbered alias for the `SepLowerBound` right inverse action. -/
alias H16_eq16_2_26_sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_sepLowerBound :=
  sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.26): source-numbered alias identifying exact solutions with the
    `SepLowerBound` nonsingular-inverse vector. -/
alias H16_eq16_2_26_sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_sepLowerBound :=
  sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.26): source-numbered alias for the positive exact-infimum left inverse
    action. -/
alias H16_eq16_2_26_sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_pos_le_sylvesterSepInf :=
  sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.26): source-numbered alias for the positive exact-infimum right inverse
    action. -/
alias H16_eq16_2_26_sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_pos_le_sylvesterSepInf :=
  sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.26): source-numbered alias identifying exact solutions with the
    positive exact-infimum nonsingular-inverse vector. -/
alias H16_eq16_2_26_sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_pos_le_sylvesterSepInf :=
  sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2)-(16.5), (16.26):
    with a supplied `SepLowerBound` certificate, Mathlib's nonsingular inverse
    gives an explicit exact vectorized Sylvester coefficient solution. -/
theorem sylvesterVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A B sigma)
    (c : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)
        (Matrix.mulVec (Inv.inv (sylvesterVecCoeff n n A B)) c) =
      c := by
  have hdet := sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv (sylvesterVecCoeff n n A B)
      (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2)-(16.5), (16.26):
    the nonsingular-inverse vector supplied by a `SepLowerBound` certificate is
    the unique exact Sylvester coefficient solution for the right-hand side. -/
theorem existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A B sigma)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (sylvesterVecCoeff n n A B) x = c := by
  refine
    ⟨Matrix.mulVec (Inv.inv (sylvesterVecCoeff n n A B)) c,
      sylvesterVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound
        n A B sigma hSep c, ?_⟩
  intro y hy
  have hdet := sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep
  calc
    y =
        Matrix.mulVec (Inv.inv (sylvesterVecCoeff n n A B))
          (Matrix.mulVec (sylvesterVecCoeff n n A B) y) := by
        symm
        rw [Matrix.mulVec_mulVec,
          Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
            (isUnit_iff_ne_zero.mpr hdet),
          Matrix.one_mulVec]
    _ = Matrix.mulVec (Inv.inv (sylvesterVecCoeff n n A B)) c := by
        rw [hy]

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.26): source-numbered alias for the `SepLowerBound` nonsingular-inverse
    vectorized Sylvester coefficient solution. -/
alias H16_eq16_2_26_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound :=
  sylvesterVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.26): source-numbered alias for the `SepLowerBound` unique exact
    vectorized Sylvester coefficient solve witness. -/
alias H16_eq16_2_26_existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound :=
  existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    a Sylvester operator sigma-min certificate transfers to the concrete
    vectorized Sylvester coefficient sigma-min route. -/
theorem sylvesterVecCoeff_sigmaMin_of_operator_sigmaMin
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y)) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x) := by
  have hSep := SepLowerBound_sylvester_of_sigmaMin n A B sigma hsigma hSigmaMin
  exact sylvesterVecCoeff_sigmaMin_of_sepLowerBound n A B sigma hSep

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    a Sylvester operator sigma-min certificate makes the vectorized
    coefficient nonsingular. -/
theorem sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y)) :
    (sylvesterVecCoeff n n A B).det ≠ 0 := by
  have hSep := SepLowerBound_sylvester_of_sigmaMin n A B sigma hsigma hSigmaMin
  exact sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.25)-(16.26): a Sylvester operator sigma-min certificate supplies the
    internally chosen real-Schur active-block determinant package through the
    source `SepLowerBound` bridge. -/
theorem sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_operator_sigmaMin
    (n : Nat) (A B : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : RMatFn n n,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y)) :
    exists (U R : RMatFn n n) (V S : RMatFn n n)
      (pA : Fin n -> Nat) (pB : Fin n -> Nat),
      IsOrthogonal n U /\
      IsOrthogonal n V /\
      A = rectMatMul U (rectMatMul R (matTranspose U)) /\
      B = rectMatMul V (rectMatMul S (matTranspose V)) /\
      Monotone pA /\
      (forall c : Nat, (Finset.univ.filter (fun i : Fin n => pA i = c)).card <= 2) /\
      (forall i j : Fin n, pA j < pA i -> R i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of R) pA /\
      Monotone pB /\
      (forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) /\
      (forall i j : Fin n, pB j < pB i -> S i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pB /\
      (forall p q : Fin n, q.val = p.val + 1 -> pB p = pB q ->
        IsAdjacentQuasiTriangularBlockFn n S p q /\
          Not (Matrix.det (sylvesterTwoColumnBlockCoeff n n R S p q) = 0)) := by
  exact
    sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_sepLowerBound
      n A B sigma
      (SepLowerBound_sylvester_of_sigmaMin n A B sigma hsigma hSigmaMin)

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.25)-(16.26): an operator sigma-min certificate supplies a real-Schur
    generated-step formula witness and transfers it back to the original
    Sylvester equation. -/
theorem exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_operator_sigmaMin
    (n : Nat)
    (A B : RMatFn n n) (C : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : RMatFn n n,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y)) :
    exists (U R : RMatFn n n) (V S : RMatFn n n)
        (pA : Fin n -> Nat) (pB : Fin n -> Nat) (X : RMatFn n n),
      IsOrthogonal n U /\
      IsOrthogonal n V /\
      A = rectMatMul U (rectMatMul R (matTranspose U)) /\
      B = rectMatMul V (rectMatMul S (matTranspose V)) /\
      Monotone pA /\
      (forall c : Nat, (Finset.univ.filter (fun i : Fin n => pA i = c)).card <= 2) /\
      (forall i j : Fin n, pA j < pA i -> R i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of R) pA /\
      Monotone pB /\
      (forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) /\
      (forall i j : Fin n, pB j < pB i -> S i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pB /\
      IsSylvesterQuasiSchurGeneratedStepFormula n n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) X pB /\
      IsSylvesterSolutionRect n n A B C
        (rectMatMul U (rectMatMul X (matTranspose V))) :=
  exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_sepLowerBound
    n A B C sigma
    (SepLowerBound_sylvester_of_sigmaMin n A B sigma hsigma hSigmaMin)

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.25)-(16.26): the operator sigma-min certificate yields uniqueness of
    the original Sylvester solution via the generated real-Schur witness. -/
theorem existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_operator_sigmaMin_generated_step_formula_witness
    (n : Nat)
    (A B : RMatFn n n) (C : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : RMatFn n n,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y)) :
    ExistsUnique (IsSylvesterSolutionRect n n A B C) :=
  existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_sepLowerBound_generated_step_formula_witness
    n A B C sigma
    (SepLowerBound_sylvester_of_sigmaMin n A B sigma hsigma hSigmaMin)

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.25)-(16.26): source-numbered alias for the operator-sigma-min route to
    the internally chosen real-Schur active-block determinant package. -/
alias H16_eq16_4_8_sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_operator_sigmaMin :=
  sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.25)-(16.26): source-numbered alias for the operator-sigma-min route to
    a real-Schur generated-step original solution witness. -/
alias H16_eq16_4_8_exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_operator_sigmaMin :=
  exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.25)-(16.26): source-numbered alias for the operator-sigma-min route to
    original-coordinate unique solvability via the generated real-Schur
    witness. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_operator_sigmaMin :=
  existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_operator_sigmaMin_generated_step_formula_witness

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    a Sylvester operator sigma-min certificate gives the exact trivial-kernel
    statement for the vectorized coefficient. -/
theorem sylvesterVecCoeff_mulVec_eq_zero_iff_of_operator_sigmaMin
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B) x = 0 ↔ x = 0 := by
  exact
    sylvesterVecCoeff_mulVec_eq_zero_iff_of_det_ne_zero n A B
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      x

/-- Higham, 2nd ed., Chapter 16.3, equation (16.26):
    source-numbered form of the operator-sigma-min trivial-kernel route for the
    vectorized Sylvester coefficient. -/
theorem H16_eq16_26_sylvesterVecCoeff_mulVec_eq_zero_iff_of_operator_sigmaMin
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B) x = 0 ↔ x = 0 := by
  exact
    sylvesterVecCoeff_mulVec_eq_zero_iff_of_operator_sigmaMin
      n A B sigma hsigma hSigmaMin x

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    a Sylvester operator sigma-min certificate makes the vectorized
    coefficient map injective. -/
theorem sylvesterVecCoeff_mulVec_injective_of_operator_sigmaMin
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y)) :
    Function.Injective (Matrix.mulVec (sylvesterVecCoeff n n A B)) := by
  exact
    finiteMatrix_mulVec_injective_of_det_ne_zero
      (sylvesterVecCoeff n n A B)
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    a Sylvester operator sigma-min certificate makes the vectorized
    coefficient map surjective. -/
theorem sylvesterVecCoeff_mulVec_surjective_of_operator_sigmaMin
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y)) :
    Function.Surjective (Matrix.mulVec (sylvesterVecCoeff n n A B)) := by
  exact
    finiteMatrix_mulVec_surjective_of_det_ne_zero
      (sylvesterVecCoeff n n A B)
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    source-numbered alias for operator-sigma-min vectorized coefficient
    injectivity. -/
alias H16_eq16_26_sylvesterVecCoeff_mulVec_injective_of_operator_sigmaMin :=
  sylvesterVecCoeff_mulVec_injective_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    source-numbered alias for operator-sigma-min vectorized coefficient
    surjectivity. -/
alias H16_eq16_26_sylvesterVecCoeff_mulVec_surjective_of_operator_sigmaMin :=
  sylvesterVecCoeff_mulVec_surjective_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    a Sylvester operator sigma-min certificate makes the vectorized
    coefficient solve bijective. -/
theorem sylvesterVecCoeff_mulVec_bijective_of_operator_sigmaMin
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y)) :
    Function.Bijective (Matrix.mulVec (sylvesterVecCoeff n n A B)) := by
  have hSep := SepLowerBound_sylvester_of_sigmaMin n A B sigma hsigma hSigmaMin
  exact sylvesterVecCoeff_mulVec_bijective_of_sepLowerBound n A B sigma hSep

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    a Sylvester operator sigma-min certificate gives unique vectorized
    coefficient solutions. -/
theorem existsUnique_sylvesterVecCoeff_mulVec_of_operator_sigmaMin
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (c : Prod (Fin n) (Fin n) -> Real) :
    ExistsUnique (fun x : Prod (Fin n) (Fin n) -> Real =>
      Matrix.mulVec (sylvesterVecCoeff n n A B) x = c) := by
  have hSep := SepLowerBound_sylvester_of_sigmaMin n A B sigma hsigma hSigmaMin
  exact existsUnique_sylvesterVecCoeff_mulVec_of_sepLowerBound n A B sigma hSep c

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    a Sylvester operator sigma-min certificate gives the nonsingular-inverse
    vectorized coefficient solution. -/
theorem sylvesterVecCoeff_nonsingInv_mulVec_solution_of_operator_sigmaMin
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (c : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)
        (Matrix.mulVec (Inv.inv (sylvesterVecCoeff n n A B)) c) =
      c := by
  have hSep := SepLowerBound_sylvester_of_sigmaMin n A B sigma hsigma hSigmaMin
  exact
    sylvesterVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound
      n A B sigma hSep c

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    a Sylvester operator sigma-min certificate uniquely characterizes the
    nonsingular-inverse vectorized solution. -/
theorem existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_operator_sigmaMin
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (c : Prod (Fin n) (Fin n) -> Real) :
    ExistsUnique (fun x : Prod (Fin n) (Fin n) -> Real =>
      Matrix.mulVec (sylvesterVecCoeff n n A B) x = c) := by
  have hSep := SepLowerBound_sylvester_of_sigmaMin n A B sigma hsigma hSigmaMin
  exact
    existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound
      n A B sigma hSep c

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    a Sylvester operator sigma-min certificate gives the right inverse action. -/
theorem sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_operator_sigmaMin
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (rhs : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)
        (Matrix.mulVec (Inv.inv (sylvesterVecCoeff n n A B)) rhs) =
      rhs := by
  have hSep := SepLowerBound_sylvester_of_sigmaMin n A B sigma hsigma hSigmaMin
  exact
    sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_sepLowerBound
      n A B sigma hSep rhs

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    a Sylvester operator sigma-min certificate gives the left inverse action. -/
theorem sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_operator_sigmaMin
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (z : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (Inv.inv (sylvesterVecCoeff n n A B))
        (Matrix.mulVec (sylvesterVecCoeff n n A B) z) =
      z := by
  have hSep := SepLowerBound_sylvester_of_sigmaMin n A B sigma hsigma hSigmaMin
  exact
    sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_sepLowerBound
      n A B sigma hSep z

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    a Sylvester operator sigma-min certificate identifies exact vectorized
    solutions with the nonsingular-inverse vector. -/
theorem sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_operator_sigmaMin
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    {z rhs : Prod (Fin n) (Fin n) -> Real}
    (hz : Matrix.mulVec (sylvesterVecCoeff n n A B) z = rhs) :
    z =
      Matrix.mulVec (Inv.inv (sylvesterVecCoeff n n A B)) rhs := by
  have hSep := SepLowerBound_sylvester_of_sigmaMin n A B sigma hsigma hSigmaMin
  exact
    sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_sepLowerBound
      n A B sigma hSep hz

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied `SepLowerBound` certificate for `sep(A,-A^T)` transfers to the
    concrete Sylvester vectorized coefficient specialized as `B = -A^T`. -/
theorem sylvesterVecCoeff_lyapunovSpecial_sigmaMin_of_sepLowerBound
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x) := by
  exact
    sylvesterVecCoeff_sigmaMin_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied `SepLowerBound` certificate for `sep(A,-A^T)` makes the
    concrete Sylvester vectorized coefficient specialized as `B = -A^T`
    nonsingular. -/
theorem sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_sepLowerBound
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma) :
    Not (Matrix.det
      (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) := by
  exact
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied `SepLowerBound` certificate for `sep(A,-A^T)` makes the
    concrete Sylvester vectorized coefficient specialized as `B = -A^T` solve
    bijective. -/
theorem sylvesterVecCoeff_lyapunovSpecial_mulVec_bijective_of_sepLowerBound
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma) :
    Function.Bijective
      (Matrix.mulVec
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) := by
  exact
    sylvesterVecCoeff_mulVec_bijective_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied `SepLowerBound` certificate for `sep(A,-A^T)` gives unique
    concrete Sylvester vectorized coefficient solutions with `B = -A^T`. -/
theorem existsUnique_sylvesterVecCoeff_lyapunovSpecial_mulVec_of_sepLowerBound
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x = c := by
  exact
    existsUnique_sylvesterVecCoeff_mulVec_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep c

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied `SepLowerBound` certificate for `sep(A,-A^T)` gives the
    nonsingular-inverse solution for the concrete Sylvester coefficient
    specialized as `B = -A^T`. -/
theorem sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_sepLowerBound
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (c : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))
        (Matrix.mulVec
          (Inv.inv (sylvesterVecCoeff n n A
            (fun i j => -matTranspose A i j))) c) =
      c := by
  exact
    sylvesterVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep c

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied `SepLowerBound` certificate for `sep(A,-A^T)` uniquely
    characterizes the nonsingular-inverse solution for the concrete Sylvester
    coefficient specialized as `B = -A^T`. -/
theorem existsUnique_sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_sepLowerBound
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x = c := by
  exact
    existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound
      n A (fun i j => -matTranspose A i j) sigma hSep c

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied `SepLowerBound` certificate for `sep(A,-A^T)` gives the right
    inverse action for the concrete Sylvester coefficient specialized as
    `B = -A^T`. -/
theorem sylvesterVecCoeff_lyapunovSpecial_mulVec_nonsingInv_mulVec_of_sepLowerBound
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (rhs : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))
        (Matrix.mulVec
          (Inv.inv (sylvesterVecCoeff n n A
            (fun i j => -matTranspose A i j))) rhs) =
      rhs := by
  exact
    sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep rhs

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied `SepLowerBound` certificate for `sep(A,-A^T)` gives the left
    inverse action for the concrete Sylvester coefficient specialized as
    `B = -A^T`. -/
theorem sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_mulVec_of_sepLowerBound
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (z : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec
        (Inv.inv (sylvesterVecCoeff n n A
          (fun i j => -matTranspose A i j)))
        (Matrix.mulVec
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) z) =
      z := by
  exact
    sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep z

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied `SepLowerBound` certificate for `sep(A,-A^T)` identifies exact
    concrete Sylvester coefficient solutions with the nonsingular-inverse
    vector. -/
theorem sylvesterVecCoeff_lyapunovSpecial_eq_nonsingInv_mulVec_of_mulVec_eq_of_sepLowerBound
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    {z rhs : Prod (Fin n) (Fin n) -> Real}
    (hz : Matrix.mulVec
      (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) z = rhs) :
    z =
      Matrix.mulVec
        (Inv.inv (sylvesterVecCoeff n n A
          (fun i j => -matTranspose A i j))) rhs := by
  exact
    sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep hz

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive lower bound on the exact infimum model `sep(A,-A^T)` transfers
    to the concrete Sylvester vectorized coefficient specialized as
    `B = -A^T`. -/
theorem sylvesterVecCoeff_lyapunovSpecial_sigmaMin_of_pos_le_sylvesterSepInf
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A
      (fun i j => -matTranspose A i j)) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x) := by
  exact
    sylvesterVecCoeff_lyapunovSpecial_sigmaMin_of_sepLowerBound n A sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive lower bound on the exact infimum model `sep(A,-A^T)` makes the
    concrete Sylvester vectorized coefficient specialized as `B = -A^T`
    nonsingular. -/
theorem sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_pos_le_sylvesterSepInf
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A
      (fun i j => -matTranspose A i j)) :
    Not (Matrix.det
      (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) := by
  exact
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_sepLowerBound n A sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive lower bound on the exact infimum model `sep(A,-A^T)` makes the
    concrete Sylvester vectorized coefficient specialized as `B = -A^T` solve
    bijective. -/
theorem sylvesterVecCoeff_lyapunovSpecial_mulVec_bijective_of_pos_le_sylvesterSepInf
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A
      (fun i j => -matTranspose A i j)) :
    Function.Bijective
      (Matrix.mulVec
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) := by
  exact
    sylvesterVecCoeff_lyapunovSpecial_mulVec_bijective_of_sepLowerBound
      n A sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive lower bound on the exact infimum model `sep(A,-A^T)` gives
    unique concrete Sylvester vectorized coefficient solutions with
    `B = -A^T`. -/
theorem existsUnique_sylvesterVecCoeff_lyapunovSpecial_mulVec_of_pos_le_sylvesterSepInf
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A
      (fun i j => -matTranspose A i j))
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x = c := by
  exact
    existsUnique_sylvesterVecCoeff_lyapunovSpecial_mulVec_of_sepLowerBound
      n A sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      c

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive lower bound on the exact infimum model `sep(A,-A^T)` gives the
    nonsingular-inverse solution for the concrete Sylvester coefficient
    specialized as `B = -A^T`. -/
theorem sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_pos_le_sylvesterSepInf
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A
      (fun i j => -matTranspose A i j))
    (c : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))
        (Matrix.mulVec
          (Inv.inv (sylvesterVecCoeff n n A
            (fun i j => -matTranspose A i j))) c) =
      c := by
  exact
    sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_sepLowerBound
      n A sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      c

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive lower bound on the exact infimum model `sep(A,-A^T)` uniquely
    characterizes the nonsingular-inverse solution for the concrete Sylvester
    coefficient specialized as `B = -A^T`. -/
theorem existsUnique_sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_pos_le_sylvesterSepInf
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A
      (fun i j => -matTranspose A i j))
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x = c := by
  exact
    existsUnique_sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_sepLowerBound
      n A sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      c

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive lower bound on the exact infimum model `sep(A,-A^T)` gives the
    right inverse action for the concrete Sylvester coefficient specialized as
    `B = -A^T`. -/
theorem sylvesterVecCoeff_lyapunovSpecial_mulVec_nonsingInv_mulVec_of_pos_le_sylvesterSepInf
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A
      (fun i j => -matTranspose A i j))
    (rhs : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))
        (Matrix.mulVec
          (Inv.inv (sylvesterVecCoeff n n A
            (fun i j => -matTranspose A i j))) rhs) =
      rhs := by
  exact
    sylvesterVecCoeff_lyapunovSpecial_mulVec_nonsingInv_mulVec_of_sepLowerBound
      n A sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      rhs

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive lower bound on the exact infimum model `sep(A,-A^T)` gives the
    left inverse action for the concrete Sylvester coefficient specialized as
    `B = -A^T`. -/
theorem sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_mulVec_of_pos_le_sylvesterSepInf
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A
      (fun i j => -matTranspose A i j))
    (z : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec
        (Inv.inv (sylvesterVecCoeff n n A
          (fun i j => -matTranspose A i j)))
        (Matrix.mulVec
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) z) =
      z := by
  exact
    sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_mulVec_of_sepLowerBound
      n A sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      z

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive lower bound on the exact infimum model `sep(A,-A^T)` identifies
    exact concrete Sylvester coefficient solutions with the nonsingular-inverse
    vector. -/
theorem sylvesterVecCoeff_lyapunovSpecial_eq_nonsingInv_mulVec_of_mulVec_eq_of_pos_le_sylvesterSepInf
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A
      (fun i j => -matTranspose A i j))
    {z rhs : Prod (Fin n) (Fin n) -> Real}
    (hz : Matrix.mulVec
      (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) z = rhs) :
    z =
      Matrix.mulVec
        (Inv.inv (sylvesterVecCoeff n n A
          (fun i j => -matTranspose A i j))) rhs := by
  exact
    sylvesterVecCoeff_lyapunovSpecial_eq_nonsingInv_mulVec_of_mulVec_eq_of_sepLowerBound
      n A sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      hz

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the Lyapunov-specialized Sylvester
    coefficient sigma-min route from a source `SepLowerBound(A,-A^T)`. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_sigmaMin_of_sepLowerBound :=
  sylvesterVecCoeff_lyapunovSpecial_sigmaMin_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for Lyapunov-specialized Sylvester
    coefficient nonsingularity from a source `SepLowerBound(A,-A^T)`. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_sepLowerBound :=
  sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for Lyapunov-specialized Sylvester
    coefficient bijectivity from a source `SepLowerBound(A,-A^T)`. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_mulVec_bijective_of_sepLowerBound :=
  sylvesterVecCoeff_lyapunovSpecial_mulVec_bijective_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for unique Lyapunov-specialized Sylvester
    coefficient solves from a source `SepLowerBound(A,-A^T)`. -/
alias H16_eq16_2_27_existsUnique_sylvesterVecCoeff_lyapunovSpecial_mulVec_of_sepLowerBound :=
  existsUnique_sylvesterVecCoeff_lyapunovSpecial_mulVec_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the nonsingular-inverse
    Lyapunov-specialized Sylvester coefficient solution from a source
    `SepLowerBound(A,-A^T)`. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_sepLowerBound :=
  sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the unique nonsingular-inverse
    Lyapunov-specialized Sylvester coefficient solve from a source
    `SepLowerBound(A,-A^T)`. -/
alias H16_eq16_2_27_existsUnique_sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_sepLowerBound :=
  existsUnique_sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the right inverse action of the
    Lyapunov-specialized Sylvester coefficient from a source
    `SepLowerBound(A,-A^T)`. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_mulVec_nonsingInv_mulVec_of_sepLowerBound :=
  sylvesterVecCoeff_lyapunovSpecial_mulVec_nonsingInv_mulVec_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the left inverse action of the
    Lyapunov-specialized Sylvester coefficient from a source
    `SepLowerBound(A,-A^T)`. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_mulVec_of_sepLowerBound :=
  sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_mulVec_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias identifying exact Lyapunov-specialized
    Sylvester coefficient solutions with the nonsingular-inverse vector under
    a source `SepLowerBound(A,-A^T)`. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_eq_nonsingInv_mulVec_of_mulVec_eq_of_sepLowerBound :=
  sylvesterVecCoeff_lyapunovSpecial_eq_nonsingInv_mulVec_of_mulVec_eq_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the Lyapunov-specialized Sylvester
    coefficient sigma-min route from a positive exact `sep(A,-A^T)` lower
    bound. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_sigmaMin_of_pos_le_sylvesterSepInf :=
  sylvesterVecCoeff_lyapunovSpecial_sigmaMin_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for Lyapunov-specialized Sylvester
    coefficient nonsingularity from a positive exact `sep(A,-A^T)` lower
    bound. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_pos_le_sylvesterSepInf :=
  sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for Lyapunov-specialized Sylvester
    coefficient bijectivity from a positive exact `sep(A,-A^T)` lower bound. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_mulVec_bijective_of_pos_le_sylvesterSepInf :=
  sylvesterVecCoeff_lyapunovSpecial_mulVec_bijective_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for unique Lyapunov-specialized Sylvester
    coefficient solves from a positive exact `sep(A,-A^T)` lower bound. -/
alias H16_eq16_2_27_existsUnique_sylvesterVecCoeff_lyapunovSpecial_mulVec_of_pos_le_sylvesterSepInf :=
  existsUnique_sylvesterVecCoeff_lyapunovSpecial_mulVec_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the nonsingular-inverse
    Lyapunov-specialized Sylvester coefficient solution from a positive exact
    `sep(A,-A^T)` lower bound. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_pos_le_sylvesterSepInf :=
  sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the unique nonsingular-inverse
    Lyapunov-specialized Sylvester coefficient solve from a positive exact
    `sep(A,-A^T)` lower bound. -/
alias H16_eq16_2_27_existsUnique_sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_pos_le_sylvesterSepInf :=
  existsUnique_sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the right inverse action of the
    Lyapunov-specialized Sylvester coefficient from a positive exact
    `sep(A,-A^T)` lower bound. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_mulVec_nonsingInv_mulVec_of_pos_le_sylvesterSepInf :=
  sylvesterVecCoeff_lyapunovSpecial_mulVec_nonsingInv_mulVec_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the left inverse action of the
    Lyapunov-specialized Sylvester coefficient from a positive exact
    `sep(A,-A^T)` lower bound. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_mulVec_of_pos_le_sylvesterSepInf :=
  sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_mulVec_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias identifying exact Lyapunov-specialized
    Sylvester coefficient solutions with the nonsingular-inverse vector under
    a positive exact `sep(A,-A^T)` lower bound. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_eq_nonsingInv_mulVec_of_mulVec_eq_of_pos_le_sylvesterSepInf :=
  sylvesterVecCoeff_lyapunovSpecial_eq_nonsingInv_mulVec_of_mulVec_eq_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a Lyapunov operator sigma-min certificate transfers to the concrete
    Sylvester vectorized coefficient specialized as `B = -A^T`. -/
theorem sylvesterVecCoeff_lyapunovSpecial_sigmaMin_of_operator_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y)) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x) := by
  have hSep := SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin
  exact
    sylvesterVecCoeff_sigmaMin_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a Lyapunov operator sigma-min certificate makes the concrete Sylvester
    vectorized coefficient specialized as `B = -A^T` nonsingular. -/
theorem sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y)) :
    (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)).det ≠ 0 := by
  have hSep := SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin
  exact
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a Lyapunov operator sigma-min certificate makes the concrete Sylvester
    vectorized coefficient specialized as `B = -A^T` solve bijective. -/
theorem sylvesterVecCoeff_lyapunovSpecial_mulVec_bijective_of_operator_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y)) :
    Function.Bijective
      (Matrix.mulVec
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) := by
  have hSep := SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin
  exact
    sylvesterVecCoeff_mulVec_bijective_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a Lyapunov operator sigma-min certificate gives unique concrete
    Sylvester vectorized coefficient solutions with `B = -A^T`. -/
theorem existsUnique_sylvesterVecCoeff_lyapunovSpecial_mulVec_of_operator_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x = c := by
  have hSep := SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin
  exact
    existsUnique_sylvesterVecCoeff_mulVec_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep c

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a Lyapunov operator sigma-min certificate gives the nonsingular-inverse
    solution for the concrete Sylvester coefficient with `B = -A^T`. -/
theorem sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_operator_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (c : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))
        (Matrix.mulVec
          (Inv.inv (sylvesterVecCoeff n n A
            (fun i j => -matTranspose A i j))) c) =
      c := by
  have hSep := SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin
  exact
    sylvesterVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep c

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a Lyapunov operator sigma-min certificate uniquely characterizes the
    nonsingular-inverse solution for the concrete Sylvester coefficient. -/
theorem existsUnique_sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_operator_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x = c := by
  have hSep := SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin
  exact
    existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound
      n A (fun i j => -matTranspose A i j) sigma hSep c

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a Lyapunov operator sigma-min certificate gives the right inverse action
    for the concrete Sylvester coefficient with `B = -A^T`. -/
theorem sylvesterVecCoeff_lyapunovSpecial_mulVec_nonsingInv_mulVec_of_operator_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (rhs : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))
        (Matrix.mulVec
          (Inv.inv (sylvesterVecCoeff n n A
            (fun i j => -matTranspose A i j))) rhs) =
      rhs := by
  have hSep := SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin
  exact
    sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep rhs

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a Lyapunov operator sigma-min certificate gives the left inverse action
    for the concrete Sylvester coefficient with `B = -A^T`. -/
theorem sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_mulVec_of_operator_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (z : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec
        (Inv.inv (sylvesterVecCoeff n n A
          (fun i j => -matTranspose A i j)))
        (Matrix.mulVec
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) z) =
      z := by
  have hSep := SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin
  exact
    sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep z

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a Lyapunov operator sigma-min certificate identifies exact concrete
    Sylvester coefficient solutions with the nonsingular-inverse vector. -/
theorem sylvesterVecCoeff_lyapunovSpecial_eq_nonsingInv_mulVec_of_mulVec_eq_of_operator_sigmaMin
    (n : Nat) (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    {z rhs : Prod (Fin n) (Fin n) -> Real}
    (hz : Matrix.mulVec
      (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) z = rhs) :
    z =
      Matrix.mulVec
        (Inv.inv (sylvesterVecCoeff n n A
          (fun i j => -matTranspose A i j))) rhs := by
  have hSep := SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin
  exact
    sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep hz

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the Lyapunov-specialized Sylvester
    coefficient sigma-min route from a supplied operator sigma-min certificate. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_sigmaMin_of_operator_sigmaMin :=
  sylvesterVecCoeff_lyapunovSpecial_sigmaMin_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for Lyapunov-specialized Sylvester
    coefficient nonsingularity from a supplied operator sigma-min certificate. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin :=
  sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for Lyapunov-specialized Sylvester
    coefficient bijectivity from a supplied operator sigma-min certificate. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_mulVec_bijective_of_operator_sigmaMin :=
  sylvesterVecCoeff_lyapunovSpecial_mulVec_bijective_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for unique Lyapunov-specialized Sylvester
    coefficient solves from a supplied operator sigma-min certificate. -/
alias H16_eq16_2_27_existsUnique_sylvesterVecCoeff_lyapunovSpecial_mulVec_of_operator_sigmaMin :=
  existsUnique_sylvesterVecCoeff_lyapunovSpecial_mulVec_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the nonsingular-inverse
    Lyapunov-specialized Sylvester coefficient solution from a supplied
    operator sigma-min certificate. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_operator_sigmaMin :=
  sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the unique nonsingular-inverse
    Lyapunov-specialized Sylvester coefficient solve from a supplied operator
    sigma-min certificate. -/
alias H16_eq16_2_27_existsUnique_sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_operator_sigmaMin :=
  existsUnique_sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_solution_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the right inverse action of the
    Lyapunov-specialized Sylvester coefficient from a supplied operator
    sigma-min certificate. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_mulVec_nonsingInv_mulVec_of_operator_sigmaMin :=
  sylvesterVecCoeff_lyapunovSpecial_mulVec_nonsingInv_mulVec_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias for the left inverse action of the
    Lyapunov-specialized Sylvester coefficient from a supplied operator
    sigma-min certificate. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_mulVec_of_operator_sigmaMin :=
  sylvesterVecCoeff_lyapunovSpecial_nonsingInv_mulVec_mulVec_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.27): source-numbered alias identifying exact Lyapunov-specialized
    Sylvester coefficient solutions with the nonsingular-inverse vector under
    a supplied operator sigma-min certificate. -/
alias H16_eq16_2_27_sylvesterVecCoeff_lyapunovSpecial_eq_nonsingInv_mulVec_of_mulVec_eq_of_operator_sigmaMin :=
  sylvesterVecCoeff_lyapunovSpecial_eq_nonsingInv_mulVec_of_mulVec_eq_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2)-(16.5), (16.26):
    with a positive lower bound on `sylvesterSepInf`, Mathlib's nonsingular
    inverse gives an explicit exact vectorized Sylvester coefficient solution. -/
theorem sylvesterVecCoeff_nonsingInv_mulVec_solution_of_pos_le_sylvesterSepInf
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B)
    (c : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)
        (Matrix.mulVec (Inv.inv (sylvesterVecCoeff n n A B)) c) =
      c := by
  exact
    sylvesterVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound
      n A B sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hsigma hle)
      c

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.2)-(16.5), (16.26):
    a positive lower bound on `sylvesterSepInf` makes the nonsingular-inverse
    vector the unique exact Sylvester coefficient solution. -/
theorem existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_pos_le_sylvesterSepInf
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (sylvesterVecCoeff n n A B) x = c := by
  exact
    existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_sepLowerBound
      n A B sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hsigma hle)
      c

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.26): source-numbered alias for the positive exact-infimum
    nonsingular-inverse vectorized Sylvester coefficient solution. -/
alias H16_eq16_2_26_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_pos_le_sylvesterSepInf :=
  sylvesterVecCoeff_nonsingInv_mulVec_solution_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.1 and 16.3, equations (16.2) and
    (16.26): source-numbered alias for the positive exact-infimum unique exact
    vectorized Sylvester coefficient solve witness. -/
alias H16_eq16_2_26_existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_pos_le_sylvesterSepInf :=
  existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_pos_le_sylvesterSepInf

/-- A concrete left inverse and operator-2 radius for the printed Sylvester
    vec/Kronecker coefficient gives the inverse-operator bound used by the
    structured condition-number surface. -/
theorem sylvesterInverseOpBound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real}
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    SylvesterInverseOpBound n A B M := by
  intro Y
  have h :=
    finiteVecNorm2_le_mul_mulVec_of_left_inverse_finiteOpNorm2Le
      (sylvesterVecCoeff n n A B) Pinv hLeft hPinv (Matrix.vec Y)
  rw [sylvesterVecCoeff_mulVec_vec n n A B Y] at h
  rwa [finiteVecNorm2_vec_eq_frobNorm n n Y,
    sylvesterOpRect_square_eq_sylvesterOp n A B Y,
    finiteVecNorm2_vec_eq_frobNorm n n (sylvesterOp n A B Y)] at h

/-- Higham, 2nd ed., Chapter 16.1 and (16.23)-(16.26):
    a Gram-eigenvalue lower bound for the concrete vectorized Sylvester
    coefficient gives the Frobenius lower bound for the Sylvester operator. -/
theorem sylvesterOp_sigmaMin_of_vecCoeff_gram_eigenvalues (n : Nat)
    (A B : Fin n -> Fin n -> Real) {lam : Real} (hlam : 0 <= lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p) :
    forall Y : Fin n -> Fin n -> Real,
      Real.sqrt lam * frobNorm Y <= frobNorm (sylvesterOp n A B Y) := by
  exact
    sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B (Real.sqrt lam)
      (sylvesterVecCoeff_sigmaMin_of_gram_eigenvalues n A B hlam hEig)

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.23)-(16.26):
    a positive lower bound for the concrete vectorized Sylvester coefficient
    gives a `SepLowerBound` certificate. -/
theorem SepLowerBound_of_vecCoeff_sigmaMin (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x)) :
    SepLowerBound n A B sigma := by
  exact
    sepLowerBound_of_sylvesterOp_sigmaMin n A B sigma hsigma
      (sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B sigma hCoeff)

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.23)-(16.26): a concrete vectorized Sylvester coefficient sigma-min
    certificate supplies the internally chosen real-Schur active-block
    determinant package through the source `SepLowerBound` bridge. -/
theorem sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_vecCoeff_sigmaMin
    (n : Nat) (A B : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x)) :
    exists (U R : RMatFn n n) (V S : RMatFn n n)
      (pA : Fin n -> Nat) (pB : Fin n -> Nat),
      IsOrthogonal n U /\
      IsOrthogonal n V /\
      A = rectMatMul U (rectMatMul R (matTranspose U)) /\
      B = rectMatMul V (rectMatMul S (matTranspose V)) /\
      Monotone pA /\
      (forall c : Nat, (Finset.univ.filter (fun i : Fin n => pA i = c)).card <= 2) /\
      (forall i j : Fin n, pA j < pA i -> R i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of R) pA /\
      Monotone pB /\
      (forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) /\
      (forall i j : Fin n, pB j < pB i -> S i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pB /\
      (forall p q : Fin n, q.val = p.val + 1 -> pB p = pB q ->
        IsAdjacentQuasiTriangularBlockFn n S p q /\
          Not (Matrix.det (sylvesterTwoColumnBlockCoeff n n R S p q) = 0)) := by
  exact
    sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_sepLowerBound
      n A B sigma
      (SepLowerBound_of_vecCoeff_sigmaMin n A B sigma hsigma hCoeff)

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.23)-(16.26): a concrete vectorized Sylvester coefficient sigma-min
    certificate supplies a real-Schur generated-step formula witness and
    transfers it back to the original Sylvester equation. -/
theorem exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_vecCoeff_sigmaMin
    (n : Nat)
    (A B : RMatFn n n) (C : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x)) :
    exists (U R : RMatFn n n) (V S : RMatFn n n)
        (pA : Fin n -> Nat) (pB : Fin n -> Nat) (X : RMatFn n n),
      IsOrthogonal n U /\
      IsOrthogonal n V /\
      A = rectMatMul U (rectMatMul R (matTranspose U)) /\
      B = rectMatMul V (rectMatMul S (matTranspose V)) /\
      Monotone pA /\
      (forall c : Nat, (Finset.univ.filter (fun i : Fin n => pA i = c)).card <= 2) /\
      (forall i j : Fin n, pA j < pA i -> R i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of R) pA /\
      Monotone pB /\
      (forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) /\
      (forall i j : Fin n, pB j < pB i -> S i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pB /\
      IsSylvesterQuasiSchurGeneratedStepFormula n n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) X pB /\
      IsSylvesterSolutionRect n n A B C
        (rectMatMul U (rectMatMul X (matTranspose V))) :=
  exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_sepLowerBound
    n A B C sigma
    (SepLowerBound_of_vecCoeff_sigmaMin n A B sigma hsigma hCoeff)

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.23)-(16.26): the concrete vectorized Sylvester coefficient sigma-min
    certificate yields uniqueness of the original Sylvester solution via the
    generated real-Schur witness. -/
theorem existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_vecCoeff_sigmaMin_generated_step_formula_witness
    (n : Nat)
    (A B : RMatFn n n) (C : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x)) :
    ExistsUnique (IsSylvesterSolutionRect n n A B C) :=
  existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_sepLowerBound_generated_step_formula_witness
    n A B C sigma
    (SepLowerBound_of_vecCoeff_sigmaMin n A B sigma hsigma hCoeff)

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.23)-(16.26): source-numbered alias for the concrete vec-coefficient
    sigma-min route to the internally chosen real-Schur active-block
    determinant package. -/
alias H16_eq16_4_8_sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_vecCoeff_sigmaMin :=
  sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_vecCoeff_sigmaMin

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.23)-(16.26): source-numbered alias for the concrete vec-coefficient
    sigma-min route to a real-Schur generated-step original solution witness. -/
alias H16_eq16_4_8_exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_vecCoeff_sigmaMin :=
  exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_vecCoeff_sigmaMin

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.23)-(16.26): source-numbered alias for the concrete vec-coefficient
    sigma-min route to original-coordinate unique solvability via the generated
    real-Schur witness. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_vecCoeff_sigmaMin :=
  existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_vecCoeff_sigmaMin_generated_step_formula_witness

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.23)-(16.26):
    in positive dimension, a positive lower bound for the concrete vectorized
    Sylvester coefficient lower-bounds the exact `sep` infimum. -/
theorem sylvesterSepInf_ge_of_vecCoeff_sigmaMin (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hn : 0 < n) (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x)) :
    sigma <= sylvesterSepInf n A B := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n A B sigma
      (SepLowerBound_of_vecCoeff_sigmaMin n A B sigma hsigma hCoeff) hn

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.23)-(16.26):
    in positive dimension, a positive lower bound for the concrete vectorized
    Sylvester coefficient makes the exact `sep` infimum strictly positive. -/
theorem sylvesterSepInf_pos_of_vecCoeff_sigmaMin (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hn : 0 < n) (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x)) :
    0 < sylvesterSepInf n A B := by
  exact
    lt_of_lt_of_le hsigma
      (sylvesterSepInf_ge_of_vecCoeff_sigmaMin n A B sigma
        hn hsigma hCoeff)

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.23)-(16.26):
    a positive Gram-eigenvalue lower bound for the concrete vectorized
    Sylvester coefficient gives a `SepLowerBound` certificate. -/
theorem SepLowerBound_of_vecCoeff_gram_eigenvalues (n : Nat)
    (A B : Fin n -> Fin n -> Real) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p) :
    SepLowerBound n A B (Real.sqrt lam) := by
  exact
    sepLowerBound_of_sylvesterOp_sigmaMin n A B (Real.sqrt lam)
      (Real.sqrt_pos.mpr hlam)
      (sylvesterOp_sigmaMin_of_vecCoeff_gram_eigenvalues n A B
        (le_of_lt hlam) hEig)

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.23)-(16.26): a positive Gram-eigenvalue lower bound for the concrete
    vectorized Sylvester coefficient supplies the internally chosen real-Schur
    active-block determinant package through the source `SepLowerBound`
    bridge. -/
theorem sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A B : RMatFn n n) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p) :
    exists (U R : RMatFn n n) (V S : RMatFn n n)
      (pA : Fin n -> Nat) (pB : Fin n -> Nat),
      IsOrthogonal n U /\
      IsOrthogonal n V /\
      A = rectMatMul U (rectMatMul R (matTranspose U)) /\
      B = rectMatMul V (rectMatMul S (matTranspose V)) /\
      Monotone pA /\
      (forall c : Nat, (Finset.univ.filter (fun i : Fin n => pA i = c)).card <= 2) /\
      (forall i j : Fin n, pA j < pA i -> R i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of R) pA /\
      Monotone pB /\
      (forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) /\
      (forall i j : Fin n, pB j < pB i -> S i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pB /\
      (forall p q : Fin n, q.val = p.val + 1 -> pB p = pB q ->
        IsAdjacentQuasiTriangularBlockFn n S p q /\
          Not (Matrix.det (sylvesterTwoColumnBlockCoeff n n R S p q) = 0)) := by
  exact
    sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_sepLowerBound
      n A B (Real.sqrt lam)
      (SepLowerBound_of_vecCoeff_gram_eigenvalues n A B hlam hEig)

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.23)-(16.26): a positive Gram-eigenvalue lower bound for the concrete
    vectorized Sylvester coefficient supplies a real-Schur generated-step
    formula witness and transfers it back to the original Sylvester equation. -/
theorem exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_vecCoeff_gram_eigenvalues
    (n : Nat)
    (A B : RMatFn n n) (C : RMatFn n n) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p) :
    exists (U R : RMatFn n n) (V S : RMatFn n n)
        (pA : Fin n -> Nat) (pB : Fin n -> Nat) (X : RMatFn n n),
      IsOrthogonal n U /\
      IsOrthogonal n V /\
      A = rectMatMul U (rectMatMul R (matTranspose U)) /\
      B = rectMatMul V (rectMatMul S (matTranspose V)) /\
      Monotone pA /\
      (forall c : Nat, (Finset.univ.filter (fun i : Fin n => pA i = c)).card <= 2) /\
      (forall i j : Fin n, pA j < pA i -> R i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of R) pA /\
      Monotone pB /\
      (forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) /\
      (forall i j : Fin n, pB j < pB i -> S i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pB /\
      IsSylvesterQuasiSchurGeneratedStepFormula n n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) X pB /\
      IsSylvesterSolutionRect n n A B C
        (rectMatMul U (rectMatMul X (matTranspose V))) :=
  exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_sepLowerBound
    n A B C (Real.sqrt lam)
    (SepLowerBound_of_vecCoeff_gram_eigenvalues n A B hlam hEig)

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.23)-(16.26): the concrete Gram-eigenvalue certificate yields uniqueness
    of the original Sylvester solution via the generated real-Schur witness. -/
theorem existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_vecCoeff_gram_eigenvalues_generated_step_formula_witness
    (n : Nat)
    (A B : RMatFn n n) (C : RMatFn n n) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p) :
    ExistsUnique (IsSylvesterSolutionRect n n A B C) :=
  existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_sepLowerBound_generated_step_formula_witness
    n A B C (Real.sqrt lam)
    (SepLowerBound_of_vecCoeff_gram_eigenvalues n A B hlam hEig)

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.23)-(16.26): source-numbered alias for the concrete Gram-eigenvalue
    route to the internally chosen real-Schur active-block determinant
    package. -/
alias H16_eq16_4_8_sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_vecCoeff_gram_eigenvalues :=
  sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_vecCoeff_gram_eigenvalues

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.23)-(16.26): source-numbered alias for the concrete Gram-eigenvalue
    route to a real-Schur generated-step original solution witness. -/
alias H16_eq16_4_8_exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_vecCoeff_gram_eigenvalues :=
  exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_vecCoeff_gram_eigenvalues

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.23)-(16.26): source-numbered alias for the concrete Gram-eigenvalue
    route to original-coordinate unique solvability via the generated
    real-Schur witness. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_vecCoeff_gram_eigenvalues :=
  existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_vecCoeff_gram_eigenvalues_generated_step_formula_witness

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.23)-(16.26):
    in positive dimension, a positive Gram-eigenvalue lower bound for the
    concrete vectorized Sylvester coefficient lower-bounds the exact `sep`
    infimum. -/
theorem sylvesterSepInf_ge_of_vecCoeff_gram_eigenvalues (n : Nat)
    (A B : Fin n -> Fin n -> Real) {lam : Real}
    (hn : 0 < n) (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p) :
    Real.sqrt lam <= sylvesterSepInf n A B := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n A B (Real.sqrt lam)
      (SepLowerBound_of_vecCoeff_gram_eigenvalues n A B hlam hEig) hn

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.23)-(16.26):
    in positive dimension, a positive Gram-eigenvalue lower bound for the
    concrete vectorized Sylvester coefficient makes the exact `sep` infimum
    strictly positive. -/
theorem sylvesterSepInf_pos_of_vecCoeff_gram_eigenvalues (n : Nat)
    (A B : Fin n -> Fin n -> Real) {lam : Real}
    (hn : 0 < n) (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p) :
    0 < sylvesterSepInf n A B := by
  exact
    lt_of_lt_of_le (Real.sqrt_pos.mpr hlam)
      (sylvesterSepInf_ge_of_vecCoeff_gram_eigenvalues n A B
        hn hlam hEig)

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.23)-(16.26):
    a supplied concrete left inverse for the printed vec/Kronecker Sylvester
    coefficient gives a `SepLowerBound` certificate. -/
theorem SepLowerBound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    SepLowerBound n A B (1 / M) := by
  have hCoeff :=
    sylvesterVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
      n A B Pinv hM hLeft hPinv
  have hOp :
      forall Y : Fin n -> Fin n -> Real,
        (1 / M) * frobNorm Y <= frobNorm (sylvesterOp n A B Y) :=
    sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B (1 / M) hCoeff
  exact
    sepLowerBound_of_sylvesterOp_sigmaMin n A B (1 / M)
      (one_div_pos.mpr hM) hOp

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.23)-(16.26): a supplied concrete left inverse and finite operator norm
    bound for the vectorized Sylvester coefficient supplies the internally
    chosen real-Schur active-block determinant package through the source
    `SepLowerBound` bridge. -/
theorem sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : RMatFn n n)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    exists (U R : RMatFn n n) (V S : RMatFn n n)
      (pA : Fin n -> Nat) (pB : Fin n -> Nat),
      IsOrthogonal n U /\
      IsOrthogonal n V /\
      A = rectMatMul U (rectMatMul R (matTranspose U)) /\
      B = rectMatMul V (rectMatMul S (matTranspose V)) /\
      Monotone pA /\
      (forall c : Nat, (Finset.univ.filter (fun i : Fin n => pA i = c)).card <= 2) /\
      (forall i j : Fin n, pA j < pA i -> R i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of R) pA /\
      Monotone pB /\
      (forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) /\
      (forall i j : Fin n, pB j < pB i -> S i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pB /\
      (forall p q : Fin n, q.val = p.val + 1 -> pB p = pB q ->
        IsAdjacentQuasiTriangularBlockFn n S p q /\
          Not (Matrix.det (sylvesterTwoColumnBlockCoeff n n R S p q) = 0)) := by
  exact
    sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_sepLowerBound
      n A B (1 / M)
      (SepLowerBound_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.23)-(16.26): a supplied concrete left inverse and finite operator norm
    bound for the vectorized Sylvester coefficient supplies a real-Schur
    generated-step formula witness and transfers it back to the original
    Sylvester equation. -/
theorem exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat)
    (A B : RMatFn n n) (C : RMatFn n n)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    exists (U R : RMatFn n n) (V S : RMatFn n n)
        (pA : Fin n -> Nat) (pB : Fin n -> Nat) (X : RMatFn n n),
      IsOrthogonal n U /\
      IsOrthogonal n V /\
      A = rectMatMul U (rectMatMul R (matTranspose U)) /\
      B = rectMatMul V (rectMatMul S (matTranspose V)) /\
      Monotone pA /\
      (forall c : Nat, (Finset.univ.filter (fun i : Fin n => pA i = c)).card <= 2) /\
      (forall i j : Fin n, pA j < pA i -> R i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of R) pA /\
      Monotone pB /\
      (forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) /\
      (forall i j : Fin n, pB j < pB i -> S i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pB /\
      IsSylvesterQuasiSchurGeneratedStepFormula n n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) X pB /\
      IsSylvesterSolutionRect n n A B C
        (rectMatMul U (rectMatMul X (matTranspose V))) :=
  exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_sepLowerBound
    n A B C (1 / M)
    (SepLowerBound_of_vecCoeff_left_inverse_finiteOpNorm2Le
      n A B Pinv hM hLeft hPinv)

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.23)-(16.26): the concrete left-inverse finite-op-norm certificate
    yields uniqueness of the original Sylvester solution via the generated
    real-Schur witness. -/
theorem existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_vecCoeff_left_inverse_finiteOpNorm2Le_generated_step_formula_witness
    (n : Nat)
    (A B : RMatFn n n) (C : RMatFn n n)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    ExistsUnique (IsSylvesterSolutionRect n n A B C) :=
  existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_sepLowerBound_generated_step_formula_witness
    n A B C (1 / M)
    (SepLowerBound_of_vecCoeff_left_inverse_finiteOpNorm2Le
      n A B Pinv hM hLeft hPinv)

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.23)-(16.26): source-numbered alias for the concrete left-inverse
    finite-op-norm route to the internally chosen real-Schur active-block
    determinant package. -/
alias H16_eq16_4_8_sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_vecCoeff_left_inverse_finiteOpNorm2Le :=
  sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_vecCoeff_left_inverse_finiteOpNorm2Le

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.23)-(16.26): source-numbered alias for the concrete left-inverse
    finite-op-norm route to a real-Schur generated-step original solution
    witness. -/
alias H16_eq16_4_8_exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_vecCoeff_left_inverse_finiteOpNorm2Le :=
  exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_vecCoeff_left_inverse_finiteOpNorm2Le

/-- Higham, 2nd ed., Chapter 16.2-16.3, equations (16.4)-(16.8),
    (16.23)-(16.26): source-numbered alias for the concrete left-inverse
    finite-op-norm route to original-coordinate unique solvability via the
    generated real-Schur witness. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_vecCoeff_left_inverse_finiteOpNorm2Le :=
  existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_vecCoeff_left_inverse_finiteOpNorm2Le_generated_step_formula_witness

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.23)-(16.26):
    in positive dimension, a supplied concrete left inverse for the printed
    vec/Kronecker Sylvester coefficient lower-bounds the exact `sep` infimum. -/
theorem sylvesterSepInf_ge_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hn : 0 < n) (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    (1 / M) <= sylvesterSepInf n A B := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n A B (1 / M)
      (SepLowerBound_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hn

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.23)-(16.26):
    in positive dimension, a supplied concrete left inverse for the printed
    vec/Kronecker Sylvester coefficient makes the exact `sep` infimum strictly
    positive. -/
theorem sylvesterSepInf_pos_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hn : 0 < n) (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    0 < sylvesterSepInf n A B := by
  exact
    lt_of_lt_of_le (one_div_pos.mpr hM)
      (sylvesterSepInf_ge_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A B Pinv hn hM hLeft hPinv)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3):
    in the diagonal case, a uniform lower bound on the coefficient magnitudes
    `|a_i - b_j|` gives the concrete vectorized coefficient lower bound. -/
theorem sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge (n : Nat)
    (a b : Fin n -> Real) (sigma : Real)
    (hsigma : 0 <= sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec
          (sylvesterVecCoeff n n (Matrix.diagonal a) (Matrix.diagonal b)) x) := by
  classical
  intro x
  let d : Prod (Fin n) (Fin n) -> Real := fun p => a p.2 - b p.1
  have hmul :
      Matrix.mulVec
          (sylvesterVecCoeff n n (Matrix.diagonal a) (Matrix.diagonal b)) x =
        fun p => d p * x p := by
    rw [sylvesterVecCoeff_diagonal]
    ext p
    simp [d, Matrix.mulVec, dotProduct, Matrix.diagonal]
  have hsquares :
      sigma ^ 2 * finiteVecNorm2Sq x <=
        finiteVecNorm2Sq (fun p : Prod (Fin n) (Fin n) => d p * x p) := by
    unfold finiteVecNorm2Sq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _hp
    have hleft : -|d p| <= sigma := by
      linarith [abs_nonneg (d p), hsigma]
    have hsq_abs : sigma ^ 2 <= |d p| ^ 2 := by
      exact sq_le_sq' hleft (by simpa [d] using hgap p.2 p.1)
    calc
      sigma ^ 2 * x p ^ 2 <= |d p| ^ 2 * x p ^ 2 :=
        mul_le_mul_of_nonneg_right hsq_abs (sq_nonneg (x p))
      _ = (d p * x p) ^ 2 := by
        rw [sq_abs]
        ring
  have hleft_sq :
      (sigma * finiteVecNorm2 x) ^ 2 =
        sigma ^ 2 * finiteVecNorm2Sq x := by
    rw [show (sigma * finiteVecNorm2 x) ^ 2 =
        sigma ^ 2 * finiteVecNorm2 x ^ 2 by ring,
      finiteVecNorm2_sq]
  have hright_sq :
      finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n (Matrix.diagonal a) (Matrix.diagonal b)) x) ^ 2 =
        finiteVecNorm2Sq (fun p : Prod (Fin n) (Fin n) => d p * x p) := by
    rw [hmul, finiteVecNorm2_sq]
  have hsq :
      (sigma * finiteVecNorm2 x) ^ 2 <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n (Matrix.diagonal a) (Matrix.diagonal b)) x) ^ 2 := by
    simpa [hleft_sq, hright_sq] using hsquares
  have hleft_nonneg : 0 <= sigma * finiteVecNorm2 x :=
    mul_nonneg hsigma (finiteVecNorm2_nonneg x)
  have hright_nonneg :
      0 <= finiteVecNorm2
        (Matrix.mulVec
          (sylvesterVecCoeff n n (Matrix.diagonal a) (Matrix.diagonal b)) x) :=
    finiteVecNorm2_nonneg _
  have habs := (sq_le_sq).mp hsq
  simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using habs

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3),
    diagonal case: a uniform lower bound on `|a_i - b_j|` gives a finite
    Gram-eigenvalue lower bound for the concrete vectorized Sylvester
    coefficient. -/
theorem sylvesterVecCoeff_diagonal_gram_eigenvalues_ge_of_entrywise_abs_ge
    (n : Nat) (a b : Fin n -> Real) (sigma : Real)
    (hsigma : 0 <= sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    forall p : Prod (Fin n) (Fin n),
      sigma ^ 2 <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n (Matrix.diagonal a) (Matrix.diagonal b)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n (Matrix.diagonal a) (Matrix.diagonal b))) p := by
  exact
    finiteMatrixGram_eigenvalues_ge_of_sigmaMin_lower_bound
      (sylvesterVecCoeff n n (Matrix.diagonal a) (Matrix.diagonal b)) hsigma
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma hsigma hgap)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3),
    diagonal case: a positive uniform gap `|a_i - b_j| >= sigma` makes the
    square vec/Kronecker Sylvester coefficient nonsingular. -/
theorem sylvesterVecCoeff_diagonal_det_ne_zero_of_entrywise_abs_ge
    (n : Nat) (a b : Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    (sylvesterVecCoeff n n (Matrix.diagonal a) (Matrix.diagonal b)).det ≠ 0 := by
  exact
    sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) (Matrix.diagonal b) hsigma
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma (le_of_lt hsigma) hgap)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3):
    in positive dimension, pairwise spectral-coordinate exclusion
    `a_i != b_j` supplies a concrete positive minimum gap
    `sigma <= |a_i - b_j|`. -/
theorem exists_pos_sylvesterDiagonalGap_of_entrywise_ne (n : Nat)
    (a b : Fin n -> Real) (hn : 0 < n)
    (hsep : forall i j, a i ≠ b j) :
    ∃ sigma : Real, 0 < sigma ∧ forall i j, sigma <= |a i - b j| := by
  classical
  let gaps : Finset Real :=
    (Finset.univ : Finset (Prod (Fin n) (Fin n))).image
      (fun p : Prod (Fin n) (Fin n) => |a p.1 - b p.2|)
  have hgaps_ne : gaps.Nonempty := by
    let i0 : Fin n := ⟨0, hn⟩
    refine ⟨|a i0 - b i0|, ?_⟩
    exact Finset.mem_image.mpr ⟨(i0, i0), by simp, rfl⟩
  refine ⟨gaps.min' hgaps_ne, ?_, ?_⟩
  · have hmem : gaps.min' hgaps_ne ∈ gaps := Finset.min'_mem gaps hgaps_ne
    obtain ⟨p, _hp, hpval⟩ := Finset.mem_image.mp hmem
    have hdiff_ne : a p.1 - b p.2 ≠ 0 := by
      intro hzero
      exact hsep p.1 p.2 (sub_eq_zero.mp hzero)
    have hpos : 0 < |a p.1 - b p.2| := abs_pos.mpr hdiff_ne
    simpa [hpval] using hpos
  · intro i j
    exact
      Finset.min'_le gaps (|a i - b j|)
        (Finset.mem_image.mpr ⟨(i, j), by simp, rfl⟩)

/-- Higham, 2nd ed., Chapter 16.1 and equation (16.26), diagonal case:
    the concrete diagonal vec/Kronecker lower bound transfers to the
    Frobenius lower bound for the Sylvester operator. -/
theorem sylvesterOp_sigmaMin_diagonal_of_entrywise_abs_ge (n : Nat)
    (a b : Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <=
        frobNorm (sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) Y) := by
  exact
    sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) (Matrix.diagonal b) sigma
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma (le_of_lt hsigma) hgap)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.3)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    a uniform lower bound on the diagonal coordinate gaps `|a_i - b_j|`
    gives the same Frobenius lower bound for the original Sylvester operator
    after the supplied orthogonal coordinate transformations. -/
theorem sylvesterOp_sigmaMin_schurDiagonal_of_entrywise_abs_ge (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y) := by
  intro Y
  let Yc : Fin n -> Fin n -> Real :=
    rectMatMul (matTranspose U) (rectMatMul Y V)
  have hYnorm : frobNorm Yc = frobNorm Y := by
    dsimp [Yc]
    calc
      frobNorm (rectMatMul (matTranspose U) (rectMatMul Y V))
          = frobNorm (rectMatMul Y V) := by
            simpa [rectMatMul, matMul] using
              (frobNorm_orthogonal_left (matTranspose U)
                (rectMatMul Y V) hU.transpose)
      _ = frobNorm Y := by
            simpa [rectMatMul, matMul] using
              (frobNorm_orthogonal_right Y V hV)
  have hYexpand :
      rectMatMul U (rectMatMul Yc (matTranspose V)) = Y := by
    dsimp [Yc]
    exact rectMatMul_schur_coords_expand U V Y hU hV
  have htrans :
      sylvesterOpRect n n A B Y =
        rectMatMul U
          (rectMatMul
            (sylvesterOpRect n n (Matrix.diagonal a)
              (Matrix.diagonal b) Yc)
            (matTranspose V)) := by
    have h :=
      sylvester_schur_transform_identity n n
        U (Matrix.diagonal a) A V (Matrix.diagonal b) B Yc
        hU hV hA hB
    rwa [hYexpand] at h
  have hOut :
      frobNorm (sylvesterOp n A B Y) =
        frobNorm (sylvesterOp n (Matrix.diagonal a)
          (Matrix.diagonal b) Yc) := by
    rw [<- sylvesterOpRect_square_eq_sylvesterOp n A B Y, htrans]
    calc
      frobNorm
          (rectMatMul U
            (rectMatMul
              (sylvesterOpRect n n (Matrix.diagonal a)
                (Matrix.diagonal b) Yc)
              (matTranspose V)))
          = frobNorm
              (rectMatMul
                (sylvesterOpRect n n (Matrix.diagonal a)
                  (Matrix.diagonal b) Yc)
                (matTranspose V)) := by
            simpa [rectMatMul, matMul] using
              (frobNorm_orthogonal_left U
                (rectMatMul
                  (sylvesterOpRect n n (Matrix.diagonal a)
                    (Matrix.diagonal b) Yc)
                  (matTranspose V)) hU)
      _ = frobNorm
            (sylvesterOpRect n n (Matrix.diagonal a)
              (Matrix.diagonal b) Yc) := by
            simpa [rectMatMul, matMul] using
              (frobNorm_orthogonal_right
                (sylvesterOpRect n n (Matrix.diagonal a)
                  (Matrix.diagonal b) Yc)
                (matTranspose V) hV.transpose)
      _ = frobNorm (sylvesterOp n (Matrix.diagonal a)
            (Matrix.diagonal b) Yc) := by
            rw [sylvesterOpRect_square_eq_sylvesterOp]
  have hdiag :=
    sylvesterOp_sigmaMin_diagonal_of_entrywise_abs_ge n
      a b sigma hsigma hgap Yc
  calc
    sigma * frobNorm Y = sigma * frobNorm Yc := by
      rw [hYnorm]
    _ <= frobNorm (sylvesterOp n (Matrix.diagonal a)
          (Matrix.diagonal b) Yc) := hdiag
    _ = frobNorm (sylvesterOp n A B Y) := hOut.symm

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    the corresponding product-index vec/Kronecker coefficient inherits the
    same sigma lower bound from the Schur-coordinate diagonal gap. -/
theorem sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x) := by
  intro x
  let Y : Fin n -> Fin n -> Real := fun i j => x (j, i)
  have hvecY : Matrix.vec Y = x := by
    ext p
    rfl
  have h :=
    sylvesterOp_sigmaMin_schurDiagonal_of_entrywise_abs_ge n
      U A V B a b sigma hU hV hA hB hsigma hgap Y
  rw [<- hvecY]
  rw [sylvesterVecCoeff_mulVec_vec n n A B Y,
    finiteVecNorm2_vec_eq_frobNorm n n Y,
    sylvesterOpRect_square_eq_sylvesterOp n A B Y,
    finiteVecNorm2_vec_eq_frobNorm n n (sylvesterOp n A B Y)]
  exact h

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    a supplied Schur-coordinate gap gives a finite Gram-eigenvalue lower
    bound for the original vec/Kronecker Sylvester coefficient. -/
theorem sylvesterVecCoeff_schurDiagonal_gram_eigenvalues_ge_of_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    forall p : Prod (Fin n) (Fin n),
      sigma ^ 2 <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p := by
  exact
    finiteMatrixGram_eigenvalues_ge_of_sigmaMin_lower_bound
      (sylvesterVecCoeff n n A B) (le_of_lt hsigma)
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hsigma hgap)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3):
    for supplied orthogonal diagonal Schur coordinates, spectral-coordinate
    exclusion `a_i != b_j` supplies some positive sigma-min lower bound for the
    original vec/Kronecker Sylvester coefficient. -/
theorem exists_sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j) :
    ∃ sigma : Real, 0 < sigma ∧
      forall x : Prod (Fin n) (Fin n) -> Real,
        sigma * finiteVecNorm2 x <=
          finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x) := by
  obtain ⟨sigma, hsigma, hgap⟩ :=
    exists_pos_sylvesterDiagonalGap_of_entrywise_ne n a b hn hsep
  refine ⟨sigma, hsigma, ?_⟩
  exact
    sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
      U A V B a b sigma hU hV hA hB hsigma hgap

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3):
    for supplied orthogonal diagonal Schur coordinates, spectral-coordinate
    exclusion `a_i != b_j` supplies a positive Gram-eigenvalue lower bound for
    the original vec/Kronecker Sylvester coefficient. -/
theorem exists_sylvesterVecCoeff_schurDiagonal_gram_eigenvalues_ge_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j) :
    ∃ sigma : Real, 0 < sigma ∧
      forall p : Prod (Fin n) (Fin n),
        sigma ^ 2 <= finiteHermitianEigenvalues
          (finiteMatrixGram (sylvesterVecCoeff n n A B))
          (isSymmetricFiniteMatrix_finiteMatrixGram
            (sylvesterVecCoeff n n A B)) p := by
  obtain ⟨sigma, hsigma, hgap⟩ :=
    exists_pos_sylvesterDiagonalGap_of_entrywise_ne n a b hn hsep
  refine ⟨sigma, hsigma, ?_⟩
  exact
    sylvesterVecCoeff_schurDiagonal_gram_eigenvalues_ge_of_entrywise_abs_ge n
      U A V B a b sigma hU hV hA hB hsigma hgap

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case: a positive coordinate gap makes
    the original square vec/Kronecker Sylvester coefficient nonsingular. -/
theorem sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    (sylvesterVecCoeff n n A B).det ≠ 0 := by
  exact
    sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin n
      A B hsigma
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hsigma hgap)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    pairwise spectral-coordinate exclusion makes the original square
    vec/Kronecker Sylvester coefficient nonsingular. -/
theorem sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j) :
    (sylvesterVecCoeff n n A B).det ≠ 0 := by
  obtain ⟨sigma, hsigma, hgap⟩ :=
    exists_pos_sylvesterDiagonalGap_of_entrywise_ne n a b hn hsep
  exact
    sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_abs_ge n
      U A V B a b sigma hU hV hA hB hsigma hgap

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    spectral-coordinate exclusion gives the exact trivial-kernel statement for
    the original vec/Kronecker Sylvester coefficient. -/
theorem sylvesterVecCoeff_schurDiagonal_mulVec_eq_zero_iff_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j)
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B) x = 0 ↔ x = 0 := by
  exact
    sylvesterVecCoeff_mulVec_eq_zero_iff_of_det_ne_zero n A B
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne n
        U A V B a b hn hU hV hA hB hsep)
      x

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    spectral-coordinate exclusion makes the original vectorized coefficient
    action injective. -/
theorem sylvesterVecCoeff_schurDiagonal_mulVec_injective_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j) :
    Function.Injective (Matrix.mulVec (sylvesterVecCoeff n n A B)) := by
  exact
    finiteMatrix_mulVec_injective_of_det_ne_zero
      (sylvesterVecCoeff n n A B)
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne n
        U A V B a b hn hU hV hA hB hsep)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    spectral-coordinate exclusion makes the original vectorized coefficient
    action surjective. -/
theorem sylvesterVecCoeff_schurDiagonal_mulVec_surjective_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j) :
    Function.Surjective (Matrix.mulVec (sylvesterVecCoeff n n A B)) := by
  exact
    finiteMatrix_mulVec_surjective_of_det_ne_zero
      (sylvesterVecCoeff n n A B)
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne n
        U A V B a b hn hU hV hA hB hsep)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    spectral-coordinate exclusion makes the original vectorized coefficient
    solve bijective. -/
theorem sylvesterVecCoeff_schurDiagonal_mulVec_bijective_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j) :
    Function.Bijective (Matrix.mulVec (sylvesterVecCoeff n n A B)) := by
  exact
    finiteMatrix_mulVec_bijective_of_det_ne_zero
      (sylvesterVecCoeff n n A B)
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne n
        U A V B a b hn hU hV hA hB hsep)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    spectral-coordinate exclusion gives a unique vectorized coefficient
    solution for every right-hand side. -/
theorem existsUnique_sylvesterVecCoeff_schurDiagonal_mulVec_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (sylvesterVecCoeff n n A B) x = c := by
  exact
    existsUnique_finiteMatrix_mulVec_of_det_ne_zero
      (sylvesterVecCoeff n n A B)
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne n
        U A V B a b hn hU hV hA hB hsep)
      c

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    spectral-coordinate exclusion gives the right nonsingular-inverse action
    for the original vectorized coefficient. -/
theorem sylvesterVecCoeff_schurDiagonal_mulVec_nonsingInv_mulVec_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j)
    (rhs : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)
        (Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ rhs) =
      rhs := by
  exact
    sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero n A B
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne n
        U A V B a b hn hU hV hA hB hsep)
      rhs

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    spectral-coordinate exclusion gives the left nonsingular-inverse action
    for the original vectorized coefficient. -/
theorem sylvesterVecCoeff_schurDiagonal_nonsingInv_mulVec_mulVec_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j)
    (z : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹
        (Matrix.mulVec (sylvesterVecCoeff n n A B) z) =
      z := by
  exact
    sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero n A B
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne n
        U A V B a b hn hU hV hA hB hsep)
      z

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    spectral-coordinate exclusion identifies every exact vectorized coefficient
    solution with the nonsingular-inverse vector. -/
theorem sylvesterVecCoeff_schurDiagonal_eq_nonsingInv_mulVec_of_mulVec_eq_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j)
    {z rhs : Prod (Fin n) (Fin n) -> Real}
    (hz : Matrix.mulVec (sylvesterVecCoeff n n A B) z = rhs) :
    z = Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ rhs := by
  exact
    sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_det_ne_zero
      n A B
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne n
        U A V B a b hn hU hV hA hB hsep)
      hz

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    spectral-coordinate exclusion gives the unique vectorized coefficient
    solution together with its nonsingular-inverse formula. -/
theorem existsUnique_sylvesterVecCoeff_schurDiagonal_nonsingInv_mulVec_solution_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (sylvesterVecCoeff n n A B) x = c ∧
        x = Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ c := by
  exact
    existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_det_ne_zero
      n A B
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne n
        U A V B a b hn hU hV hA hB hsep)
      c

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26), supplied orthogonal
    diagonal Schur-coordinate case:
    a uniform Schur-coordinate gap gives a `SepLowerBound` certificate for
    the original Sylvester operator. -/
theorem SepLowerBound_schurDiagonal_of_entrywise_abs_ge (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    SepLowerBound n A B sigma := by
  exact
    sepLowerBound_of_sylvesterOp_sigmaMin n A B sigma hsigma
      (sylvesterOp_sigmaMin_schurDiagonal_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hsigma hgap)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26), supplied orthogonal
    diagonal Schur-coordinate case:
    a uniform Schur-coordinate gap is below the exact infimum model of
    `sep(A,B)` whenever the feasible ratio set is nonempty. -/
theorem sylvesterSepInf_schurDiagonal_ge_of_entrywise_abs_ge (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hne : (sylvesterSepRatios n A B).Nonempty) :
    sigma <= sylvesterSepInf n A B := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_nonempty n A B sigma
      (SepLowerBound_schurDiagonal_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hsigma hgap)
      hne

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26), supplied orthogonal
    diagonal Schur-coordinate case:
    in positive dimension, a uniform Schur-coordinate gap is below the exact
    infimum model of `sep(A,B)`. -/
theorem sylvesterSepInf_schurDiagonal_ge_of_entrywise_abs_ge_of_pos_dim
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hn : 0 < n) :
    sigma <= sylvesterSepInf n A B := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n A B sigma
      (SepLowerBound_schurDiagonal_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hsigma hgap)
      hn

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26): source-numbered
    alias for the supplied Schur-diagonal uniform-gap `SepLowerBound`
    certificate. -/
alias H16_eq16_26_SepLowerBound_schurDiagonal_of_entrywise_abs_ge :=
  SepLowerBound_schurDiagonal_of_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26): source-numbered
    alias for the supplied Schur-diagonal exact-infimum lower-bound route from
    nonempty feasible ratios. -/
alias H16_eq16_26_sylvesterSepInf_schurDiagonal_ge_of_entrywise_abs_ge :=
  sylvesterSepInf_schurDiagonal_ge_of_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26): source-numbered
    alias for the positive-dimensional supplied Schur-diagonal exact-infimum
    lower-bound route. -/
alias H16_eq16_26_sylvesterSepInf_schurDiagonal_ge_of_entrywise_abs_ge_of_pos_dim :=
  sylvesterSepInf_schurDiagonal_ge_of_entrywise_abs_ge_of_pos_dim

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3), and equation
    (16.26): for supplied orthogonal diagonal Schur coordinates, pairwise
    spectral-coordinate exclusion gives some positive `SepLowerBound`
    certificate for the original Sylvester operator. -/
theorem exists_SepLowerBound_schurDiagonal_of_entrywise_ne (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j) :
    ∃ sigma : Real, SepLowerBound n A B sigma := by
  obtain ⟨sigma, hsigma, hgap⟩ :=
    exists_pos_sylvesterDiagonalGap_of_entrywise_ne n a b hn hsep
  exact
    ⟨sigma, SepLowerBound_schurDiagonal_of_entrywise_abs_ge n
      U A V B a b sigma hU hV hA hB hsigma hgap⟩

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3), and equation
    (16.26): for supplied orthogonal diagonal Schur coordinates, pairwise
    spectral-coordinate exclusion gives a positive lower bound on the exact
    `sep(A,B)` infimum model. -/
theorem exists_sylvesterSepInf_schurDiagonal_pos_lower_bound_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j) :
    ∃ sigma : Real, 0 < sigma ∧ sigma <= sylvesterSepInf n A B := by
  obtain ⟨sigma, hsigma, hgap⟩ :=
    exists_pos_sylvesterDiagonalGap_of_entrywise_ne n a b hn hsep
  refine ⟨sigma, hsigma, ?_⟩
  exact
    sylvesterSepInf_schurDiagonal_ge_of_entrywise_abs_ge_of_pos_dim n
      U A V B a b sigma hU hV hA hB hsigma hgap hn

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3):
    source-numbered alias for the positive spectral-coordinate gap constructed
    from pairwise exclusion in positive dimension. -/
alias H16_eq16_2_3_exists_pos_sylvesterDiagonalGap_of_entrywise_ne :=
  exists_pos_sylvesterDiagonalGap_of_entrywise_ne

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3):
    source-numbered alias for the supplied Schur-diagonal sigma-min lower-bound
    route obtained from pairwise spectral-coordinate exclusion. -/
alias H16_eq16_2_3_exists_sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_ne :=
  exists_sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_ne

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3):
    source-numbered alias for the supplied Schur-diagonal Gram-eigenvalue
    lower-bound route obtained from pairwise spectral-coordinate exclusion. -/
alias H16_eq16_2_3_exists_sylvesterVecCoeff_schurDiagonal_gram_eigenvalues_ge_of_entrywise_ne :=
  exists_sylvesterVecCoeff_schurDiagonal_gram_eigenvalues_ge_of_entrywise_ne

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3), and Chapter
    16.4, equation (16.26): source-numbered alias for the positive
    `SepLowerBound` certificate obtained from supplied Schur-diagonal
    spectral-coordinate exclusion. -/
alias H16_eq16_2_3_26_exists_SepLowerBound_schurDiagonal_of_entrywise_ne :=
  exists_SepLowerBound_schurDiagonal_of_entrywise_ne

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3), and Chapter
    16.4, equation (16.26): source-numbered alias for the positive exact
    `sep(A,B)` lower-bound route obtained from supplied Schur-diagonal
    spectral-coordinate exclusion. -/
alias H16_eq16_2_3_26_exists_sylvesterSepInf_schurDiagonal_pos_lower_bound_of_entrywise_ne :=
  exists_sylvesterSepInf_schurDiagonal_pos_lower_bound_of_entrywise_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27),
    supplied orthogonal spectral-coordinate Lyapunov case:
    a uniform spectral-coordinate sum gap gives a `SepLowerBound` certificate
    for the Sylvester special case `sep(A,-A^T)`. -/
theorem SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    SepLowerBound n A (fun i j => -matTranspose A i j) sigma := by
  have hnegAT :
      (fun i j => -matTranspose A i j) =
        rectMatMul U
          (rectMatMul (Matrix.diagonal (fun i : Fin n => -a i))
            (matTranspose U)) := by
    rw [hA]
    ext i j
    simp [rectMatMul, matTranspose, Matrix.diagonal]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  have hgapSylv :
      forall i j, sigma <= |a i - (fun k : Fin n => -a k) j| := by
    intro i j
    simpa [sub_eq_add_neg] using hgap i j
  exact
    SepLowerBound_schurDiagonal_of_entrywise_abs_ge n
      U A U (fun i j => -matTranspose A i j)
      a (fun i : Fin n => -a i) sigma hU hU hA hnegAT
      hsigma hgapSylv

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27),
    supplied orthogonal spectral-coordinate Lyapunov case:
    the spectral-coordinate sum gap is below the exact infimum model of
    `sep(A,-A^T)` whenever the feasible ratio set is nonempty. -/
theorem sylvesterSepInf_lyapunovSpectralDiagonal_ge_of_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hne : (sylvesterSepRatios n A
      (fun i j => -matTranspose A i j)).Nonempty) :
    sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_nonempty n A
      (fun i j => -matTranspose A i j) sigma
      (SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      hne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27),
    supplied orthogonal spectral-coordinate Lyapunov case:
    in positive dimension, the spectral-coordinate sum gap is below the exact
    infimum model of `sep(A,-A^T)`. -/
theorem sylvesterSepInf_lyapunovSpectralDiagonal_ge_of_entrywise_abs_ge_of_pos_dim
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hn : 0 < n) :
    sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n A
      (fun i j => -matTranspose A i j) sigma
      (SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      hn

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26): source-numbered
    alias for the supplied spectral-coordinate Lyapunov `sep(A,-A^T)`
    lower-bound certificate. -/
alias H16_eq16_26_SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge :=
  SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26): source-numbered
    alias for the supplied spectral-coordinate Lyapunov exact-infimum
    lower-bound route from a nonempty feasible ratio set. -/
alias H16_eq16_26_sylvesterSepInf_lyapunovSpectralDiagonal_ge_of_entrywise_abs_ge :=
  sylvesterSepInf_lyapunovSpectralDiagonal_ge_of_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26): source-numbered
    alias for the positive-dimensional supplied spectral-coordinate Lyapunov
    exact-infimum lower-bound route. -/
alias H16_eq16_26_sylvesterSepInf_lyapunovSpectralDiagonal_ge_of_entrywise_abs_ge_of_pos_dim :=
  sylvesterSepInf_lyapunovSpectralDiagonal_ge_of_entrywise_abs_ge_of_pos_dim

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    a positive lower bound for the concrete vectorized Lyapunov coefficient
    gives the Lyapunov operator lower bound consumed by the sigma-min
    condition-number wrapper. -/
theorem lyapunovOp_sigmaMin_of_vecCoeff_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x)) :
    forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y) := by
  intro Y
  have h := hCoeff (Matrix.vec Y)
  rw [lyapunovVecCoeff_mulVec_vec n A Y] at h
  let Amat : Matrix (Fin n) (Fin n) Real := A
  let Ymat : Matrix (Fin n) (Fin n) Real := Y
  have hLY :
      Amat * Ymat + Ymat * Matrix.transpose Amat =
        lyapunovOp n A Y := by
    ext i j
    simp [Amat, Ymat, lyapunovOp, matMul, matTranspose, Matrix.mul_apply]
  rwa [finiteVecNorm2_vec_eq_frobNorm n n Y, hLY,
    finiteVecNorm2_vec_eq_frobNorm n n (lyapunovOp n A Y)] at h

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive lower bound for the concrete vectorized Lyapunov coefficient
    gives a `SepLowerBound` certificate for `sep(A, -A^T)`. -/
theorem SepLowerBound_lyapunov_of_vecCoeff_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x)) :
    SepLowerBound n A (fun i j => -matTranspose A i j) sigma := by
  have hOp := lyapunovOp_sigmaMin_of_vecCoeff_sigmaMin n A sigma hCoeff
  have hSylv : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <=
        frobNorm (sylvesterOp n A (fun i j => -matTranspose A i j) Y) := by
    intro Y
    have h := hOp Y
    rwa [lyapunovOp_eq_sylvesterOp n A Y] at h
  exact
    sepLowerBound_of_sylvesterOp_sigmaMin n A
      (fun i j => -matTranspose A i j) sigma hsigma hSylv

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    in positive dimension, a positive lower bound for the concrete vectorized
    Lyapunov coefficient lower-bounds the exact `sep(A, -A^T)` infimum. -/
theorem sylvesterSepInf_lyapunov_ge_of_vecCoeff_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hn : 0 < n) (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x)) :
    sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n A
      (fun i j => -matTranspose A i j) sigma
      (SepLowerBound_lyapunov_of_vecCoeff_sigmaMin
        n A sigma hsigma hCoeff)
      hn

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    in positive dimension, a positive lower bound for the concrete vectorized
    Lyapunov coefficient makes the exact `sep(A, -A^T)` infimum strictly
    positive. -/
theorem sylvesterSepInf_lyapunov_pos_of_vecCoeff_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hn : 0 < n) (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x)) :
    0 < sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact
    lt_of_lt_of_le hsigma
      (sylvesterSepInf_lyapunov_ge_of_vecCoeff_sigmaMin n A sigma
        hn hsigma hCoeff)

/-- A concrete left inverse and operator-2 radius for the printed Lyapunov
    vec/Kronecker coefficient gives the Lyapunov operator sigma-min lower
    bound. -/
theorem lyapunovOp_sigmaMin_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    forall Y : Fin n -> Fin n -> Real,
      (1 / M) * frobNorm Y <= frobNorm (lyapunovOp n A Y) := by
  exact
    lyapunovOp_sigmaMin_of_vecCoeff_sigmaMin n A (1 / M)
      (lyapunovVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)

/-- A concrete left inverse and operator-2 radius for the printed Lyapunov
    vec/Kronecker coefficient gives a `SepLowerBound` certificate for
    `sep(A, -A^T)`. -/
theorem SepLowerBound_lyapunov_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    SepLowerBound n A (fun i j => -matTranspose A i j) (1 / M) := by
  have hOp :=
    lyapunovOp_sigmaMin_of_vecCoeff_left_inverse_finiteOpNorm2Le
      n A Pinv hM hLeft hPinv
  have hSylv : forall Y : Fin n -> Fin n -> Real,
      (1 / M) * frobNorm Y <=
        frobNorm (sylvesterOp n A (fun i j => -matTranspose A i j) Y) := by
    intro Y
    have h := hOp Y
    rwa [lyapunovOp_eq_sylvesterOp n A Y] at h
  exact
    sepLowerBound_of_sylvesterOp_sigmaMin n A
      (fun i j => -matTranspose A i j) (1 / M)
      (one_div_pos.mpr hM) hSylv

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a concrete left inverse and operator-2 radius for the printed Lyapunov
    vec/Kronecker coefficient give an exact-infimum lower bound for
    `sep(A, -A^T)` in positive dimension. -/
theorem sylvesterSepInf_lyapunov_ge_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hn : 0 < n) (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    (1 / M) <= sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n A
      (fun i j => -matTranspose A i j) (1 / M)
      (SepLowerBound_lyapunov_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)
      hn

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    in positive dimension, a concrete left inverse and operator-2 radius for
    the printed Lyapunov vec/Kronecker coefficient make the exact
    `sep(A, -A^T)` infimum strictly positive. -/
theorem sylvesterSepInf_lyapunov_pos_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hn : 0 < n) (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    0 < sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact
    lt_of_lt_of_le (one_div_pos.mpr hM)
      (sylvesterSepInf_lyapunov_ge_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A Pinv hn hM hLeft hPinv)

/-- A concrete left inverse and operator-2 radius for the printed Lyapunov
    vec/Kronecker coefficient gives the inverse-operator bound used by the
    Lyapunov condition-number surface. -/
theorem lyapunovInverseOpBound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real}
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    LyapunovInverseOpBound n A M := by
  intro Y
  have h :=
    finiteVecNorm2_le_mul_mulVec_of_left_inverse_finiteOpNorm2Le
      (lyapunovVecCoeff n A) Pinv hLeft hPinv (Matrix.vec Y)
  rw [lyapunovVecCoeff_mulVec_vec n A Y] at h
  let Amat : Matrix (Fin n) (Fin n) Real := A
  let Ymat : Matrix (Fin n) (Fin n) Real := Y
  have hLY :
      Amat * Ymat + Ymat * Matrix.transpose Amat =
        lyapunovOp n A Y := by
    ext i j
    simp [Amat, Ymat, lyapunovOp, matMul, matTranspose, Matrix.mul_apply]
  rwa [finiteVecNorm2_vec_eq_frobNorm n n Y, hLY,
    finiteVecNorm2_vec_eq_frobNorm n n (lyapunovOp n A Y)] at h

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    a Gram-eigenvalue lower bound for the concrete vectorized Lyapunov
    coefficient gives the Frobenius lower bound for the Lyapunov operator. -/
theorem lyapunovOp_sigmaMin_of_vecCoeff_gram_eigenvalues (n : Nat)
    (A : Fin n -> Fin n -> Real) {lam : Real} (hlam : 0 <= lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p) :
    forall Y : Fin n -> Fin n -> Real,
      Real.sqrt lam * frobNorm Y <= frobNorm (lyapunovOp n A Y) := by
  exact
    lyapunovOp_sigmaMin_of_vecCoeff_sigmaMin n A (Real.sqrt lam)
      (lyapunovVecCoeff_sigmaMin_of_gram_eigenvalues n A hlam hEig)

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied Gram-eigenvalue lower bound for the concrete vectorized
    Lyapunov coefficient gives a `SepLowerBound` certificate for
    `sep(A, -A^T)`. -/
theorem SepLowerBound_lyapunov_of_vecCoeff_gram_eigenvalues (n : Nat)
    (A : Fin n -> Fin n -> Real) {lam : Real}
    (hlam : 0 <= lam) (hsqrt : 0 < Real.sqrt lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p) :
    SepLowerBound n A (fun i j => -matTranspose A i j) (Real.sqrt lam) := by
  have hOp :=
    lyapunovOp_sigmaMin_of_vecCoeff_gram_eigenvalues n A hlam hEig
  have hSylv : forall Y : Fin n -> Fin n -> Real,
      Real.sqrt lam * frobNorm Y <=
        frobNorm (sylvesterOp n A (fun i j => -matTranspose A i j) Y) := by
    intro Y
    have h := hOp Y
    rwa [lyapunovOp_eq_sylvesterOp n A Y] at h
  exact
    sepLowerBound_of_sylvesterOp_sigmaMin n A
      (fun i j => -matTranspose A i j) (Real.sqrt lam)
      hsqrt hSylv

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    in positive dimension, a supplied Gram-eigenvalue lower bound for the
    concrete vectorized Lyapunov coefficient lower-bounds the exact
    `sep(A, -A^T)` infimum. -/
theorem sylvesterSepInf_lyapunov_ge_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A : Fin n -> Fin n -> Real) {lam : Real}
    (hn : 0 < n) (hlam : 0 <= lam) (hsqrt : 0 < Real.sqrt lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p) :
    Real.sqrt lam <=
      sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n A
      (fun i j => -matTranspose A i j) (Real.sqrt lam)
      (SepLowerBound_lyapunov_of_vecCoeff_gram_eigenvalues
        n A hlam hsqrt hEig)
      hn

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    in positive dimension, a supplied Gram-eigenvalue lower bound for the
    concrete vectorized Lyapunov coefficient makes the exact `sep(A, -A^T)`
    infimum strictly positive. -/
theorem sylvesterSepInf_lyapunov_pos_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A : Fin n -> Fin n -> Real) {lam : Real}
    (hn : 0 < n) (hlam : 0 <= lam) (hsqrt : 0 < Real.sqrt lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p) :
    0 < sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact
    lt_of_lt_of_le hsqrt
      (sylvesterSepInf_lyapunov_ge_of_vecCoeff_gram_eigenvalues
        n A hn hlam hsqrt hEig)

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    a uniform lower bound on the diagonal Lyapunov coefficient magnitudes
    `|a_i + a_j|` gives the concrete vectorized coefficient lower bound. -/
theorem lyapunovVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge (n : Nat)
    (a : Fin n -> Real) (sigma : Real)
    (hsigma : 0 <= sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec (lyapunovVecCoeff n (Matrix.diagonal a)) x) := by
  classical
  intro x
  let d : Prod (Fin n) (Fin n) -> Real := fun p => a p.2 + a p.1
  let Y : Matrix (Fin n) (Fin n) Real := fun i j => x (j, i)
  have hvecY : Matrix.vec Y = x := by
    ext p
    rfl
  have hLY :
      Matrix.diagonal a * Y + Y * Matrix.transpose (Matrix.diagonal a) =
        fun i j => (a i + a j) * x (j, i) := by
    ext i j
    simp [Y, Matrix.mul_apply, Matrix.diagonal]
    ring
  have hmul :
      Matrix.mulVec (lyapunovVecCoeff n (Matrix.diagonal a)) x =
        fun p => d p * x p := by
    have h := lyapunovVecCoeff_mulVec_vec n (Matrix.diagonal a) Y
    rw [hvecY, hLY] at h
    ext p
    simpa [d, Matrix.vec] using congrFun h p
  have hsquares :
      sigma ^ 2 * finiteVecNorm2Sq x <=
        finiteVecNorm2Sq (fun p : Prod (Fin n) (Fin n) => d p * x p) := by
    unfold finiteVecNorm2Sq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _hp
    have hleft : -|d p| <= sigma := by
      linarith [abs_nonneg (d p), hsigma]
    have hsq_abs : sigma ^ 2 <= |d p| ^ 2 := by
      exact sq_le_sq' hleft (by simpa [d] using hgap p.2 p.1)
    calc
      sigma ^ 2 * x p ^ 2 <= |d p| ^ 2 * x p ^ 2 :=
        mul_le_mul_of_nonneg_right hsq_abs (sq_nonneg (x p))
      _ = (d p * x p) ^ 2 := by
        rw [sq_abs]
        ring
  have hleft_sq :
      (sigma * finiteVecNorm2 x) ^ 2 =
        sigma ^ 2 * finiteVecNorm2Sq x := by
    rw [show (sigma * finiteVecNorm2 x) ^ 2 =
        sigma ^ 2 * finiteVecNorm2 x ^ 2 by ring,
      finiteVecNorm2_sq]
  have hright_sq :
      finiteVecNorm2
          (Matrix.mulVec (lyapunovVecCoeff n (Matrix.diagonal a)) x) ^ 2 =
        finiteVecNorm2Sq (fun p : Prod (Fin n) (Fin n) => d p * x p) := by
    rw [hmul, finiteVecNorm2_sq]
  have hsq :
      (sigma * finiteVecNorm2 x) ^ 2 <=
        finiteVecNorm2
          (Matrix.mulVec (lyapunovVecCoeff n (Matrix.diagonal a)) x) ^ 2 := by
    simpa [hleft_sq, hright_sq] using hsquares
  have hleft_nonneg : 0 <= sigma * finiteVecNorm2 x :=
    mul_nonneg hsigma (finiteVecNorm2_nonneg x)
  have hright_nonneg :
      0 <= finiteVecNorm2
        (Matrix.mulVec (lyapunovVecCoeff n (Matrix.diagonal a)) x) :=
    finiteVecNorm2_nonneg _
  have habs := (sq_le_sq).mp hsq
  simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using habs

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    a uniform lower bound on `|a_i + a_j|` gives a finite Gram-eigenvalue
    lower bound for the concrete vectorized Lyapunov coefficient. -/
theorem lyapunovVecCoeff_diagonal_gram_eigenvalues_ge_of_entrywise_abs_ge
    (n : Nat) (a : Fin n -> Real) (sigma : Real)
    (hsigma : 0 <= sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    forall p : Prod (Fin n) (Fin n),
      sigma ^ 2 <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n (Matrix.diagonal a)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n (Matrix.diagonal a))) p := by
  exact
    finiteMatrixGram_eigenvalues_ge_of_sigmaMin_lower_bound
      (lyapunovVecCoeff n (Matrix.diagonal a)) hsigma
      (lyapunovVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a sigma hsigma hgap)

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    a positive uniform gap `|a_i + a_j| >= sigma` makes the square Lyapunov
    vec/Kronecker coefficient nonsingular. -/
theorem lyapunovVecCoeff_diagonal_det_ne_zero_of_entrywise_abs_ge
    (n : Nat) (a : Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    (lyapunovVecCoeff n (Matrix.diagonal a)).det ≠ 0 := by
  exact
    lyapunovVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) hsigma
      (lyapunovVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a sigma (le_of_lt hsigma) hgap)

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    the concrete diagonal Lyapunov vec/Kronecker lower bound transfers to the
    Frobenius lower bound for the Lyapunov operator. -/
theorem lyapunovOp_sigmaMin_diagonal_of_entrywise_abs_ge (n : Nat)
    (a : Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <=
        frobNorm (lyapunovOp n (Matrix.diagonal a) Y) := by
  exact
    lyapunovOp_sigmaMin_of_vecCoeff_sigmaMin n (Matrix.diagonal a) sigma
      (lyapunovVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a sigma (le_of_lt hsigma) hgap)

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    if `A = U diag(a) U^T`, then a uniform lower bound on
    `|a_i + a_j|` gives the same Frobenius lower bound for the original
    Lyapunov operator. -/
theorem lyapunovOp_sigmaMin_spectralDiagonal_of_entrywise_abs_ge (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y) := by
  have hnegAT :
      (fun i j => -matTranspose A i j) =
        rectMatMul U
          (rectMatMul (Matrix.diagonal (fun i : Fin n => -a i))
            (matTranspose U)) := by
    rw [hA]
    ext i j
    simp [rectMatMul, matTranspose, Matrix.diagonal]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  have hgapSylv :
      forall i j, sigma <= |a i - (fun k : Fin n => -a k) j| := by
    intro i j
    simpa [sub_eq_add_neg] using hgap i j
  intro Y
  have h :=
    sylvesterOp_sigmaMin_schurDiagonal_of_entrywise_abs_ge n
      U A U (fun i j => -matTranspose A i j)
      a (fun i : Fin n => -a i) sigma hU hU hA hnegAT
      hsigma hgapSylv Y
  rwa [<- lyapunovOp_eq_sylvesterOp n A Y] at h

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    the original-coordinate Lyapunov vec/Kronecker coefficient inherits the
    same sigma lower bound from the spectral-coordinate diagonal sums. -/
theorem lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x) := by
  intro x
  let Y : Matrix (Fin n) (Fin n) Real := fun i j => x (j, i)
  have hvecY : Matrix.vec Y = x := by
    ext p
    rfl
  have hOp :=
    lyapunovOp_sigmaMin_spectralDiagonal_of_entrywise_abs_ge n
      U A a sigma hU hA hsigma hgap Y
  let Amat : Matrix (Fin n) (Fin n) Real := A
  let Ymat : Matrix (Fin n) (Fin n) Real := Y
  have hLY :
      Amat * Ymat + Ymat * Matrix.transpose Amat = lyapunovOp n A Y := by
    ext i j
    simp [Amat, Ymat, Y, lyapunovOp, matMul, matTranspose, Matrix.mul_apply]
  rw [<- hvecY]
  rw [lyapunovVecCoeff_mulVec_vec n A Y,
    finiteVecNorm2_vec_eq_frobNorm n n Y, hLY,
    finiteVecNorm2_vec_eq_frobNorm n n (lyapunovOp n A Y)]
  exact hOp

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    a spectral-coordinate gap gives a finite Gram-eigenvalue lower bound for
    the original Lyapunov vec/Kronecker coefficient. -/
theorem lyapunovVecCoeff_spectralDiagonal_gram_eigenvalues_ge_of_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    forall p : Prod (Fin n) (Fin n),
      sigma ^ 2 <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p := by
  exact
    finiteMatrixGram_eigenvalues_ge_of_sigmaMin_lower_bound
      (lyapunovVecCoeff n A) (le_of_lt hsigma)
      (lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case: a positive spectral-coordinate sum gap makes the
    original square Lyapunov vec/Kronecker coefficient nonsingular. -/
theorem lyapunovVecCoeff_spectralDiagonal_det_ne_zero_of_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    (lyapunovVecCoeff n A).det ≠ 0 := by
  exact
    lyapunovVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin n
      A hsigma
      (lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    the structured `Psi` certificate follows from a positive lower bound on the
    printed Kronecker/vectorized Sylvester coefficient. -/
theorem sylvesterPsi_of_vecCoeff_sigmaMin_isPsiFirstOrderBound (n : Nat)
    (A B X : Fin n -> Fin n -> Real) (alpha beta gamma sigma : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (hX : 0 < frobNorm X)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x)) :
    SylvesterPsiFirstOrderBound n A B X alpha beta gamma
      (sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma)) := by
  exact
    sylvesterPsi_of_sigmaMin_isPsiFirstOrderBound n
      A B X alpha beta gamma sigma halpha hbeta hgamma hsigma hX
      (sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B sigma hCoeff)

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    a finite Gram-eigenvalue lower bound for the printed Sylvester
    vec/Kronecker coefficient instantiates the structured `Psi` certificate
    with inverse-operator constant `1 / sqrt(lam)`. -/
theorem sylvesterPsi_of_vecCoeff_gram_eigenvalues_isPsiFirstOrderBound
    (n : Nat)
    (A B X : Fin n -> Fin n -> Real) (alpha beta gamma lam : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hlam : 0 < lam) (hX : 0 < frobNorm X)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p) :
    SylvesterPsiFirstOrderBound n A B X alpha beta gamma
      (sylvesterPsi_of_inverseOpBound n X alpha beta gamma
        (1 / Real.sqrt lam)) := by
  exact
    sylvesterPsi_of_vecCoeff_sigmaMin_isPsiFirstOrderBound n
      A B X alpha beta gamma (Real.sqrt lam)
      halpha hbeta hgamma (Real.sqrt_pos.mpr hlam) hX
      (sylvesterVecCoeff_sigmaMin_of_gram_eigenvalues n A B
        (le_of_lt hlam) hEig)

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    a concrete left inverse and operator-2 radius for the printed Sylvester
    vec/Kronecker coefficient instantiates the structured `Psi` certificate
    directly, without first postulating a sigma-min lower bound. -/
theorem sylvesterPsi_of_vecCoeff_left_inverse_finiteOpNorm2Le_isPsiFirstOrderBound
    (n : Nat)
    (A B X : Fin n -> Fin n -> Real) (alpha beta gamma M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hM : 0 <= M) (hX : 0 < frobNorm X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    SylvesterPsiFirstOrderBound n A B X alpha beta gamma
      (sylvesterPsi_of_inverseOpBound n X alpha beta gamma M) := by
  exact
    sylvesterPsi_of_inverseOpBound_isPsiFirstOrderBound n
      A B X alpha beta gamma M halpha hbeta hgamma hM hX
      (sylvesterInverseOpBound_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A B Pinv hLeft hPinv)

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    source-facing first-order Frobenius Sylvester bound from a positive lower
    bound on the concrete Kronecker/vectorized Sylvester coefficient. -/
theorem sylvester_first_order_bound_of_vecCoeff_sigmaMin (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (hX : 0 < frobNorm X)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX <=
      sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) *
        frobNorm X *
        sylvesterScaledPerturbationTripleNorm n DeltaA DeltaB DeltaC
          alpha beta gamma := by
  exact
    sylvesterPsi_of_vecCoeff_sigmaMin_isPsiFirstOrderBound n
      A B X alpha beta gamma sigma halpha hbeta hgamma hsigma hX hCoeff
      DeltaA DeltaB DeltaC DeltaX hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    source-facing first-order Frobenius Sylvester bound from a finite
    Gram-eigenvalue lower bound for the concrete vectorized Sylvester
    coefficient. -/
theorem sylvester_first_order_bound_of_vecCoeff_gram_eigenvalues
    (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma lam : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hlam : 0 < lam) (hX : 0 < frobNorm X)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX <=
      sylvesterPsi_of_inverseOpBound n X alpha beta gamma
          (1 / Real.sqrt lam) *
        frobNorm X *
        sylvesterScaledPerturbationTripleNorm n DeltaA DeltaB DeltaC
          alpha beta gamma := by
  exact
    sylvesterPsi_of_vecCoeff_gram_eigenvalues_isPsiFirstOrderBound n
      A B X alpha beta gamma lam halpha hbeta hgamma hlam hX hEig
      DeltaA DeltaB DeltaC DeltaX hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    source-facing first-order Frobenius Sylvester bound from a concrete left
    inverse and operator-2 radius for the printed vec/Kronecker coefficient. -/
theorem sylvester_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hM : 0 <= M) (hX : 0 < frobNorm X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX <=
      sylvesterPsi_of_inverseOpBound n X alpha beta gamma M *
        frobNorm X *
        sylvesterScaledPerturbationTripleNorm n DeltaA DeltaB DeltaC
          alpha beta gamma := by
  exact
    sylvesterPsi_of_vecCoeff_left_inverse_finiteOpNorm2Le_isPsiFirstOrderBound
      n A B X alpha beta gamma M Pinv halpha hbeta hgamma hM hX hLeft hPinv
      DeltaA DeltaB DeltaC DeltaX hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    source-shaped first-order relative perturbation bound from a positive
    lower bound on the concrete Kronecker/vectorized Sylvester coefficient. -/
theorem H16_eq16_24_structured_condition_of_vecCoeff_sigmaMin (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_of_sigmaMin n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX
      (sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B sigma hCoeff)
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    source-shaped first-order relative perturbation bound from a concrete
    left inverse and operator-2 radius for the printed Sylvester
    vec/Kronecker coefficient. -/
theorem H16_eq16_24_structured_condition_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma M eps : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hM : 0 <= M) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma M * eps := by
  have hPsi :=
    sylvesterPsi_of_vecCoeff_left_inverse_finiteOpNorm2Le_isPsiFirstOrderBound
      n A B X alpha beta gamma M Pinv halpha hbeta hgamma hM hX hLeft hPinv
  have hPsi_nonneg :
      0 <= sylvesterPsi_of_inverseOpBound n X alpha beta gamma M := by
    unfold sylvesterPsi_of_inverseOpBound
    have hsum : 0 <= alpha + beta :=
      add_nonneg (le_of_lt halpha) (le_of_lt hbeta)
    have hprod : 0 <= (alpha + beta) * frobNorm X :=
      mul_nonneg hsum (le_of_lt hX)
    have hnum : 0 <= (alpha + beta) * frobNorm X + gamma :=
      add_nonneg hprod (le_of_lt hgamma)
    exact div_nonneg (mul_nonneg hM hnum) (le_of_lt hX)
  exact
    sylvester_relative_first_order_bound_of_psi n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma
      (sylvesterPsi_of_inverseOpBound n X alpha beta gamma M) eps
      hPsi hX hPsi_nonneg halpha hbeta hgamma heps
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    source-shaped first-order relative perturbation bound from a finite
    Gram-eigenvalue lower bound for the concrete vectorized Sylvester
    coefficient. -/
theorem H16_eq16_24_structured_condition_of_vecCoeff_gram_eigenvalues
    (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma lam eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hlam : 0 < lam) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma
          (1 / Real.sqrt lam) * eps := by
  exact
    H16_eq16_24_structured_condition_of_vecCoeff_sigmaMin n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma
      (Real.sqrt lam) eps halpha hbeta hgamma
      (Real.sqrt_pos.mpr hlam) heps hX
      (sylvesterVecCoeff_sigmaMin_of_gram_eigenvalues n A B
        (le_of_lt hlam) hEig)
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    relative Sylvester first-order perturbation bound from a positive lower
    bound on the concrete Kronecker/vectorized Sylvester coefficient. -/
theorem sylvester_relative_first_order_bound_of_vecCoeff_sigmaMin (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_of_vecCoeff_sigmaMin n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX hCoeff
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    relative Sylvester first-order perturbation bound from a concrete left
    inverse and operator-2 radius for the printed vec/Kronecker coefficient. -/
theorem sylvester_relative_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma M eps : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hM : 0 <= M) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma M * eps := by
  exact
    H16_eq16_24_structured_condition_of_vecCoeff_left_inverse_finiteOpNorm2Le
      n A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma M eps Pinv
      halpha hbeta hgamma hM heps hX hLeft hPinv
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    relative Sylvester first-order perturbation bound from a finite
    Gram-eigenvalue lower bound for the concrete vectorized Sylvester
    coefficient. -/
theorem sylvester_relative_first_order_bound_of_vecCoeff_gram_eigenvalues
    (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma lam eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hlam : 0 < lam) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma
          (1 / Real.sqrt lam) * eps := by
  exact
    H16_eq16_24_structured_condition_of_vecCoeff_gram_eigenvalues n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma lam eps
      halpha hbeta hgamma hlam heps hX hEig
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    source-numbered aliases for finite Gram-eigenvalue Sylvester
    first-order condition wrappers. -/
alias H16_eq16_23_sylvester_first_order_bound_of_vecCoeff_gram_eigenvalues :=
  sylvester_first_order_bound_of_vecCoeff_gram_eigenvalues

alias H16_eq16_24_sylvester_relative_first_order_bound_of_vecCoeff_gram_eigenvalues :=
  sylvester_relative_first_order_bound_of_vecCoeff_gram_eigenvalues

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24),
    diagonal case: source-shaped first-order relative perturbation bound from
    the concrete diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem H16_eq16_24_structured_condition_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a b : Fin n -> Real)
    (X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) (Matrix.diagonal b)
      X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma (le_of_lt hsigma) hgap)
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24),
    supplied orthogonal diagonal Schur-coordinate case:
    source-shaped first-order relative perturbation bound from the concrete
    Schur-diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem H16_eq16_24_structured_condition_schurDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_of_vecCoeff_sigmaMin n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hsigma hgap)
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24),
    diagonal case: Frobenius first-order Sylvester perturbation bound from the
    concrete diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a b : Fin n -> Real)
    (X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX <=
      sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) *
        frobNorm X *
        sylvesterScaledPerturbationTripleNorm n DeltaA DeltaB DeltaC
          alpha beta gamma := by
  exact
    sylvester_first_order_bound_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) (Matrix.diagonal b)
      X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma
      halpha hbeta hgamma hsigma hX
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma (le_of_lt hsigma) hgap)
      hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24),
    diagonal case: relative Sylvester first-order perturbation bound from the
    concrete diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_relative_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a b : Fin n -> Real)
    (X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_diagonal_of_vecCoeff_entrywise_abs_ge n
      a b X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX hgap
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24),
    supplied orthogonal diagonal Schur-coordinate case:
    Frobenius first-order Sylvester perturbation bound from the concrete
    Schur-diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_first_order_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX <=
      sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) *
        frobNorm X *
        sylvesterScaledPerturbationTripleNorm n DeltaA DeltaB DeltaC
          alpha beta gamma := by
  exact
    sylvester_first_order_bound_of_vecCoeff_sigmaMin n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma
      halpha hbeta hgamma hsigma hX
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hsigma hgap)
      hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24),
    supplied orthogonal diagonal Schur-coordinate case:
    relative Sylvester first-order perturbation bound from the concrete
    Schur-diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_relative_first_order_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_schurDiagonal_of_vecCoeff_entrywise_abs_ge n
      U A V B a b X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      hU hV hA hB halpha hbeta hgamma hsigma heps hX hgap
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.23):
    source-numbered alias for the concrete Sylvester vec/Kronecker sigma-min
    first-order bound. -/
alias H16_eq16_23_sylvester_first_order_bound_of_vecCoeff_sigmaMin :=
  sylvester_first_order_bound_of_vecCoeff_sigmaMin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.23):
    source-numbered alias for the concrete Sylvester vec/Kronecker
    left-inverse first-order bound. -/
alias H16_eq16_23_sylvester_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le :=
  sylvester_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le

/-- Higham, 2nd ed., Chapter 16.3, equation (16.24):
    source-numbered alias for the relative concrete Sylvester vec/Kronecker
    sigma-min first-order bound. -/
alias H16_eq16_24_sylvester_relative_first_order_bound_of_vecCoeff_sigmaMin :=
  sylvester_relative_first_order_bound_of_vecCoeff_sigmaMin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.24):
    source-numbered alias for the relative concrete Sylvester vec/Kronecker
    left-inverse first-order bound. -/
alias H16_eq16_24_sylvester_relative_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le :=
  sylvester_relative_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le

/-- Higham, 2nd ed., Chapter 16.3, equation (16.23), diagonal case:
    source-numbered alias for the concrete Sylvester vec/Kronecker
    entrywise-gap first-order bound. -/
alias H16_eq16_23_sylvester_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge :=
  sylvester_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.3, equation (16.24), diagonal case:
    source-numbered alias for the relative concrete Sylvester vec/Kronecker
    entrywise-gap first-order bound. -/
alias H16_eq16_24_sylvester_relative_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge :=
  sylvester_relative_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.3, equation (16.23), supplied orthogonal
    Schur-diagonal case:
    source-numbered alias for the concrete Sylvester vec/Kronecker
    entrywise-gap first-order bound. -/
alias H16_eq16_23_sylvester_first_order_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge :=
  sylvester_first_order_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.3, equation (16.24), supplied orthogonal
    Schur-diagonal case:
    source-numbered alias for the relative concrete Sylvester vec/Kronecker
    entrywise-gap first-order bound. -/
alias H16_eq16_24_sylvester_relative_first_order_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge :=
  sylvester_relative_first_order_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    Frobenius first-order Sylvester perturbation bound from a positive lower
    bound on the concrete Kronecker/vectorized Sylvester coefficient. -/
theorem sylvester_perturbation_bound_of_vecCoeff_sigmaMin (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0)) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_sigmaMin n
      A B X dA dB dC dX sigma hSigma
      (sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B sigma hCoeff)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    relative Sylvester perturbation bound from a positive lower bound on the
    concrete Kronecker/vectorized Sylvester coefficient. -/
theorem sylvester_relative_perturbation_of_vecCoeff_sigmaMin (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_of_sigmaMin n
      A B X dA dB dC dX sigma hSigma
      (sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B sigma hCoeff)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    Frobenius first-order Sylvester perturbation bound from a concrete left
    inverse and operator-2 radius for the printed vec/Kronecker coefficient. -/
theorem sylvester_perturbation_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0)) :
    frobNorm dX <=
      M * ((alpha + beta) * frobNorm X + gamma) * eps := by
  have h :=
    sylvester_perturbation_bound_of_vecCoeff_sigmaMin n
      A B X dA dB dC dX (1 / M) (one_div_pos.mpr hM)
      (sylvesterVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne
  simpa [one_div] using h

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    relative Sylvester perturbation bound from a concrete left inverse and
    operator-2 radius for the printed vec/Kronecker coefficient. -/
theorem sylvester_relative_perturbation_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma (1 / M) * eps := by
  exact
    sylvester_relative_perturbation_of_vecCoeff_sigmaMin n
      A B X dA dB dC dX (1 / M) (one_div_pos.mpr hM)
      (sylvesterVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    Frobenius first-order Sylvester perturbation bound from a finite
    Gram-eigenvalue lower bound for the concrete vectorized Sylvester
    coefficient. -/
theorem sylvester_perturbation_bound_of_vecCoeff_gram_eigenvalues (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0)) :
    frobNorm dX <=
      (1 / Real.sqrt lam) *
        ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_vecCoeff_sigmaMin n
      A B X dA dB dC dX (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (sylvesterVecCoeff_sigmaMin_of_gram_eigenvalues n A B
        (le_of_lt hLam) hEig)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    relative Sylvester perturbation bound from a finite Gram-eigenvalue lower
    bound for the concrete vectorized Sylvester coefficient. -/
theorem sylvester_relative_perturbation_of_vecCoeff_gram_eigenvalues (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma (Real.sqrt lam) * eps := by
  exact
    sylvester_relative_perturbation_of_vecCoeff_sigmaMin n
      A B X dA dB dC dX (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (sylvesterVecCoeff_sigmaMin_of_gram_eigenvalues n A B
        (le_of_lt hLam) hEig)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    total Frobenius first-order Sylvester perturbation bound from a positive
    lower bound on the concrete Kronecker/vectorized Sylvester coefficient.

    This source-facing wrapper removes the nonzero perturbation side condition
    by routing through the total `SepLowerBound` theorem. -/
theorem sylvester_perturbation_bound_of_vecCoeff_sigmaMin_total (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_sepLowerBound_total n
      A B X dA dB dC dX sigma
      (SepLowerBound_of_vecCoeff_sigmaMin n A B sigma hSigma hCoeff)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    total relative Sylvester perturbation bound from a positive lower bound on
    the concrete Kronecker/vectorized Sylvester coefficient.

    This is the total absolute vec-coefficient wrapper divided by the positive
    Frobenius norm of the exact Sylvester solution. -/
theorem sylvester_relative_perturbation_of_vecCoeff_sigmaMin_total (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_of_sepLowerBound_total n
      A B X dA dB dC dX sigma
      (SepLowerBound_of_vecCoeff_sigmaMin n A B sigma hSigma hCoeff)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    total Frobenius first-order Sylvester perturbation bound from a concrete
    left inverse and operator-2 radius for the printed vec/Kronecker
    coefficient. -/
theorem sylvester_perturbation_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
    (n : Nat) (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      M * ((alpha + beta) * frobNorm X + gamma) * eps := by
  have h :=
    sylvester_perturbation_bound_of_sepLowerBound_total n
      A B X dA dB dC dX (1 / M)
      (SepLowerBound_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin
  simpa [one_div] using h

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    total relative Sylvester perturbation bound from a concrete left inverse
    and operator-2 radius for the printed vec/Kronecker coefficient. -/
theorem sylvester_relative_perturbation_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
    (n : Nat) (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma (1 / M) * eps := by
  exact
    sylvester_relative_perturbation_of_sepLowerBound_total n
      A B X dA dB dC dX (1 / M)
      (SepLowerBound_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    total Frobenius first-order Sylvester perturbation bound from a finite
    Gram-eigenvalue lower bound for the concrete vectorized Sylvester
    coefficient. -/
theorem sylvester_perturbation_bound_of_vecCoeff_gram_eigenvalues_total (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      (1 / Real.sqrt lam) *
        ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_sepLowerBound_total n
      A B X dA dB dC dX (Real.sqrt lam)
      (SepLowerBound_of_vecCoeff_gram_eigenvalues n A B hLam hEig)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    total relative Sylvester perturbation bound from a finite Gram-eigenvalue
    lower bound for the concrete vectorized Sylvester coefficient. -/
theorem sylvester_relative_perturbation_of_vecCoeff_gram_eigenvalues_total
    (n : Nat) (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma (Real.sqrt lam) * eps := by
  exact
    sylvester_relative_perturbation_of_sepLowerBound_total n
      A B X dA dB dC dX (Real.sqrt lam)
      (SepLowerBound_of_vecCoeff_gram_eigenvalues n A B hLam hEig)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26),
    diagonal case: Frobenius first-order Sylvester perturbation bound from the
    concrete diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_perturbation_bound_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) dX i j =
        dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0)) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) (Matrix.diagonal b)
      X dA dB dC dX sigma hSigma
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma (le_of_lt hSigma) hgap)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26),
    diagonal case: relative Sylvester perturbation bound from the concrete
    diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_relative_perturbation_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) dX i j =
        dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n (Matrix.diagonal a) (Matrix.diagonal b)
        X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) (Matrix.diagonal b)
      X dA dB dC dX sigma hSigma
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma (le_of_lt hSigma) hgap)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26),
    supplied orthogonal diagonal Schur-coordinate case:
    Frobenius first-order Sylvester perturbation bound from the concrete
    Schur-diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_perturbation_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0)) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_vecCoeff_sigmaMin n
      A B X dA dB dC dX sigma hSigma
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hSigma hgap)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26),
    supplied orthogonal diagonal Schur-coordinate case:
    relative Sylvester perturbation bound from the concrete Schur-diagonal
    vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_relative_perturbation_schurDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_of_vecCoeff_sigmaMin n
      A B X dA dB dC dX sigma hSigma
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hSigma hgap)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26),
    total diagonal case: Frobenius first-order Sylvester perturbation bound from
    the concrete diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_perturbation_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) dX i j =
        dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_vecCoeff_sigmaMin_total n
      (Matrix.diagonal a) (Matrix.diagonal b)
      X dA dB dC dX sigma hSigma
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma (le_of_lt hSigma) hgap)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26),
    total diagonal case: relative Sylvester perturbation bound from the concrete
    diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_relative_perturbation_diagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) dX i j =
        dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n (Matrix.diagonal a) (Matrix.diagonal b)
        X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_of_vecCoeff_sigmaMin_total n
      (Matrix.diagonal a) (Matrix.diagonal b)
      X dA dB dC dX sigma hSigma
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma (le_of_lt hSigma) hgap)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26),
    total supplied orthogonal diagonal Schur-coordinate case:
    Frobenius first-order Sylvester perturbation bound from the concrete
    Schur-diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_perturbation_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_vecCoeff_sigmaMin_total n
      A B X dA dB dC dX sigma hSigma
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hSigma hgap)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26),
    total supplied orthogonal diagonal Schur-coordinate case:
    relative Sylvester perturbation bound from the concrete Schur-diagonal
    vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_relative_perturbation_schurDiagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_of_vecCoeff_sigmaMin_total n
      A B X dA dB dC dX sigma hSigma
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hSigma hgap)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25):
    source-numbered alias for the total Frobenius Sylvester perturbation bound
    from a positive lower bound on the concrete vectorized coefficient. -/
theorem H16_eq16_25_sylvester_perturbation_bound_of_vecCoeff_sigmaMin_total
    (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_vecCoeff_sigmaMin_total n
      A B X dA dB dC dX sigma hSigma hCoeff
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25):
    source-numbered alias for the total relative Sylvester perturbation bound
    from a positive lower bound on the concrete vectorized coefficient. -/
theorem H16_eq16_25_sylvester_relative_perturbation_of_vecCoeff_sigmaMin_total
    (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_of_vecCoeff_sigmaMin_total n
      A B X dA dB dC dX sigma hSigma hCoeff
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25):
    source-numbered alias for the total Frobenius Sylvester perturbation bound
    from a concrete left inverse of the printed vec/Kronecker coefficient. -/
theorem H16_eq16_25_sylvester_perturbation_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
    (n : Nat) (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      M * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
      n A B X dA dB dC dX M Pinv hM hLeft hPinv
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25):
    source-numbered alias for the total relative Sylvester perturbation bound
    from a concrete left inverse of the printed vec/Kronecker coefficient. -/
theorem H16_eq16_25_sylvester_relative_perturbation_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
    (n : Nat) (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma (1 / M) * eps := by
  exact
    sylvester_relative_perturbation_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
      n A B X dA dB dC dX M Pinv hM hLeft hPinv
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25):
    source-numbered alias for the total Frobenius Sylvester perturbation bound
    from a Gram-eigenvalue certificate for the concrete vectorized coefficient. -/
theorem H16_eq16_25_sylvester_perturbation_bound_of_vecCoeff_gram_eigenvalues_total
    (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      (1 / Real.sqrt lam) *
        ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_vecCoeff_gram_eigenvalues_total n
      A B X dA dB dC dX lam hLam hEig
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25):
    source-numbered alias for the total relative Sylvester perturbation bound
    from a Gram-eigenvalue certificate for the concrete vectorized coefficient. -/
theorem H16_eq16_25_sylvester_relative_perturbation_of_vecCoeff_gram_eigenvalues_total
    (n : Nat) (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma (Real.sqrt lam) * eps := by
  exact
    sylvester_relative_perturbation_of_vecCoeff_gram_eigenvalues_total n
      A B X dA dB dC dX lam hLam hEig
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25), diagonal case:
    source-numbered alias for the total Frobenius Sylvester perturbation bound
    from the diagonal concrete coefficient certificate. -/
theorem H16_eq16_25_sylvester_perturbation_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) dX i j =
        dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total
      n a b X dA dB dC dX sigma hSigma hgap
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25), diagonal case:
    source-numbered alias for the total relative Sylvester perturbation bound
    from the diagonal concrete coefficient certificate. -/
theorem H16_eq16_25_sylvester_relative_perturbation_diagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) dX i j =
        dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n (Matrix.diagonal a) (Matrix.diagonal b)
        X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_diagonal_of_vecCoeff_entrywise_abs_ge_total
      n a b X dA dB dC dX sigma hSigma hgap
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25), supplied orthogonal
    diagonal Schur-coordinate case:
    source-numbered alias for the total Frobenius Sylvester perturbation bound
    from the Schur-diagonal concrete coefficient certificate. -/
theorem H16_eq16_25_sylvester_perturbation_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge_total
      n U A V B a b X dA dB dC dX sigma hU hV hA hB hSigma hgap
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25), supplied orthogonal
    diagonal Schur-coordinate case:
    source-numbered alias for the total relative Sylvester perturbation bound
    from the Schur-diagonal concrete coefficient certificate. -/
theorem H16_eq16_25_sylvester_relative_perturbation_schurDiagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_schurDiagonal_of_vecCoeff_entrywise_abs_ge_total
      n U A V B a b X dA dB dC dX sigma hU hV hA hB hSigma hgap
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    a posteriori error-residual bound from a positive lower bound on the
    concrete Kronecker/vectorized Sylvester coefficient. -/
theorem sylvester_aposteriori_bound_of_vecCoeff_sigmaMin (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) := by
  exact
    sylvester_aposteriori_bound_of_sigmaMin n
      A B C X Xhat sigma hSigma
      (sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B sigma hCoeff)
      hExact hE_ne

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    relative a posteriori error-residual bound from a positive lower bound on
    the concrete Kronecker/vectorized Sylvester coefficient. -/
theorem sylvester_relative_aposteriori_bound_of_vecCoeff_sigmaMin (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_of_sigmaMin n
      A B C X Xhat sigma hSigma
      (sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B sigma hCoeff)
      hExact hE_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    a posteriori error-residual bound from a concrete left inverse and
    operator-2 radius for the printed vec/Kronecker coefficient. -/
theorem sylvester_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B C X Xhat : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      M * frobNorm (sylvesterResidual n A B C Xhat) := by
  have h :=
    sylvester_aposteriori_bound_of_vecCoeff_sigmaMin n
      A B C X Xhat (1 / M) (one_div_pos.mpr hM)
      (sylvesterVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hExact hE_ne
  simpa [one_div] using h

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    relative a posteriori error-residual bound from a concrete left inverse
    and operator-2 radius for the printed vec/Kronecker coefficient. -/
theorem sylvester_relative_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B C X Xhat : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      (M * frobNorm (sylvesterResidual n A B C Xhat)) / frobNorm X := by
  have h :=
    sylvester_relative_aposteriori_bound_of_vecCoeff_sigmaMin n
      A B C X Xhat (1 / M) (one_div_pos.mpr hM)
      (sylvesterVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hExact hE_ne hX_pos
  simpa [one_div] using h

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    a posteriori error-residual bound from a finite Gram-eigenvalue lower bound
    for the concrete vectorized Sylvester coefficient. -/
theorem sylvester_aposteriori_bound_of_vecCoeff_gram_eigenvalues (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / Real.sqrt lam) *
        frobNorm (sylvesterResidual n A B C Xhat) := by
  exact
    sylvester_aposteriori_bound_of_vecCoeff_sigmaMin n
      A B C X Xhat (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (sylvesterVecCoeff_sigmaMin_of_gram_eigenvalues n A B
        (le_of_lt hLam) hEig)
      hExact hE_ne

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    relative a posteriori error-residual bound from a finite Gram-eigenvalue
    lower bound for the concrete vectorized Sylvester coefficient. -/
theorem sylvester_relative_aposteriori_bound_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A B C X Xhat : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / Real.sqrt lam) *
        frobNorm (sylvesterResidual n A B C Xhat)) / frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_of_vecCoeff_sigmaMin n
      A B C X Xhat (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (sylvesterVecCoeff_sigmaMin_of_gram_eigenvalues n A B
        (le_of_lt hLam) hEig)
      hExact hE_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    total a posteriori error-residual bound from a positive lower bound on the
    concrete Kronecker/vectorized Sylvester coefficient.

    This source-facing wrapper removes the nonzero-error side condition by
    routing through the total Sylvester sigma-min theorem. -/
theorem sylvester_aposteriori_bound_of_vecCoeff_sigmaMin_total (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) := by
  exact
    sylvester_aposteriori_bound_of_sigmaMin_total n
      A B C X Xhat sigma hSigma
      (sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B sigma hCoeff)
      hExact

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    total relative a posteriori error-residual bound from a positive lower
    bound on the concrete Kronecker/vectorized Sylvester coefficient.

    This is the total absolute vec-coefficient wrapper divided by the positive
    Frobenius norm of the exact Sylvester solution. -/
theorem sylvester_relative_aposteriori_bound_of_vecCoeff_sigmaMin_total (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_of_sigmaMin_total n
      A B C X Xhat sigma hSigma
      (sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B sigma hCoeff)
      hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    total a posteriori error-residual bound from a concrete left inverse and
    operator-2 radius for the printed vec/Kronecker coefficient. -/
theorem sylvester_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
    (n : Nat) (A B C X Xhat : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      M * frobNorm (sylvesterResidual n A B C Xhat) := by
  have h :=
    sylvester_aposteriori_bound_of_vecCoeff_sigmaMin_total n
      A B C X Xhat (1 / M) (one_div_pos.mpr hM)
      (sylvesterVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hExact
  simpa [one_div] using h

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    total relative a posteriori error-residual bound from a concrete left
    inverse and operator-2 radius for the printed vec/Kronecker coefficient. -/
theorem sylvester_relative_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
    (n : Nat) (A B C X Xhat : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      (M * frobNorm (sylvesterResidual n A B C Xhat)) / frobNorm X := by
  have h :=
    sylvester_relative_aposteriori_bound_of_vecCoeff_sigmaMin_total n
      A B C X Xhat (1 / M) (one_div_pos.mpr hM)
      (sylvesterVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hExact hX_pos
  simpa [one_div] using h

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    total a posteriori error-residual bound from a finite Gram-eigenvalue lower
    bound for the concrete vectorized Sylvester coefficient. -/
theorem sylvester_aposteriori_bound_of_vecCoeff_gram_eigenvalues_total
    (n : Nat) (A B C X Xhat : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / Real.sqrt lam) *
        frobNorm (sylvesterResidual n A B C Xhat) := by
  exact
    sylvester_aposteriori_bound_of_vecCoeff_sigmaMin_total n
      A B C X Xhat (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (sylvesterVecCoeff_sigmaMin_of_gram_eigenvalues n A B
        (le_of_lt hLam) hEig)
      hExact

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    total relative a posteriori error-residual bound from a finite
    Gram-eigenvalue lower bound for the concrete vectorized Sylvester
    coefficient. -/
theorem sylvester_relative_aposteriori_bound_of_vecCoeff_gram_eigenvalues_total
    (n : Nat) (A B C X Xhat : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / Real.sqrt lam) *
        frobNorm (sylvesterResidual n A B C Xhat)) / frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_of_vecCoeff_sigmaMin_total n
      A B C X Xhat (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (sylvesterVecCoeff_sigmaMin_of_gram_eigenvalues n A B
        (le_of_lt hLam) hEig)
      hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28),
    diagonal case: a posteriori error-residual bound from the concrete diagonal
    vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a b : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) *
        frobNorm
          (sylvesterResidual n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat) := by
  exact
    sylvester_aposteriori_bound_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) (Matrix.diagonal b)
      C X Xhat sigma hSigma
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma (le_of_lt hSigma) hgap)
      hExact hE_ne

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28),
    diagonal case: relative a posteriori error-residual bound from the concrete
    diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_relative_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a b : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) *
        frobNorm
          (sylvesterResidual n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) (Matrix.diagonal b)
      C X Xhat sigma hSigma
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma (le_of_lt hSigma) hgap)
      hExact hE_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28),
    supplied orthogonal diagonal Schur-coordinate case:
    a posteriori error-residual bound from the concrete Schur-diagonal
    vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_aposteriori_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) := by
  exact
    sylvester_aposteriori_bound_of_vecCoeff_sigmaMin n
      A B C X Xhat sigma hSigma
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hSigma hgap)
      hExact hE_ne

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28),
    supplied orthogonal diagonal Schur-coordinate case:
    relative a posteriori error-residual bound from the concrete
    Schur-diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_relative_aposteriori_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_of_vecCoeff_sigmaMin n
      A B C X Xhat sigma hSigma
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hSigma hgap)
      hExact hE_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the concrete Sylvester vec/Kronecker sigma-min
    a posteriori bound, preserving the explicit nonzero-error side condition. -/
alias H16_eq16_28_sylvester_aposteriori_bound_of_vecCoeff_sigmaMin :=
  sylvester_aposteriori_bound_of_vecCoeff_sigmaMin

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the relative concrete Sylvester vec/Kronecker
    sigma-min a posteriori bound, preserving the explicit nonzero-error and
    positive-solution-norm side conditions. -/
alias H16_eq16_28_sylvester_relative_aposteriori_bound_of_vecCoeff_sigmaMin :=
  sylvester_relative_aposteriori_bound_of_vecCoeff_sigmaMin

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the concrete Sylvester vec/Kronecker left-inverse
    a posteriori bound, preserving the explicit nonzero-error side condition. -/
alias H16_eq16_28_sylvester_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le :=
  sylvester_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the relative concrete Sylvester vec/Kronecker
    left-inverse a posteriori bound, preserving the explicit nonzero-error and
    positive-solution-norm side conditions. -/
alias H16_eq16_28_sylvester_relative_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le :=
  sylvester_relative_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the concrete Sylvester vec/Kronecker finite-Gram
    a posteriori bound, preserving the explicit nonzero-error side condition. -/
alias H16_eq16_28_sylvester_aposteriori_bound_of_vecCoeff_gram_eigenvalues :=
  sylvester_aposteriori_bound_of_vecCoeff_gram_eigenvalues

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the relative concrete Sylvester vec/Kronecker
    finite-Gram a posteriori bound, preserving the explicit nonzero-error and
    positive-solution-norm side conditions. -/
alias H16_eq16_28_sylvester_relative_aposteriori_bound_of_vecCoeff_gram_eigenvalues :=
  sylvester_relative_aposteriori_bound_of_vecCoeff_gram_eigenvalues

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), diagonal case:
    source-numbered alias for the concrete Sylvester vec/Kronecker
    entrywise-gap a posteriori bound, preserving the explicit nonzero-error
    side condition. -/
alias H16_eq16_28_sylvester_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge :=
  sylvester_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), diagonal case:
    source-numbered alias for the relative concrete Sylvester vec/Kronecker
    entrywise-gap a posteriori bound, preserving the explicit nonzero-error
    and positive-solution-norm side conditions. -/
alias H16_eq16_28_sylvester_relative_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge :=
  sylvester_relative_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), supplied orthogonal
    Schur-diagonal case:
    source-numbered alias for the concrete Sylvester vec/Kronecker
    entrywise-gap a posteriori bound, preserving the explicit nonzero-error
    side condition. -/
alias H16_eq16_28_sylvester_aposteriori_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge :=
  sylvester_aposteriori_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), supplied orthogonal
    Schur-diagonal case:
    source-numbered alias for the relative concrete Sylvester vec/Kronecker
    entrywise-gap a posteriori bound, preserving the explicit nonzero-error
    and positive-solution-norm side conditions. -/
alias H16_eq16_28_sylvester_relative_aposteriori_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge :=
  sylvester_relative_aposteriori_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28),
    total diagonal case: a posteriori error-residual bound from the concrete
    diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat) (a b : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) *
        frobNorm
          (sylvesterResidual n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat) := by
  exact
    sylvester_aposteriori_bound_of_vecCoeff_sigmaMin_total n
      (Matrix.diagonal a) (Matrix.diagonal b)
      C X Xhat sigma hSigma
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma (le_of_lt hSigma) hgap)
      hExact

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28),
    total diagonal case: relative a posteriori error-residual bound from the
    concrete diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_relative_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat) (a b : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) *
        frobNorm
          (sylvesterResidual n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_of_vecCoeff_sigmaMin_total n
      (Matrix.diagonal a) (Matrix.diagonal b)
      C X Xhat sigma hSigma
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma (le_of_lt hSigma) hgap)
      hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28),
    total supplied orthogonal diagonal Schur-coordinate case:
    a posteriori error-residual bound from the concrete Schur-diagonal
    vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_aposteriori_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) := by
  exact
    sylvester_aposteriori_bound_of_vecCoeff_sigmaMin_total n
      A B C X Xhat sigma hSigma
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hSigma hgap)
      hExact

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28),
    total supplied orthogonal diagonal Schur-coordinate case:
    relative a posteriori error-residual bound from the concrete
    Schur-diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_relative_aposteriori_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_of_vecCoeff_sigmaMin_total n
      A B C X Xhat sigma hSigma
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hSigma hgap)
      hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the total Sylvester a posteriori
    error-residual bound from a positive lower bound on the concrete
    vectorized coefficient. -/
theorem H16_eq16_28_sylvester_aposteriori_bound_of_vecCoeff_sigmaMin_total
    (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) := by
  exact
    sylvester_aposteriori_bound_of_vecCoeff_sigmaMin_total n
      A B C X Xhat sigma hSigma hCoeff hExact

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the total relative Sylvester a posteriori
    error-residual bound from a positive lower bound on the concrete
    vectorized coefficient. -/
theorem H16_eq16_28_sylvester_relative_aposteriori_bound_of_vecCoeff_sigmaMin_total
    (n : Nat) (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_of_vecCoeff_sigmaMin_total n
      A B C X Xhat sigma hSigma hCoeff hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the total Sylvester a posteriori
    error-residual bound from a concrete left inverse of the printed
    vec/Kronecker coefficient. -/
theorem H16_eq16_28_sylvester_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
    (n : Nat) (A B C X Xhat : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      M * frobNorm (sylvesterResidual n A B C Xhat) := by
  exact
    sylvester_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
      n A B C X Xhat M Pinv hM hLeft hPinv hExact

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the total relative Sylvester a posteriori
    error-residual bound from a concrete left inverse of the printed
    vec/Kronecker coefficient. -/
theorem H16_eq16_28_sylvester_relative_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
    (n : Nat) (A B C X Xhat : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      (M * frobNorm (sylvesterResidual n A B C Xhat)) / frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
      n A B C X Xhat M Pinv hM hLeft hPinv hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the total Sylvester a posteriori
    error-residual bound from a Gram-eigenvalue certificate for the concrete
    vectorized coefficient. -/
theorem H16_eq16_28_sylvester_aposteriori_bound_of_vecCoeff_gram_eigenvalues_total
    (n : Nat) (A B C X Xhat : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / Real.sqrt lam) *
        frobNorm (sylvesterResidual n A B C Xhat) := by
  exact
    sylvester_aposteriori_bound_of_vecCoeff_gram_eigenvalues_total
      n A B C X Xhat lam hLam hEig hExact

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the total relative Sylvester a posteriori
    error-residual bound from a Gram-eigenvalue certificate for the concrete
    vectorized coefficient. -/
theorem H16_eq16_28_sylvester_relative_aposteriori_bound_of_vecCoeff_gram_eigenvalues_total
    (n : Nat) (A B C X Xhat : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / Real.sqrt lam) *
        frobNorm (sylvesterResidual n A B C Xhat)) / frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_of_vecCoeff_gram_eigenvalues_total
      n A B C X Xhat lam hLam hEig hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), diagonal case:
    source-numbered alias for the total Sylvester a posteriori
    error-residual bound from the diagonal concrete coefficient certificate. -/
theorem H16_eq16_28_sylvester_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat) (a b : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) *
        frobNorm
          (sylvesterResidual n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat) := by
  exact
    sylvester_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total
      n a b C X Xhat sigma hSigma hgap hExact

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), diagonal case:
    source-numbered alias for the total relative Sylvester a posteriori
    error-residual bound from the diagonal concrete coefficient certificate. -/
theorem H16_eq16_28_sylvester_relative_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat) (a b : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) *
        frobNorm
          (sylvesterResidual n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total
      n a b C X Xhat sigma hSigma hgap hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), supplied orthogonal
    diagonal Schur-coordinate case:
    source-numbered alias for the total Sylvester a posteriori error-residual
    bound from the Schur-diagonal concrete coefficient certificate. -/
theorem H16_eq16_28_sylvester_aposteriori_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) := by
  exact
    sylvester_aposteriori_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge_total
      n U A V B a b C X Xhat sigma hU hV hA hB hSigma hgap hExact

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), supplied orthogonal
    diagonal Schur-coordinate case:
    source-numbered alias for the total relative Sylvester a posteriori
    error-residual bound from the Schur-diagonal concrete coefficient
    certificate. -/
theorem H16_eq16_28_sylvester_relative_aposteriori_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge_total
      n U A V B a b C X Xhat sigma hU hV hA hB hSigma hgap hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    Lyapunov a posteriori error-residual bound from a positive lower bound on
    the concrete vectorized Lyapunov coefficient. -/
theorem lyapunov_aposteriori_bound_of_vecCoeff_sigmaMin (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (lyapunovResidual n A C Xhat) := by
  have hExactSylv :
      forall i j,
        sylvesterOp n A (fun i' j' => -matTranspose A i' j') X i j = C i j := by
    intro i j
    rw [<- lyapunovOp_eq_sylvesterOp n A X]
    exact hExact i j
  have h :=
    sylvester_aposteriori_bound n A (fun i j => -matTranspose A i j)
      C X Xhat sigma hsigma
      (SepLowerBound_lyapunov_of_vecCoeff_sigmaMin n A sigma hsigma hCoeff)
      hExactSylv hE_ne
  simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using h

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    relative Lyapunov a posteriori error-residual bound from a positive lower
    bound on the concrete vectorized Lyapunov coefficient. -/
theorem lyapunov_relative_aposteriori_bound_of_vecCoeff_sigmaMin
    (n : Nat) (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (lyapunovResidual n A C Xhat)) /
        frobNorm X := by
  have hExactSylv :
      forall i j,
        sylvesterOp n A (fun i' j' => -matTranspose A i' j') X i j = C i j := by
    intro i j
    rw [<- lyapunovOp_eq_sylvesterOp n A X]
    exact hExact i j
  have h :=
    sylvester_relative_aposteriori_bound n A (fun i j => -matTranspose A i j)
      C X Xhat sigma hsigma
      (SepLowerBound_lyapunov_of_vecCoeff_sigmaMin n A sigma hsigma hCoeff)
      hExactSylv hE_ne hX_pos
  simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using h

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    Lyapunov a posteriori error-residual bound from a concrete left inverse and
    operator-2 radius for the printed Lyapunov vec/Kronecker coefficient. -/
theorem lyapunov_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A C X Xhat : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      M * frobNorm (lyapunovResidual n A C Xhat) := by
  have hExactSylv :
      forall i j,
        sylvesterOp n A (fun i' j' => -matTranspose A i' j') X i j = C i j := by
    intro i j
    rw [<- lyapunovOp_eq_sylvesterOp n A X]
    exact hExact i j
  have h :=
    sylvester_aposteriori_bound n A (fun i j => -matTranspose A i j)
      C X Xhat (1 / M) (one_div_pos.mpr hM)
      (SepLowerBound_lyapunov_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)
      hExactSylv hE_ne
  simpa [one_div, lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using h

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    relative Lyapunov a posteriori error-residual bound from a concrete left
    inverse and operator-2 radius for the printed Lyapunov vec/Kronecker
    coefficient. -/
theorem lyapunov_relative_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A C X Xhat : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      (M * frobNorm (lyapunovResidual n A C Xhat)) / frobNorm X := by
  have hExactSylv :
      forall i j,
        sylvesterOp n A (fun i' j' => -matTranspose A i' j') X i j = C i j := by
    intro i j
    rw [<- lyapunovOp_eq_sylvesterOp n A X]
    exact hExact i j
  have h :=
    sylvester_relative_aposteriori_bound n A (fun i j => -matTranspose A i j)
      C X Xhat (1 / M) (one_div_pos.mpr hM)
      (SepLowerBound_lyapunov_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)
      hExactSylv hE_ne hX_pos
  simpa [one_div, lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using h

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    Lyapunov a posteriori error-residual bound from a finite Gram-eigenvalue
    lower bound for the concrete vectorized Lyapunov coefficient. -/
theorem lyapunov_aposteriori_bound_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A C X Xhat : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / Real.sqrt lam) * frobNorm (lyapunovResidual n A C Xhat) := by
  have hExactSylv :
      forall i j,
        sylvesterOp n A (fun i' j' => -matTranspose A i' j') X i j = C i j := by
    intro i j
    rw [<- lyapunovOp_eq_sylvesterOp n A X]
    exact hExact i j
  have h :=
    sylvester_aposteriori_bound n A (fun i j => -matTranspose A i j)
      C X Xhat (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (SepLowerBound_lyapunov_of_vecCoeff_gram_eigenvalues
        n A (le_of_lt hLam) (Real.sqrt_pos.mpr hLam) hEig)
      hExactSylv hE_ne
  simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using h

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    relative Lyapunov a posteriori error-residual bound from a finite
    Gram-eigenvalue lower bound for the concrete vectorized Lyapunov
    coefficient. -/
theorem lyapunov_relative_aposteriori_bound_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A C X Xhat : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / Real.sqrt lam) * frobNorm (lyapunovResidual n A C Xhat)) /
        frobNorm X := by
  have hExactSylv :
      forall i j,
        sylvesterOp n A (fun i' j' => -matTranspose A i' j') X i j = C i j := by
    intro i j
    rw [<- lyapunovOp_eq_sylvesterOp n A X]
    exact hExact i j
  have h :=
    sylvester_relative_aposteriori_bound n A (fun i j => -matTranspose A i j)
      C X Xhat (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (SepLowerBound_lyapunov_of_vecCoeff_gram_eigenvalues
        n A (le_of_lt hLam) (Real.sqrt_pos.mpr hLam) hEig)
      hExactSylv hE_ne hX_pos
  simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using h

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    total Lyapunov a posteriori error-residual bound from a positive lower
    bound on the concrete vectorized Lyapunov coefficient.

    This routes through the total Lyapunov sigma-min theorem. -/
theorem lyapunov_aposteriori_bound_of_vecCoeff_sigmaMin_total (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    (hExact : forall i j, lyapunovOp n A X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (lyapunovResidual n A C Xhat) := by
  exact
    lyapunov_aposteriori_bound_of_sigmaMin n
      A C X Xhat sigma hsigma
      (lyapunovOp_sigmaMin_of_vecCoeff_sigmaMin n A sigma hCoeff)
      hExact

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    total relative Lyapunov a posteriori error-residual bound from a positive
    lower bound on the concrete vectorized Lyapunov coefficient. -/
theorem lyapunov_relative_aposteriori_bound_of_vecCoeff_sigmaMin_total
    (n : Nat) (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (lyapunovResidual n A C Xhat)) /
        frobNorm X := by
  exact
    lyapunov_relative_aposteriori_bound_of_sigmaMin n
      A C X Xhat sigma hsigma
      (lyapunovOp_sigmaMin_of_vecCoeff_sigmaMin n A sigma hCoeff)
      hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    total Lyapunov a posteriori error-residual bound from a concrete left
    inverse and operator-2 radius for the printed Lyapunov vec/Kronecker
    coefficient. -/
theorem lyapunov_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
    (n : Nat) (A C X Xhat : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hExact : forall i j, lyapunovOp n A X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      M * frobNorm (lyapunovResidual n A C Xhat) := by
  have h :=
    lyapunov_aposteriori_bound_of_vecCoeff_sigmaMin_total n
      A C X Xhat (1 / M) (one_div_pos.mpr hM)
      (lyapunovVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)
      hExact
  simpa [one_div] using h

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    total relative Lyapunov a posteriori error-residual bound from a concrete
    left inverse and operator-2 radius for the printed Lyapunov vec/Kronecker
    coefficient. -/
theorem lyapunov_relative_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
    (n : Nat) (A C X Xhat : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      (M * frobNorm (lyapunovResidual n A C Xhat)) / frobNorm X := by
  have h :=
    lyapunov_relative_aposteriori_bound_of_vecCoeff_sigmaMin_total n
      A C X Xhat (1 / M) (one_div_pos.mpr hM)
      (lyapunovVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)
      hExact hX_pos
  simpa [one_div] using h

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    total Lyapunov a posteriori error-residual bound from a finite
    Gram-eigenvalue lower bound for the concrete vectorized Lyapunov
    coefficient. -/
theorem lyapunov_aposteriori_bound_of_vecCoeff_gram_eigenvalues_total
    (n : Nat) (A C X Xhat : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (hExact : forall i j, lyapunovOp n A X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / Real.sqrt lam) * frobNorm (lyapunovResidual n A C Xhat) := by
  exact
    lyapunov_aposteriori_bound_of_vecCoeff_sigmaMin_total n
      A C X Xhat (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (lyapunovVecCoeff_sigmaMin_of_gram_eigenvalues n A
        (le_of_lt hLam) hEig)
      hExact

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    total relative Lyapunov a posteriori error-residual bound from a finite
    Gram-eigenvalue lower bound for the concrete vectorized Lyapunov
    coefficient. -/
theorem lyapunov_relative_aposteriori_bound_of_vecCoeff_gram_eigenvalues_total
    (n : Nat) (A C X Xhat : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / Real.sqrt lam) * frobNorm (lyapunovResidual n A C Xhat)) /
        frobNorm X := by
  exact
    lyapunov_relative_aposteriori_bound_of_vecCoeff_sigmaMin_total n
      A C X Xhat (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (lyapunovVecCoeff_sigmaMin_of_gram_eigenvalues n A
        (le_of_lt hLam) hEig)
      hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), diagonal case:
    Lyapunov a posteriori error-residual bound from the concrete diagonal
    vec/Kronecker coefficient lower-bound certificate. -/
theorem lyapunov_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hExact : forall i j,
      lyapunovOp n (Matrix.diagonal a) X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) *
        frobNorm (lyapunovResidual n (Matrix.diagonal a) C Xhat) := by
  exact
    lyapunov_aposteriori_bound_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) C X Xhat sigma hSigma
      (lyapunovVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a sigma (le_of_lt hSigma) hgap)
      hExact hE_ne

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), diagonal case:
    relative Lyapunov a posteriori error-residual bound from the concrete
    diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem lyapunov_relative_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hExact : forall i j,
      lyapunovOp n (Matrix.diagonal a) X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) *
        frobNorm (lyapunovResidual n (Matrix.diagonal a) C Xhat)) /
        frobNorm X := by
  exact
    lyapunov_relative_aposteriori_bound_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) C X Xhat sigma hSigma
      (lyapunovVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a sigma (le_of_lt hSigma) hgap)
      hExact hE_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), supplied orthogonal
    spectral-coordinate case:
    Lyapunov a posteriori error-residual bound from the concrete
    spectral-diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem lyapunov_aposteriori_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (lyapunovResidual n A C Xhat) := by
  exact
    lyapunov_aposteriori_bound_of_vecCoeff_sigmaMin n
      A C X Xhat sigma hSigma
      (lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A a sigma hU hA hSigma hgap)
      hExact hE_ne

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), supplied orthogonal
    spectral-coordinate case:
    relative Lyapunov a posteriori error-residual bound from the concrete
    spectral-diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem lyapunov_relative_aposteriori_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (lyapunovResidual n A C Xhat)) /
        frobNorm X := by
  exact
    lyapunov_relative_aposteriori_bound_of_vecCoeff_sigmaMin n
      A C X Xhat sigma hSigma
      (lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A a sigma hU hA hSigma hgap)
      hExact hE_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the concrete Lyapunov vec/Kronecker sigma-min
    a posteriori bound, preserving the explicit nonzero-error side condition. -/
alias H16_eq16_28_lyapunov_aposteriori_bound_of_vecCoeff_sigmaMin :=
  lyapunov_aposteriori_bound_of_vecCoeff_sigmaMin

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the relative concrete Lyapunov vec/Kronecker
    sigma-min a posteriori bound, preserving the explicit nonzero-error and
    positive-solution-norm side conditions. -/
alias H16_eq16_28_lyapunov_relative_aposteriori_bound_of_vecCoeff_sigmaMin :=
  lyapunov_relative_aposteriori_bound_of_vecCoeff_sigmaMin

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the concrete Lyapunov vec/Kronecker left-inverse
    a posteriori bound, preserving the explicit nonzero-error side condition. -/
alias H16_eq16_28_lyapunov_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le :=
  lyapunov_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the relative concrete Lyapunov vec/Kronecker
    left-inverse a posteriori bound, preserving the explicit nonzero-error and
    positive-solution-norm side conditions. -/
alias H16_eq16_28_lyapunov_relative_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le :=
  lyapunov_relative_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the concrete Lyapunov vec/Kronecker finite-Gram
    a posteriori bound, preserving the explicit nonzero-error side condition. -/
alias H16_eq16_28_lyapunov_aposteriori_bound_of_vecCoeff_gram_eigenvalues :=
  lyapunov_aposteriori_bound_of_vecCoeff_gram_eigenvalues

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the relative concrete Lyapunov vec/Kronecker
    finite-Gram a posteriori bound, preserving the explicit nonzero-error and
    positive-solution-norm side conditions. -/
alias H16_eq16_28_lyapunov_relative_aposteriori_bound_of_vecCoeff_gram_eigenvalues :=
  lyapunov_relative_aposteriori_bound_of_vecCoeff_gram_eigenvalues

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), diagonal case:
    source-numbered alias for the concrete Lyapunov vec/Kronecker
    entrywise-gap a posteriori bound, preserving the explicit nonzero-error
    side condition. -/
alias H16_eq16_28_lyapunov_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge :=
  lyapunov_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), diagonal case:
    source-numbered alias for the relative concrete Lyapunov vec/Kronecker
    entrywise-gap a posteriori bound, preserving the explicit nonzero-error
    and positive-solution-norm side conditions. -/
alias H16_eq16_28_lyapunov_relative_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge :=
  lyapunov_relative_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), supplied orthogonal
    spectral-coordinate case:
    source-numbered alias for the concrete Lyapunov vec/Kronecker
    entrywise-gap a posteriori bound, preserving the explicit nonzero-error
    side condition. -/
alias H16_eq16_28_lyapunov_aposteriori_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge :=
  lyapunov_aposteriori_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), supplied orthogonal
    spectral-coordinate case:
    source-numbered alias for the relative concrete Lyapunov vec/Kronecker
    entrywise-gap a posteriori bound, preserving the explicit nonzero-error
    and positive-solution-norm side conditions. -/
alias H16_eq16_28_lyapunov_relative_aposteriori_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge :=
  lyapunov_relative_aposteriori_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), total diagonal case:
    Lyapunov a posteriori error-residual bound from the concrete diagonal
    vec/Kronecker coefficient lower-bound certificate. -/
theorem lyapunov_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat) (a : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hExact : forall i j,
      lyapunovOp n (Matrix.diagonal a) X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) *
        frobNorm (lyapunovResidual n (Matrix.diagonal a) C Xhat) := by
  exact
    lyapunov_aposteriori_bound_of_vecCoeff_sigmaMin_total n
      (Matrix.diagonal a) C X Xhat sigma hSigma
      (lyapunovVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a sigma (le_of_lt hSigma) hgap)
      hExact

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), total diagonal case:
    relative Lyapunov a posteriori error-residual bound from the concrete
    diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem lyapunov_relative_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat) (a : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hExact : forall i j,
      lyapunovOp n (Matrix.diagonal a) X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) *
        frobNorm (lyapunovResidual n (Matrix.diagonal a) C Xhat)) /
        frobNorm X := by
  exact
    lyapunov_relative_aposteriori_bound_of_vecCoeff_sigmaMin_total n
      (Matrix.diagonal a) C X Xhat sigma hSigma
      (lyapunovVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a sigma (le_of_lt hSigma) hgap)
      hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), total supplied orthogonal
    spectral-coordinate case:
    Lyapunov a posteriori error-residual bound from the concrete
    spectral-diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem lyapunov_aposteriori_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hExact : forall i j, lyapunovOp n A X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (lyapunovResidual n A C Xhat) := by
  exact
    lyapunov_aposteriori_bound_of_vecCoeff_sigmaMin_total n
      A C X Xhat sigma hSigma
      (lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A a sigma hU hA hSigma hgap)
      hExact

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28), total supplied orthogonal
    spectral-coordinate case:
    relative Lyapunov a posteriori error-residual bound from the concrete
    spectral-diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem lyapunov_relative_aposteriori_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (lyapunovResidual n A C Xhat)) /
        frobNorm X := by
  exact
    lyapunov_relative_aposteriori_bound_of_vecCoeff_sigmaMin_total n
      A C X Xhat sigma hSigma
      (lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A a sigma hU hA hSigma hgap)
      hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28): source-numbered
    alias for the total concrete Lyapunov coefficient sigma-min a posteriori
    error-residual endpoint. -/
alias H16_eq16_28_lyapunov_aposteriori_bound_of_vecCoeff_sigmaMin_total :=
  lyapunov_aposteriori_bound_of_vecCoeff_sigmaMin_total

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28): source-numbered
    alias for the total relative concrete Lyapunov coefficient sigma-min
    a posteriori error-residual endpoint. -/
alias H16_eq16_28_lyapunov_relative_aposteriori_bound_of_vecCoeff_sigmaMin_total :=
  lyapunov_relative_aposteriori_bound_of_vecCoeff_sigmaMin_total

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28): source-numbered
    alias for the total concrete-left-inverse Lyapunov a posteriori
    error-residual endpoint. -/
alias H16_eq16_28_lyapunov_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total :=
  lyapunov_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28): source-numbered
    alias for the total relative concrete-left-inverse Lyapunov a posteriori
    error-residual endpoint. -/
alias H16_eq16_28_lyapunov_relative_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total :=
  lyapunov_relative_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28): source-numbered
    alias for the total finite-Gram Lyapunov a posteriori error-residual
    endpoint. -/
alias H16_eq16_28_lyapunov_aposteriori_bound_of_vecCoeff_gram_eigenvalues_total :=
  lyapunov_aposteriori_bound_of_vecCoeff_gram_eigenvalues_total

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28): source-numbered
    alias for the total relative finite-Gram Lyapunov a posteriori
    error-residual endpoint. -/
alias H16_eq16_28_lyapunov_relative_aposteriori_bound_of_vecCoeff_gram_eigenvalues_total :=
  lyapunov_relative_aposteriori_bound_of_vecCoeff_gram_eigenvalues_total

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28): source-numbered
    alias for the total diagonal concrete-coefficient Lyapunov a posteriori
    error-residual endpoint. -/
alias H16_eq16_28_lyapunov_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total :=
  lyapunov_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28): source-numbered
    alias for the total relative diagonal concrete-coefficient Lyapunov
    a posteriori error-residual endpoint. -/
alias H16_eq16_28_lyapunov_relative_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total :=
  lyapunov_relative_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28): source-numbered
    alias for the total supplied spectral-coordinate Lyapunov a posteriori
    error-residual endpoint. -/
alias H16_eq16_28_lyapunov_aposteriori_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge_total :=
  lyapunov_aposteriori_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge_total

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28): source-numbered
    alias for the total relative supplied spectral-coordinate Lyapunov
    a posteriori error-residual endpoint. -/
alias H16_eq16_28_lyapunov_relative_aposteriori_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge_total :=
  lyapunov_relative_aposteriori_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge_total

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    the Lyapunov condition-number certificate follows from a positive lower
    bound on the printed vectorized Lyapunov coefficient. -/
theorem lyapunovCond_of_vecCoeff_sigmaMin_isLyapunovConditionFirstOrderBound
    (n : Nat) (A X : Fin n -> Fin n -> Real) (alpha gamma sigma : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma) (hsigma : 0 < sigma)
    (hX : 0 < frobNorm X)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x)) :
    LyapunovConditionFirstOrderBound n A X alpha gamma
      (lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma)) := by
  exact
    lyapunovCond_of_sigmaMin_isLyapunovConditionFirstOrderBound n
      A X alpha gamma sigma halpha hgamma hsigma hX
      (lyapunovOp_sigmaMin_of_vecCoeff_sigmaMin n A sigma hCoeff)

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    a finite Gram-eigenvalue lower bound for the printed Lyapunov vec/Kronecker
    coefficient instantiates the Lyapunov condition certificate with
    inverse-operator constant `1 / sqrt(lam)`. -/
theorem lyapunovCond_of_vecCoeff_gram_eigenvalues_isLyapunovConditionFirstOrderBound
    (n : Nat) (A X : Fin n -> Fin n -> Real) (alpha gamma lam : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma) (hlam : 0 < lam)
    (hX : 0 < frobNorm X)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p) :
    LyapunovConditionFirstOrderBound n A X alpha gamma
      (lyapunovCond_of_inverseOpBound n X alpha gamma
        (1 / Real.sqrt lam)) := by
  exact
    lyapunovCond_of_vecCoeff_sigmaMin_isLyapunovConditionFirstOrderBound
      n A X alpha gamma (Real.sqrt lam)
      halpha hgamma (Real.sqrt_pos.mpr hlam) hX
      (lyapunovVecCoeff_sigmaMin_of_gram_eigenvalues n A
        (le_of_lt hlam) hEig)

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    a concrete left inverse and operator-2 radius for the printed Lyapunov
    vec/Kronecker coefficient instantiates the Lyapunov condition certificate
    directly, without first postulating a sigma-min lower bound. -/
theorem lyapunovCond_of_vecCoeff_left_inverse_finiteOpNorm2Le_isLyapunovConditionFirstOrderBound
    (n : Nat) (A X : Fin n -> Fin n -> Real) (alpha gamma M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hM : 0 <= M) (hX : 0 < frobNorm X)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    LyapunovConditionFirstOrderBound n A X alpha gamma
      (lyapunovCond_of_inverseOpBound n X alpha gamma M) := by
  exact
    lyapunovCond_of_inverseOpBound_isLyapunovConditionFirstOrderBound n
      A X alpha gamma M halpha hgamma hM hX
      (lyapunovInverseOpBound_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A Pinv hLeft hPinv)

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-shaped Lyapunov first-order perturbation bound from a positive lower
    bound on the concrete vectorized Lyapunov coefficient. -/
theorem H16_eq16_27_lyapunov_condition_of_vecCoeff_sigmaMin (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_sigmaMin n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX
      (lyapunovOp_sigmaMin_of_vecCoeff_sigmaMin n A sigma hCoeff)
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    Frobenius first-order Lyapunov perturbation bound from a positive lower
    bound on the concrete vectorized Lyapunov coefficient. -/
theorem lyapunov_first_order_bound_of_vecCoeff_sigmaMin (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (hX : 0 < frobNorm X)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX <=
      lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) *
        frobNorm X *
        lyapunovScaledPerturbationPairNorm n DeltaA DeltaC alpha gamma := by
  exact
    (lyapunovCond_of_vecCoeff_sigmaMin_isLyapunovConditionFirstOrderBound
      n A X alpha gamma sigma halpha hgamma hsigma hX hCoeff)
      DeltaA DeltaC DeltaX hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    relative Lyapunov first-order perturbation bound from a positive lower
    bound on the concrete vectorized Lyapunov coefficient. -/
theorem lyapunov_relative_first_order_bound_of_vecCoeff_sigmaMin
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_vecCoeff_sigmaMin n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX hCoeff
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    Frobenius Lyapunov perturbation bound from a positive lower bound on the
    concrete vectorized Lyapunov coefficient. -/
theorem lyapunov_perturbation_bound_of_vecCoeff_sigmaMin (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hDeltaX_ne : Not (frobNormSq DeltaX = 0)) :
    frobNorm DeltaX <=
      (1 / sigma) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound n A X DeltaA DeltaC DeltaX
      sigma hsigma
      (SepLowerBound_lyapunov_of_vecCoeff_sigmaMin n A sigma hsigma hCoeff)
      alpha gamma eps halpha hgamma heps
      hDeltaA hDeltaC hLin hDeltaX_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    relative Lyapunov perturbation bound from a positive lower bound on the
    concrete vectorized Lyapunov coefficient. -/
theorem lyapunov_relative_perturbation_of_vecCoeff_sigmaMin
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hDeltaX_ne : Not (frobNormSq DeltaX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma sigma * eps := by
  have hDeltaB :
      frobNorm (fun i j => -matTranspose DeltaA i j) <= eps * alpha := by
    rw [show (fun i j => -matTranspose DeltaA i j) =
        (fun i j => -(matTranspose DeltaA) i j) from by ext i j; rfl]
    rw [frobNorm_neg, frobNorm_transpose]
    exact hDeltaA
  exact
    sylvester_relative_perturbation n A
      (fun i j => -matTranspose A i j) X DeltaA
      (fun i j => -matTranspose DeltaA i j) DeltaC DeltaX
      sigma hsigma
      (SepLowerBound_lyapunov_of_vecCoeff_sigmaMin n A sigma hsigma hCoeff)
      alpha alpha gamma eps halpha halpha hgamma heps
      hDeltaA hDeltaB hDeltaC hLin hDeltaX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    Frobenius first-order Lyapunov perturbation bound from a concrete left
    inverse and operator-2 radius for the printed Lyapunov vec/Kronecker
    coefficient. -/
theorem lyapunov_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hM : 0 <= M) (hX : 0 < frobNorm X)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX <=
      lyapunovCond_of_inverseOpBound n X alpha gamma M * frobNorm X *
        lyapunovScaledPerturbationPairNorm n DeltaA DeltaC alpha gamma := by
  exact
    (lyapunovCond_of_vecCoeff_left_inverse_finiteOpNorm2Le_isLyapunovConditionFirstOrderBound
      n A X alpha gamma M Pinv halpha hgamma hM hX hLeft hPinv)
      DeltaA DeltaC DeltaX hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    relative Lyapunov first-order perturbation bound from a concrete left
    inverse and operator-2 radius for the printed Lyapunov vec/Kronecker
    coefficient. -/
theorem lyapunov_relative_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma M eps : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hM : 0 <= M) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma M * eps := by
  have hCond :=
    lyapunovCond_of_vecCoeff_left_inverse_finiteOpNorm2Le_isLyapunovConditionFirstOrderBound
      n A X alpha gamma M Pinv halpha hgamma hM hX hLeft hPinv
  have hCond_nonneg :
      0 <= lyapunovCond_of_inverseOpBound n X alpha gamma M := by
    unfold lyapunovCond_of_inverseOpBound
    have htwo_alpha : 0 <= 2 * alpha :=
      mul_nonneg (by norm_num) (le_of_lt halpha)
    have hprod : 0 <= 2 * alpha * frobNorm X :=
      mul_nonneg htwo_alpha (le_of_lt hX)
    have hnum : 0 <= 2 * alpha * frobNorm X + gamma :=
      add_nonneg hprod (le_of_lt hgamma)
    exact div_nonneg (mul_nonneg hM hnum) (le_of_lt hX)
  exact
    lyapunov_relative_first_order_bound_of_condition n
      A X DeltaA DeltaC DeltaX alpha gamma
      (lyapunovCond_of_inverseOpBound n X alpha gamma M) eps
      hCond hX hCond_nonneg halpha hgamma heps
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    Frobenius first-order Lyapunov perturbation bound from a finite
    Gram-eigenvalue lower bound for the concrete vectorized Lyapunov
    coefficient. -/
theorem lyapunov_first_order_bound_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma lam : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hlam : 0 < lam) (hX : 0 < frobNorm X)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX <=
      lyapunovCond_of_inverseOpBound n X alpha gamma
        (1 / Real.sqrt lam) * frobNorm X *
        lyapunovScaledPerturbationPairNorm n DeltaA DeltaC alpha gamma := by
  exact
    (lyapunovCond_of_vecCoeff_gram_eigenvalues_isLyapunovConditionFirstOrderBound
      n A X alpha gamma lam halpha hgamma hlam hX hEig)
      DeltaA DeltaC DeltaX hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    relative Lyapunov first-order perturbation bound from a finite
    Gram-eigenvalue lower bound for the concrete vectorized Lyapunov
    coefficient. -/
theorem lyapunov_relative_first_order_bound_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma lam eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hlam : 0 < lam) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma
          (1 / Real.sqrt lam) * eps := by
  have hCond :=
    lyapunovCond_of_vecCoeff_gram_eigenvalues_isLyapunovConditionFirstOrderBound
      n A X alpha gamma lam halpha hgamma hlam hX hEig
  have hCond_nonneg :
      0 <= lyapunovCond_of_inverseOpBound n X alpha gamma
        (1 / Real.sqrt lam) := by
    unfold lyapunovCond_of_inverseOpBound
    have hM : 0 <= (1 : Real) / Real.sqrt lam := by
      exact div_nonneg zero_le_one (Real.sqrt_nonneg lam)
    have htwo_alpha : 0 <= 2 * alpha :=
      mul_nonneg (by norm_num) (le_of_lt halpha)
    have hprod : 0 <= 2 * alpha * frobNorm X :=
      mul_nonneg htwo_alpha (le_of_lt hX)
    have hnum : 0 <= 2 * alpha * frobNorm X + gamma :=
      add_nonneg hprod (le_of_lt hgamma)
    exact div_nonneg (mul_nonneg hM hnum) (le_of_lt hX)
  exact
    lyapunov_relative_first_order_bound_of_condition n
      A X DeltaA DeltaC DeltaX alpha gamma
      (lyapunovCond_of_inverseOpBound n X alpha gamma
        (1 / Real.sqrt lam)) eps
      hCond hX hCond_nonneg halpha hgamma heps
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the concrete Lyapunov vec/Kronecker sigma-min
    first-order bound. -/
alias H16_eq16_27_lyapunov_first_order_bound_of_vecCoeff_sigmaMin :=
  lyapunov_first_order_bound_of_vecCoeff_sigmaMin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the relative concrete Lyapunov vec/Kronecker
    sigma-min first-order bound. -/
alias H16_eq16_27_lyapunov_relative_first_order_bound_of_vecCoeff_sigmaMin :=
  lyapunov_relative_first_order_bound_of_vecCoeff_sigmaMin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the concrete Lyapunov vec/Kronecker left-inverse
    first-order bound. -/
alias H16_eq16_27_lyapunov_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le :=
  lyapunov_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the relative concrete Lyapunov vec/Kronecker
    left-inverse first-order bound. -/
alias H16_eq16_27_lyapunov_relative_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le :=
  lyapunov_relative_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered aliases for finite Gram-eigenvalue Lyapunov
    first-order condition wrappers. -/
alias H16_eq16_27_lyapunov_first_order_bound_of_vecCoeff_gram_eigenvalues :=
  lyapunov_first_order_bound_of_vecCoeff_gram_eigenvalues

alias H16_eq16_27_lyapunov_relative_first_order_bound_of_vecCoeff_gram_eigenvalues :=
  lyapunov_relative_first_order_bound_of_vecCoeff_gram_eigenvalues

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-shaped Lyapunov first-order perturbation bound from a concrete
    left inverse and operator-2 radius for the printed Lyapunov
    vec/Kronecker coefficient. -/
theorem H16_eq16_27_lyapunov_condition_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma M eps : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hM : 0 <= M) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma M * eps := by
  exact
    lyapunov_relative_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
      n A X DeltaA DeltaC DeltaX alpha gamma M eps Pinv
      halpha hgamma hM heps hX hLeft hPinv
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    Frobenius Lyapunov perturbation bound from a concrete left inverse and
    operator-2 radius for the printed Lyapunov vec/Kronecker coefficient. -/
theorem lyapunov_perturbation_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hDeltaX_ne : Not (frobNormSq DeltaX = 0)) :
    frobNorm DeltaX <=
      M * (2 * alpha * frobNorm X + gamma) * eps := by
  have h :=
    lyapunov_perturbation_bound n A X DeltaA DeltaC DeltaX
      (1 / M) (one_div_pos.mpr hM)
      (SepLowerBound_lyapunov_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)
      alpha gamma eps halpha hgamma heps
      hDeltaA hDeltaC hLin hDeltaX_ne
  simpa [one_div] using h

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    relative Lyapunov perturbation bound from a concrete left inverse and
    operator-2 radius for the printed Lyapunov vec/Kronecker coefficient. -/
theorem lyapunov_relative_perturbation_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hDeltaX_ne : Not (frobNormSq DeltaX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma (1 / M) * eps := by
  have hDeltaB : frobNorm (fun i j => -matTranspose DeltaA i j) <= eps * alpha := by
    rw [show (fun i j => -matTranspose DeltaA i j) =
        (fun i j => -(matTranspose DeltaA) i j) from by ext i j; rfl]
    rw [frobNorm_neg, frobNorm_transpose]
    exact hDeltaA
  exact
    sylvester_relative_perturbation n A
      (fun i j => -matTranspose A i j) X DeltaA
      (fun i j => -matTranspose DeltaA i j) DeltaC DeltaX
      (1 / M) (one_div_pos.mpr hM)
      (SepLowerBound_lyapunov_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)
      alpha alpha gamma eps halpha halpha hgamma heps
      hDeltaA hDeltaB hDeltaC hLin hDeltaX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    Frobenius Lyapunov perturbation bound from a supplied finite
    Gram-eigenvalue lower bound for the concrete Lyapunov vec/Kronecker
    coefficient. -/
theorem lyapunov_perturbation_bound_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hDeltaX_ne : Not (frobNormSq DeltaX = 0)) :
    frobNorm DeltaX <=
      (1 / Real.sqrt lam) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound n A X DeltaA DeltaC DeltaX
      (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (SepLowerBound_lyapunov_of_vecCoeff_gram_eigenvalues
        n A (le_of_lt hLam) (Real.sqrt_pos.mpr hLam) hEig)
      alpha gamma eps halpha hgamma heps
      hDeltaA hDeltaC hLin hDeltaX_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    relative Lyapunov perturbation bound from a supplied finite
    Gram-eigenvalue lower bound for the concrete Lyapunov vec/Kronecker
    coefficient. -/
theorem lyapunov_relative_perturbation_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hDeltaX_ne : Not (frobNormSq DeltaX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma (Real.sqrt lam) * eps := by
  have hDeltaB : frobNorm (fun i j => -matTranspose DeltaA i j) <= eps * alpha := by
    rw [show (fun i j => -matTranspose DeltaA i j) =
        (fun i j => -(matTranspose DeltaA) i j) from by ext i j; rfl]
    rw [frobNorm_neg, frobNorm_transpose]
    exact hDeltaA
  exact
    sylvester_relative_perturbation n A
      (fun i j => -matTranspose A i j) X DeltaA
      (fun i j => -matTranspose DeltaA i j) DeltaC DeltaX
      (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (SepLowerBound_lyapunov_of_vecCoeff_gram_eigenvalues
        n A (le_of_lt hLam) (Real.sqrt_pos.mpr hLam) hEig)
      alpha alpha gamma eps halpha halpha hgamma heps
      hDeltaA hDeltaB hDeltaC hLin hDeltaX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    total Frobenius Lyapunov perturbation bound from a positive lower bound on
    the concrete vectorized Lyapunov coefficient.

    This source-facing wrapper removes the nonzero perturbation side condition
    by routing through the total Lyapunov `SepLowerBound` theorem. -/
theorem lyapunov_perturbation_bound_of_vecCoeff_sigmaMin_total (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j) :
    frobNorm DeltaX <=
      (1 / sigma) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound_of_sepLowerBound_total n
      A X DeltaA DeltaC DeltaX sigma hsigma
      (SepLowerBound_lyapunov_of_vecCoeff_sigmaMin
        n A sigma hsigma hCoeff)
      alpha gamma eps halpha hgamma heps
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    total relative Lyapunov perturbation bound from a positive lower bound on
    the concrete vectorized Lyapunov coefficient.

    This is the total absolute vec-coefficient wrapper divided by the positive
    Frobenius norm of the exact Lyapunov solution. -/
theorem lyapunov_relative_perturbation_of_vecCoeff_sigmaMin_total
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma sigma * eps := by
  exact
    lyapunov_relative_perturbation_of_sepLowerBound_total n
      A X DeltaA DeltaC DeltaX sigma hsigma
      (SepLowerBound_lyapunov_of_vecCoeff_sigmaMin
        n A sigma hsigma hCoeff)
      alpha gamma eps halpha hgamma heps
      hDeltaA hDeltaC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    total Frobenius Lyapunov perturbation bound from a concrete left inverse
    and operator-2 radius for the printed Lyapunov vec/Kronecker coefficient. -/
theorem lyapunov_perturbation_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j) :
    frobNorm DeltaX <=
      M * (2 * alpha * frobNorm X + gamma) * eps := by
  have h :=
    lyapunov_perturbation_bound_of_sepLowerBound_total n
      A X DeltaA DeltaC DeltaX (1 / M) (one_div_pos.mpr hM)
      (SepLowerBound_lyapunov_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)
      alpha gamma eps halpha hgamma heps
      hDeltaA hDeltaC hLin
  simpa [one_div] using h

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    total relative Lyapunov perturbation bound from a concrete left inverse
    and operator-2 radius for the printed Lyapunov vec/Kronecker coefficient. -/
theorem lyapunov_relative_perturbation_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma (1 / M) * eps := by
  exact
    lyapunov_relative_perturbation_of_sepLowerBound_total n
      A X DeltaA DeltaC DeltaX (1 / M) (one_div_pos.mpr hM)
      (SepLowerBound_lyapunov_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)
      alpha gamma eps halpha hgamma heps
      hDeltaA hDeltaC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    total Frobenius Lyapunov perturbation bound from a supplied finite
    Gram-eigenvalue lower bound for the concrete Lyapunov vec/Kronecker
    coefficient. -/
theorem lyapunov_perturbation_bound_of_vecCoeff_gram_eigenvalues_total
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j) :
    frobNorm DeltaX <=
      (1 / Real.sqrt lam) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound_of_sepLowerBound_total n
      A X DeltaA DeltaC DeltaX (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (SepLowerBound_lyapunov_of_vecCoeff_gram_eigenvalues
        n A (le_of_lt hLam) (Real.sqrt_pos.mpr hLam) hEig)
      alpha gamma eps halpha hgamma heps
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    total relative Lyapunov perturbation bound from a supplied finite
    Gram-eigenvalue lower bound for the concrete Lyapunov vec/Kronecker
    coefficient. -/
theorem lyapunov_relative_perturbation_of_vecCoeff_gram_eigenvalues_total
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma (Real.sqrt lam) * eps := by
  exact
    lyapunov_relative_perturbation_of_sepLowerBound_total n
      A X DeltaA DeltaC DeltaX (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (SepLowerBound_lyapunov_of_vecCoeff_gram_eigenvalues
        n A (le_of_lt hLam) (Real.sqrt_pos.mpr hLam) hEig)
      alpha gamma eps halpha hgamma heps
      hDeltaA hDeltaC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total Lyapunov perturbation endpoint from a
    concrete vec-coefficient sigma-min lower bound. -/
alias H16_eq16_27_lyapunov_perturbation_bound_of_vecCoeff_sigmaMin_total :=
  lyapunov_perturbation_bound_of_vecCoeff_sigmaMin_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total relative Lyapunov perturbation endpoint
    from a concrete vec-coefficient sigma-min lower bound. -/
alias H16_eq16_27_lyapunov_relative_perturbation_of_vecCoeff_sigmaMin_total :=
  lyapunov_relative_perturbation_of_vecCoeff_sigmaMin_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total Lyapunov perturbation endpoint from a
    concrete left inverse and finite operator-2 bound. -/
alias H16_eq16_27_lyapunov_perturbation_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total :=
  lyapunov_perturbation_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total relative Lyapunov perturbation endpoint
    from a concrete left inverse and finite operator-2 bound. -/
alias H16_eq16_27_lyapunov_relative_perturbation_of_vecCoeff_left_inverse_finiteOpNorm2Le_total :=
  lyapunov_relative_perturbation_of_vecCoeff_left_inverse_finiteOpNorm2Le_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total Lyapunov perturbation endpoint from a
    finite Gram-eigenvalue lower-bound certificate. -/
alias H16_eq16_27_lyapunov_perturbation_bound_of_vecCoeff_gram_eigenvalues_total :=
  lyapunov_perturbation_bound_of_vecCoeff_gram_eigenvalues_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total relative Lyapunov perturbation endpoint
    from a finite Gram-eigenvalue lower-bound certificate. -/
alias H16_eq16_27_lyapunov_relative_perturbation_of_vecCoeff_gram_eigenvalues_total :=
  lyapunov_relative_perturbation_of_vecCoeff_gram_eigenvalues_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27),
    total diagonal case: Frobenius Lyapunov perturbation bound from the concrete
    diagonal Lyapunov vec/Kronecker coefficient lower-bound certificate. -/
theorem lyapunov_perturbation_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a)
          (fun i' j' => -matTranspose (Matrix.diagonal a) i' j')
          DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j) :
    frobNorm DeltaX <=
      (1 / sigma) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound_of_vecCoeff_sigmaMin_total n
      (Matrix.diagonal a) X DeltaA DeltaC DeltaX sigma hsigma
      (lyapunovVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a sigma (le_of_lt hsigma) hgap)
      alpha gamma eps halpha hgamma heps
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27),
    total diagonal case: relative Lyapunov perturbation bound from the concrete
    diagonal Lyapunov vec/Kronecker coefficient lower-bound certificate. -/
theorem lyapunov_relative_perturbation_diagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a)
          (fun i' j' => -matTranspose (Matrix.diagonal a) i' j')
          DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n (Matrix.diagonal a)
        (fun i j => -matTranspose (Matrix.diagonal a) i j)
        X alpha alpha gamma sigma * eps := by
  exact
    lyapunov_relative_perturbation_of_vecCoeff_sigmaMin_total n
      (Matrix.diagonal a) X DeltaA DeltaC DeltaX sigma hsigma
      (lyapunovVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a sigma (le_of_lt hsigma) hgap)
      alpha gamma eps halpha hgamma heps
      hDeltaA hDeltaC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total diagonal Lyapunov perturbation endpoint
    from concrete pair-sum gap data. -/
alias H16_eq16_27_lyapunov_perturbation_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total :=
  lyapunov_perturbation_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total relative diagonal Lyapunov perturbation
    endpoint from concrete pair-sum gap data. -/
alias H16_eq16_27_lyapunov_relative_perturbation_diagonal_of_vecCoeff_entrywise_abs_ge_total :=
  lyapunov_relative_perturbation_diagonal_of_vecCoeff_entrywise_abs_ge_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27),
    total supplied orthogonal spectral-coordinate case:
    Frobenius Lyapunov perturbation bound from the concrete spectral-diagonal
    Lyapunov vec/Kronecker coefficient lower-bound certificate. -/
theorem lyapunov_perturbation_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j) :
    frobNorm DeltaX <=
      (1 / sigma) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound_of_vecCoeff_sigmaMin_total n
      A X DeltaA DeltaC DeltaX sigma hsigma
      (lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      alpha gamma eps halpha hgamma heps
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27),
    total supplied orthogonal spectral-coordinate case:
    relative Lyapunov perturbation bound from the concrete spectral-diagonal
    Lyapunov vec/Kronecker coefficient lower-bound certificate. -/
theorem lyapunov_relative_perturbation_spectralDiagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma sigma * eps := by
  exact
    lyapunov_relative_perturbation_of_vecCoeff_sigmaMin_total n
      A X DeltaA DeltaC DeltaX sigma hsigma
      (lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      alpha gamma eps halpha hgamma heps
      hDeltaA hDeltaC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total supplied spectral-coordinate
    Lyapunov perturbation endpoint. -/
alias H16_eq16_27_lyapunov_perturbation_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge_total :=
  lyapunov_perturbation_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total relative supplied spectral-coordinate
    Lyapunov perturbation endpoint. -/
alias H16_eq16_27_lyapunov_relative_perturbation_spectralDiagonal_of_vecCoeff_entrywise_abs_ge_total :=
  lyapunov_relative_perturbation_spectralDiagonal_of_vecCoeff_entrywise_abs_ge_total

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-shaped Lyapunov first-order perturbation bound from a finite
    Gram-eigenvalue lower bound for the concrete vectorized Lyapunov
    coefficient. -/
theorem H16_eq16_27_lyapunov_condition_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma lam eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hlam : 0 < lam) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma
          (1 / Real.sqrt lam) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_vecCoeff_sigmaMin n
      A X DeltaA DeltaC DeltaX alpha gamma (Real.sqrt lam) eps
      halpha hgamma (Real.sqrt_pos.mpr hlam) heps hX
      (lyapunovVecCoeff_sigmaMin_of_gram_eigenvalues n A
        (le_of_lt hlam) hEig)
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    source-shaped Lyapunov first-order perturbation bound from the concrete
    diagonal Lyapunov vec/Kronecker coefficient lower-bound certificate. -/
theorem H16_eq16_27_lyapunov_condition_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n (Matrix.diagonal a) DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX
      (lyapunovVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a sigma (le_of_lt hsigma) hgap)
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    source-shaped Lyapunov first-order perturbation bound from the concrete
    spectral-diagonal Lyapunov vec/Kronecker coefficient lower-bound
    certificate. -/
theorem H16_eq16_27_lyapunov_condition_spectralDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_vecCoeff_sigmaMin n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX
      (lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    Frobenius first-order Lyapunov perturbation bound from the concrete
    diagonal Lyapunov vec/Kronecker coefficient lower-bound certificate. -/
theorem lyapunov_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hLin : forall i j,
      lyapunovOp n (Matrix.diagonal a) DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX <=
      lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) *
        frobNorm X *
        lyapunovScaledPerturbationPairNorm n DeltaA DeltaC alpha gamma := by
  exact
    (lyapunovCond_of_vecCoeff_sigmaMin_isLyapunovConditionFirstOrderBound
      n (Matrix.diagonal a) X alpha gamma sigma
      halpha hgamma hsigma hX
      (lyapunovVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a sigma (le_of_lt hsigma) hgap))
      DeltaA DeltaC DeltaX hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    relative Lyapunov first-order perturbation bound from the concrete
    diagonal Lyapunov vec/Kronecker coefficient lower-bound certificate. -/
theorem lyapunov_relative_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n (Matrix.diagonal a) DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_diagonal_of_vecCoeff_entrywise_abs_ge n
      a X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX hgap
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    Frobenius first-order Lyapunov perturbation bound from the concrete
    spectral-diagonal Lyapunov vec/Kronecker coefficient lower-bound
    certificate. -/
theorem lyapunov_first_order_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX <=
      lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) *
        frobNorm X *
        lyapunovScaledPerturbationPairNorm n DeltaA DeltaC alpha gamma := by
  exact
    (lyapunovCond_of_vecCoeff_sigmaMin_isLyapunovConditionFirstOrderBound
      n A X alpha gamma sigma halpha hgamma hsigma hX
      (lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap))
      DeltaA DeltaC DeltaX hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    relative Lyapunov first-order perturbation bound from the concrete
    spectral-diagonal Lyapunov vec/Kronecker coefficient lower-bound
    certificate. -/
theorem lyapunov_relative_first_order_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_spectralDiagonal_of_vecCoeff_entrywise_abs_ge n
      U A a X DeltaA DeltaC DeltaX alpha gamma sigma eps
      hU hA halpha hgamma hsigma heps hX hgap
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    source-numbered alias for the concrete Lyapunov vec/Kronecker
    entrywise-gap first-order bound. -/
alias H16_eq16_27_lyapunov_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge :=
  lyapunov_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    source-numbered alias for the relative concrete Lyapunov vec/Kronecker
    entrywise-gap first-order bound. -/
alias H16_eq16_27_lyapunov_relative_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge :=
  lyapunov_relative_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    source-numbered alias for the concrete Lyapunov vec/Kronecker
    entrywise-gap first-order bound. -/
alias H16_eq16_27_lyapunov_first_order_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge :=
  lyapunov_first_order_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    source-numbered alias for the relative concrete Lyapunov vec/Kronecker
    entrywise-gap first-order bound. -/
alias H16_eq16_27_lyapunov_relative_first_order_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge :=
  lyapunov_relative_first_order_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    source-shaped Lyapunov first-order perturbation bound from the
    spectral-coordinate `sep(A,-A^T)` lower-bound certificate. -/
theorem H16_eq16_27_lyapunov_condition_spectralDiagonal_of_sep_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_sepLowerBound n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX
      (SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      hDeltaA hDeltaC hLin

end NumStability
