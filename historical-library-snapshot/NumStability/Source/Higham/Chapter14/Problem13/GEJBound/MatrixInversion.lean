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
import NumStability.Source.Higham.Chapter14.Problem11.HadamardCondition.MatrixInversion

/-!
# Chapter14 Problem13 GEJBound MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    finite AM-GM in the product form used by Appendix A.  For nonnegative
    `z_i`, `prod_i z_i <= ((sum_i z_i)/n)^n`. -/
theorem higham14_problem14_13_amgm_prod_le_pow_sum_div_card {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (∏ i : Fin n, z i) ≤ ((∑ i : Fin n, z i) / (n : ℝ)) ^ n := by
  let S : ℝ := ∑ i : Fin n, z i
  by_cases hS : S = 0
  · have hz_zero : ∀ i, z i = 0 := by
      have hsum_zero : ∑ i : Fin n, z i = 0 := by simpa [S] using hS
      have hterms := (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin n))) (f := z)
        (by intro i _; exact hz i)).mp hsum_zero
      intro i
      exact hterms i (Finset.mem_univ i)
    have hprod_zero : ∏ i : Fin n, z i = 0 := by
      let i : Fin n := ⟨0, hn⟩
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (hz_zero i)]
    have hsum_zero : ∑ i : Fin n, z i = 0 := by simpa [S] using hS
    rw [hprod_zero, hsum_zero]
    exact pow_nonneg (div_nonneg le_rfl (Nat.cast_nonneg n)) n
  · have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      exact Finset.sum_nonneg (fun i _ => hz i)
    have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS)
    let y : Fin n → ℝ := fun i => (n : ℝ) / S * z i
    have hy_nonneg : ∀ i, 0 ≤ y i := by
      intro i
      exact mul_nonneg (div_nonneg (Nat.cast_nonneg n) hS_nonneg) (hz i)
    have hy_sum : ∑ i : Fin n, y i = n := by
      dsimp [y]
      rw [← Finset.mul_sum]
      change ((n : ℝ) / S) * S = (n : ℝ)
      field_simp [hS]
    have hy_prod_le_one : ∏ i : Fin n, y i ≤ 1 :=
      geomMean_prod_le_one_of_sum_eq_card hn y hy_nonneg hy_sum
    have hy_prod :
        ∏ i : Fin n, y i = ((n : ℝ) / S) ^ n * ∏ i : Fin n, z i := by
      dsimp [y]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    have hscale_pos : 0 < (S / (n : ℝ)) ^ n :=
      pow_pos (div_pos hS_pos (Nat.cast_pos.mpr hn)) n
    have hmain :
        ((n : ℝ) / S) ^ n * ∏ i : Fin n, z i ≤ 1 := by
      rwa [← hy_prod]
    have hmul := mul_le_mul_of_nonneg_left hmain hscale_pos.le
    have hcancel :
        (S / (n : ℝ)) ^ n * (((n : ℝ) / S) ^ n * ∏ i : Fin n, z i) =
          ∏ i : Fin n, z i := by
      have hfac : (S / (n : ℝ)) * ((n : ℝ) / S) = 1 := by
        field_simp [hS, Nat.cast_ne_zero.mpr hn.ne']
      calc
        (S / (n : ℝ)) ^ n * (((n : ℝ) / S) ^ n * ∏ i : Fin n, z i)
            = ((S / (n : ℝ)) ^ n * ((n : ℝ) / S) ^ n) *
                ∏ i : Fin n, z i := by ring
        _ = (((S / (n : ℝ)) * ((n : ℝ) / S)) ^ n) *
                ∏ i : Fin n, z i := by rw [mul_pow]
        _ = ∏ i : Fin n, z i := by rw [hfac]; simp
    have hrhs :
        (S / (n : ℝ)) ^ n * 1 = (S / (n : ℝ)) ^ n := by ring
    simpa [S] using (by rwa [hcancel, hrhs] at hmul)

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    the Appendix A AM-GM algebra in squared form.  The family `z` represents
    the `n` numbers whose geometric mean is
    `(kappa * |det(A)| / 2)^(2/n)` in the source proof. -/
theorem higham14_problem14_13_gej_squared_bound_from_amgm {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i)
    {p frob : ℝ}
    (hprod : (∏ i : Fin n, z i) = p ^ 2)
    (hsum_lt : (∑ i : Fin n, z i) < frob ^ 2) :
    p ^ 2 < (frob ^ 2 / (n : ℝ)) ^ n := by
  have hprod_le :=
    higham14_problem14_13_amgm_prod_le_pow_sum_div_card hn z hz
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, z i :=
    Finset.sum_nonneg (fun i _ => hz i)
  have hdiv_lt :
      (∑ i : Fin n, z i) / (n : ℝ) < frob ^ 2 / (n : ℝ) :=
    div_lt_div_of_pos_right hsum_lt (Nat.cast_pos.mpr hn)
  have hdiv_nonneg : 0 ≤ (∑ i : Fin n, z i) / (n : ℝ) :=
    div_nonneg hsum_nonneg (Nat.cast_nonneg n)
  have hpow_lt :
      ((∑ i : Fin n, z i) / (n : ℝ)) ^ n <
        (frob ^ 2 / (n : ℝ)) ^ n :=
    pow_lt_pow_left₀ hdiv_lt hdiv_nonneg hn.ne'
  calc
    p ^ 2 = ∏ i : Fin n, z i := hprod.symm
    _ ≤ ((∑ i : Fin n, z i) / (n : ℝ)) ^ n := hprod_le
    _ < (frob ^ 2 / (n : ℝ)) ^ n := hpow_lt

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    convert the squared GEJ AM-GM conclusion to the printed inequality shape
    `kappa < 2/|det(A)| * (||A||_F/sqrt(n))^n`. -/
theorem higham14_problem14_13_gej_bound_from_squared
    {n : ℕ} (hn : 0 < n) {kappa detAbs frob : ℝ}
    (hdet_pos : 0 < detAbs)
    (hkappa_nonneg : 0 ≤ kappa)
    (hfrob_nonneg : 0 ≤ frob)
    (hsq :
      (kappa * detAbs / 2) ^ 2 < (frob ^ 2 / (n : ℝ)) ^ n) :
    kappa < (2 / detAbs) * (frob / Real.sqrt (n : ℝ)) ^ n := by
  have hnR_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsqrtn_pos : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.mpr hnR_pos
  have hbase_nonneg : 0 ≤ frob / Real.sqrt (n : ℝ) :=
    div_nonneg hfrob_nonneg hsqrtn_pos.le
  have hrhs_nonneg : 0 ≤ (frob / Real.sqrt (n : ℝ)) ^ n :=
    pow_nonneg hbase_nonneg n
  have hp_nonneg : 0 ≤ kappa * detAbs / 2 := by
    positivity
  have hrhs_sq :
      ((frob / Real.sqrt (n : ℝ)) ^ n) ^ 2 =
        (frob ^ 2 / (n : ℝ)) ^ n := by
    calc
      ((frob / Real.sqrt (n : ℝ)) ^ n) ^ 2
          = ((frob / Real.sqrt (n : ℝ)) ^ 2) ^ n := by
              rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = (frob ^ 2 / (n : ℝ)) ^ n := by
              rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hp_lt :
      kappa * detAbs / 2 < (frob / Real.sqrt (n : ℝ)) ^ n :=
    (sq_lt_sq₀ hp_nonneg hrhs_nonneg).mp (by
      simpa [hrhs_sq] using hsq)
  have hscale_pos : 0 < 2 / detAbs := div_pos (by norm_num) hdet_pos
  have hmul := mul_lt_mul_of_pos_left hp_lt hscale_pos
  have hleft : (2 / detAbs) * (kappa * detAbs / 2) = kappa := by
    field_simp [hdet_pos.ne']
  rwa [hleft] at hmul

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    source-shaped AM-GM certificate theorem.  Supplying the singular-value
    product certificate and the strict Frobenius-sum comparison yields the GEJ
    determinant/condition inequality. -/
theorem higham14_problem14_13_gej_bound_from_amgm_certificate
    {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ)
    {kappa detAbs frob : ℝ}
    (hdet_pos : 0 < detAbs)
    (hkappa_nonneg : 0 ≤ kappa)
    (hfrob_nonneg : 0 ≤ frob)
    (hz : ∀ i, 0 ≤ z i)
    (hprod : (∏ i : Fin n, z i) = (kappa * detAbs / 2) ^ 2)
    (hsum_lt : (∑ i : Fin n, z i) < frob ^ 2) :
    kappa < (2 / detAbs) * (frob / Real.sqrt (n : ℝ)) ^ n :=
  higham14_problem14_13_gej_bound_from_squared hn hdet_pos hkappa_nonneg
    hfrob_nonneg
    (higham14_problem14_13_gej_squared_bound_from_amgm hn z hz hprod hsum_lt)

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    the repository's exact real operator `2`-norm agrees with the operator
    norm of the complexified real matrix. -/
theorem higham14_problem14_13_opNorm2_eq_complexMatrixOp2_realRectToCMatrix
    {n : ℕ} (A : Fin n → Fin n → ℝ) :
    opNorm2 A = complexMatrixOp2 (realRectToCMatrix A) := by
  apply le_antisymm
  · exact opNorm2_le_of_opNorm2Le A
      (complexMatrixOp2_nonneg (realRectToCMatrix A))
      (opNorm2Le_complexMatrixOp2_realRectToCMatrix A)
  · exact complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le A
      (opNorm2_nonneg A) (opNorm2Le_opNorm2 A)

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    the real operator `2`-norm is the largest ordered singular value of the
    complexified real matrix. -/
theorem higham14_problem14_13_opNorm2_eq_complex_top_singularValue
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ) :
    opNorm2 A =
      complexMatrixSingularValue (realRectToCMatrix A) ⟨0, hn⟩ := by
  rw [higham14_problem14_13_opNorm2_eq_complexMatrixOp2_realRectToCMatrix A]
  exact complexMatrixOp2_eq_top_singularValue hn (realRectToCMatrix A)

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    the real Frobenius square agrees with the Frobenius square of the
    complexified real matrix. -/
theorem higham14_problem14_13_frobNorm_sq_eq_complexMatrixFrobeniusSq
    {n : ℕ} (A : Fin n → Fin n → ℝ) :
    frobNorm A ^ 2 = complexMatrixFrobeniusSq (realRectToCMatrix A) := by
  rw [frobNorm_sq]
  unfold frobNormSq complexMatrixFrobeniusSq realRectToCMatrix
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [complexNorm_ofReal_eq_abs, sq_abs]

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    the Frobenius square of a real matrix is the sum of the squared ordered
    singular values of its complexification. -/
theorem higham14_problem14_13_frobNorm_sq_eq_sum_complex_singularValue_sq
    {n : ℕ} (A : Fin n → Fin n → ℝ) :
    frobNorm A ^ 2 =
      ∑ i : Fin n, complexMatrixSingularValue (realRectToCMatrix A) i ^ 2 := by
  rw [higham14_problem14_13_frobNorm_sq_eq_complexMatrixFrobeniusSq A]
  exact complexMatrixFrobeniusSq_eq_sum_singularValue_sq (realRectToCMatrix A)

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    the Euclidean lower norm of a real `(k+1) x (k+1)` matrix equals its last
    ordered singular value after complexification. -/
theorem higham14_problem14_13_lowerNorm_eq_complex_last_singularValue
    {k : ℕ} (A : Fin (k + 1) → Fin (k + 1) → ℝ) :
    matMulVecLowerNorm2 (Nat.succ_pos k) A =
      complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) := by
  let sigma : ℝ := complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k)
  have hsigma_nonneg : 0 ≤ sigma := by
    simpa [sigma] using
      complexMatrixSingularValue_nonneg (realRectToCMatrix A) (Fin.last k)
  apply le_antisymm
  · obtain ⟨x, hx_ne, hx_eq⟩ :=
      realRectToCMatrix_last_singularValue_exists_real_attaining_vector_sq A
    have hx_norm_ne : vecNorm2 x ≠ 0 := by
      intro hx_zero
      apply hx_ne
      funext i
      exact (vecNorm2_eq_zero_iff x).mp hx_zero i
    have hx_norm_pos : 0 < vecNorm2 x :=
      lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hx_norm_ne)
    let y : Fin (k + 1) → ℝ := fun i => (vecNorm2 x)⁻¹ * x i
    have hy_unit : vecNorm2 y = 1 :=
      vecNorm2_inv_smul_self_of_pos x hx_norm_pos
    have hAy_sq : vecNorm2 (matMulVec (k + 1) A y) ^ 2 = sigma ^ 2 := by
      have hAx_sq : vecNorm2 (matMulVec (k + 1) A x) ^ 2 =
          sigma ^ 2 * vecNorm2 x ^ 2 := by
        rw [vecNorm2_sq, vecNorm2_sq]
        simpa [sigma, matMulVec, rectMatMulVec] using hx_eq
      have hAy_eq : matMulVec (k + 1) A y =
          fun i => (vecNorm2 x)⁻¹ * matMulVec (k + 1) A x i := by
        simpa [y] using matMulVec_const_mul_right (k + 1) A (vecNorm2 x)⁻¹ x
      calc
        vecNorm2 (matMulVec (k + 1) A y) ^ 2
            = ((vecNorm2 x)⁻¹ * vecNorm2 (matMulVec (k + 1) A x)) ^ 2 := by
                rw [hAy_eq, vecNorm2_smul, abs_of_pos (inv_pos.mpr hx_norm_pos)]
        _ = (vecNorm2 x)⁻¹ ^ 2 * vecNorm2 (matMulVec (k + 1) A x) ^ 2 := by
                ring
        _ = (vecNorm2 x)⁻¹ ^ 2 * (sigma ^ 2 * vecNorm2 x ^ 2) := by
                rw [hAx_sq]
        _ = sigma ^ 2 := by
                field_simp [hx_norm_ne]
    have hAy_norm : vecNorm2 (matMulVec (k + 1) A y) = sigma := by
      exact (sq_eq_sq₀ (vecNorm2_nonneg _) hsigma_nonneg).mp hAy_sq
    calc
      matMulVecLowerNorm2 (Nat.succ_pos k) A
          ≤ vecNorm2 (matMulVec (k + 1) A y) :=
            matMulVecLowerNorm2_le (Nat.succ_pos k) A y hy_unit
      _ = sigma := hAy_norm
  · obtain ⟨y, hy_unit, hy_eq⟩ :=
      matMulVecLowerNorm2_attained (Nat.succ_pos k) A
    have hlower :=
      complexMatrixSingularValue_last_mul_norm_le_norm_euclideanLin
        (realRectToCMatrix A) (realVecToEuclidean y)
    have hsigma_le : sigma ≤ vecNorm2 (matMulVec (k + 1) A y) := by
      simpa [sigma, realVecToEuclidean_norm,
        realRectToCMatrix_euclideanLin_realVecToEuclidean_norm, hy_unit,
        matMulVec, rectMatMulVec] using hlower
    rwa [← hy_eq] at hsigma_le

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    a certified right inverse has operator norm equal to the reciprocal of the
    last ordered singular value of the original matrix. -/
theorem higham14_problem14_13_opNorm2_rightInverse_eq_inv_complex_last_singularValue
    {k : ℕ} (A Ainv : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv) :
    opNorm2 Ainv =
      (complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k))⁻¹ := by
  have hlower :=
    matMulVecLowerNorm2_eq_inv_opNorm2_of_isRightInverse
      (Nat.succ_pos k) A Ainv hRight
  have hlast :=
    higham14_problem14_13_lowerNorm_eq_complex_last_singularValue A
  have hinv :
      (opNorm2 Ainv)⁻¹ =
        complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) := by
    rw [← hlower]
    exact hlast
  calc
    opNorm2 Ainv = ((opNorm2 Ainv)⁻¹)⁻¹ := by rw [inv_inv]
    _ = (complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k))⁻¹ := by
          rw [hinv]

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    for a supplied right inverse, `kappa2` is `sigma_1 / sigma_n` in the
    ordered singular values of the complexified real matrix. -/
theorem higham14_problem14_13_kappa2_eq_top_div_last_singularValue_of_rightInverse
    {k : ℕ} (A Ainv : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv) :
    kappa2 A Ainv =
      complexMatrixSingularValue (realRectToCMatrix A) ⟨0, Nat.succ_pos k⟩ /
        complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) := by
  rw [kappa2,
    higham14_problem14_13_opNorm2_eq_complex_top_singularValue (Nat.succ_pos k) A,
    higham14_problem14_13_opNorm2_rightInverse_eq_inv_complex_last_singularValue
      A Ainv hRight,
    div_eq_mul_inv]

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    determinant of the complex Gram linear map as the product of its ordered
    Gram eigenvalues. -/
theorem higham14_problem14_13_complexGramLin_det_eq_prod_gramEigenvalues
    {n : ℕ} (A : CMatrix n n) :
    LinearMap.det (complexMatrixGramLin A) =
      ∏ i : Fin n, (complexMatrixGramEigenvalues A i : ℂ) := by
  let ob := complexMatrixGramEigenvectorBasis A
  let b := ob.toBasis
  have hmat : LinearMap.toMatrix b b (complexMatrixGramLin A) =
      Matrix.diagonal (fun i : Fin n => (complexMatrixGramEigenvalues A i : ℂ)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have happ := complexMatrixGramLin_apply_eigenvectorBasis A j
    change b.repr ((complexMatrixGramLin A) (b j)) i =
      Matrix.diagonal (fun i : Fin n => (complexMatrixGramEigenvalues A i : ℂ)) i j
    have hb_j : b j = complexMatrixGramEigenvectorBasis A j := by rfl
    rw [hb_j, happ]
    rw [OrthonormalBasis.coe_toBasis_repr_apply]
    rw [map_smul, OrthonormalBasis.repr_self]
    by_cases hji : j = i
    · subst i
      rw [WithLp.ofLp_smul, Pi.smul_apply, EuclideanSpace.single_apply]
      simp
    · have hij : i ≠ j := fun h => hji h.symm
      rw [WithLp.ofLp_smul, Pi.smul_apply, EuclideanSpace.single_apply]
      simp [Matrix.diagonal, hij]
  rw [← LinearMap.det_toMatrix b (complexMatrixGramLin A), hmat,
    Matrix.det_diagonal]

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    determinant of `Aᴴ A` is the product of squared ordered singular values. -/
theorem higham14_problem14_13_complex_det_conjTranspose_mul_self_eq_prod_singularValue_sq
    {n : ℕ} (A : CMatrix n n) :
    Matrix.det ((complexCMatrixAsMatrix A).conjTranspose * complexCMatrixAsMatrix A) =
      ∏ i : Fin n, ((complexMatrixSingularValue A i : ℂ) ^ 2) := by
  have hdet_toMatrix := LinearMap.det_toMatrix (complexEuclideanBasisFin n)
    (complexMatrixGramLin A)
  rw [complexMatrixGramLin_toMatrix] at hdet_toMatrix
  calc
    Matrix.det ((complexCMatrixAsMatrix A).conjTranspose * complexCMatrixAsMatrix A)
        = LinearMap.det (complexMatrixGramLin A) := hdet_toMatrix
    _ = ∏ i : Fin n, (complexMatrixGramEigenvalues A i : ℂ) :=
        higham14_problem14_13_complexGramLin_det_eq_prod_gramEigenvalues A
    _ = ∏ i : Fin n, ((complexMatrixSingularValue A i : ℂ) ^ 2) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [← Complex.ofReal_pow, complexMatrixSingularValue_sq]

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    square of a real determinant as the product of squared ordered singular
    values of the complexified real matrix. -/
theorem higham14_problem14_13_real_det_sq_eq_prod_complex_singularValue_sq
    {n : ℕ} (A : Fin n → Fin n → ℝ) :
    (Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) ^ 2 =
      ∏ i : Fin n, complexMatrixSingularValue (realRectToCMatrix A) i ^ 2 := by
  let C : CMatrix n n := realRectToCMatrix A
  have hdetC : Matrix.det (complexCMatrixAsMatrix C) =
      ((Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) : ℝ) : ℂ) := by
    dsimp [C]
    symm
    exact RingHom.map_det (algebraMap ℝ ℂ)
      (A : Matrix (Fin n) (Fin n) ℝ)
  have hleft :
      Matrix.det ((complexCMatrixAsMatrix C).conjTranspose * complexCMatrixAsMatrix C) =
        (((Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose, hdetC]
    simp [pow_two]
  have h :=
    higham14_problem14_13_complex_det_conjTranspose_mul_self_eq_prod_singularValue_sq C
  rw [hleft] at h
  apply Complex.ofReal_injective
  calc
    (((Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) ^ 2 : ℝ) : ℂ)
        = ∏ i : Fin n,
            ((complexMatrixSingularValue (realRectToCMatrix A) i : ℂ) ^ 2) := by
            simpa [C] using h
    _ = ((∏ i : Fin n,
            complexMatrixSingularValue (realRectToCMatrix A) i ^ 2 : ℝ) : ℂ) := by
        calc
          (∏ i : Fin n,
              ((complexMatrixSingularValue (realRectToCMatrix A) i : ℂ) ^ 2))
              = ∏ i : Fin n,
                  ((complexMatrixSingularValue (realRectToCMatrix A) i ^ 2 : ℝ) : ℂ) := by
                apply Finset.prod_congr rfl
                intro i _
                rw [Complex.ofReal_pow]
          _ = ((∏ i : Fin n,
                  complexMatrixSingularValue (realRectToCMatrix A) i ^ 2 : ℝ) : ℂ) :=
                (Complex.ofReal_prod Finset.univ
                  (fun i : Fin n =>
                    complexMatrixSingularValue (realRectToCMatrix A) i ^ 2)).symm

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    absolute value of a real determinant as the product of ordered singular
    values of the complexified real matrix. -/
theorem higham14_problem14_13_abs_det_eq_prod_complex_singularValue
    {n : ℕ} (A : Fin n → Fin n → ℝ) :
    |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
      ∏ i : Fin n, complexMatrixSingularValue (realRectToCMatrix A) i := by
  apply (sq_eq_sq₀ (abs_nonneg _) (Finset.prod_nonneg
    (fun i _ => complexMatrixSingularValue_nonneg (realRectToCMatrix A) i))).mp
  rw [sq_abs]
  rw [← Finset.prod_pow Finset.univ 2
    (fun i : Fin n => complexMatrixSingularValue (realRectToCMatrix A) i)]
  exact higham14_problem14_13_real_det_sq_eq_prod_complex_singularValue_sq A

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    a supplied right inverse makes the determinant strictly nonzero in
    absolute value. -/
theorem higham14_problem14_13_abs_det_pos_of_isRightInverse
    {n : ℕ} (A Ainv : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n A Ainv) :
    0 < |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| := by
  let AM : Matrix (Fin n) (Fin n) ℝ := A
  let AinvM : Matrix (Fin n) (Fin n) ℝ := Ainv
  have hmat :
      AM * AinvM = 1 := by
    ext i j
    simpa [AM, AinvM, Matrix.mul_apply] using hRight i j
  have hdet_prod : Matrix.det AM * Matrix.det AinvM = 1 := by
    calc
      Matrix.det AM * Matrix.det AinvM = Matrix.det (AM * AinvM) := by
        rw [Matrix.det_mul]
      _ = Matrix.det (1 : Matrix (Fin n) (Fin n) ℝ) := by
        rw [hmat]
      _ = 1 := Matrix.det_one
  have hdet_ne : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
    intro hzero
    have hzeroAM : Matrix.det AM = 0 := by
      simpa [AM] using hzero
    rw [hzeroAM, zero_mul] at hdet_prod
    norm_num at hdet_prod
  exact abs_pos.mpr hdet_ne

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    matrix-shaped AM-GM certificate wrapper for the GEJ bound.  This removes
    the scalar positivity hypotheses from
    `higham14_problem14_13_gej_bound_from_amgm_certificate` when a right
    inverse is supplied. -/
theorem higham14_problem14_13_gej_bound_from_matrix_amgm_certificate
    {n : ℕ} (hn : 0 < n) (A Ainv : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hRight : IsRightInverse n A Ainv)
    (hz : ∀ i, 0 ≤ z i)
    (hprod :
      (∏ i : Fin n, z i) =
        (kappa2 A Ainv *
          |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| / 2) ^ 2)
    (hsum_lt : (∑ i : Fin n, z i) < frobNorm A ^ 2) :
    kappa2 A Ainv <
      (2 / |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)|) *
        (frobNorm A / Real.sqrt (n : ℝ)) ^ n := by
  exact
    higham14_problem14_13_gej_bound_from_amgm_certificate hn z
      (higham14_problem14_13_abs_det_pos_of_isRightInverse A Ainv hRight)
      (mul_nonneg (opNorm2_nonneg A) (opNorm2_nonneg Ainv))
      (frobNorm_nonneg A)
      hz hprod hsum_lt

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 / equation (14.37):
    the source AM-GM family for dimensions `k + 2`.  Its entries are
    `sigma_1^2/2`, `sigma_1^2/2`, and then `sigma_2^2, ..., sigma_{n-1}^2`,
    using zero-based ordered singular-value indices. -/
noncomputable def higham14_problem14_13_gejAmgmFamily
    {k : ℕ} (A : Fin (k + 2) → Fin (k + 2) → ℝ) :
    Fin (k + 2) → ℝ :=
  let sigma := fun i : Fin (k + 2) =>
    complexMatrixSingularValue (realRectToCMatrix A) i
  Fin.cons (sigma 0 ^ 2 / 2)
    (Fin.cons (sigma 0 ^ 2 / 2)
      (fun i : Fin k => sigma i.castSucc.succ ^ 2))

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    the source GEJ AM-GM family is nonnegative. -/
theorem higham14_problem14_13_gejAmgmFamily_nonneg
    {k : ℕ} (A : Fin (k + 2) → Fin (k + 2) → ℝ) :
    ∀ i, 0 ≤ higham14_problem14_13_gejAmgmFamily A i := by
  intro i
  refine Fin.cases ?h0 ?hs i
  · simp [higham14_problem14_13_gejAmgmFamily]
    positivity
  · intro j
    refine Fin.cases ?h1 ?ht j
    · simp [higham14_problem14_13_gejAmgmFamily]
      positivity
    · intro t
      simp [higham14_problem14_13_gejAmgmFamily]
      positivity

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    a supplied right inverse makes the last ordered singular value positive. -/
theorem higham14_problem14_13_last_singularValue_pos_of_isRightInverse
    {k : ℕ} (A Ainv : Fin (k + 2) → Fin (k + 2) → ℝ)
    (hRight : IsRightInverse (k + 2) A Ainv) :
    0 <
      complexMatrixSingularValue (realRectToCMatrix A) (Fin.last (k + 1)) := by
  let sigma := fun i : Fin (k + 2) =>
    complexMatrixSingularValue (realRectToCMatrix A) i
  have hdet_pos :=
    higham14_problem14_13_abs_det_pos_of_isRightInverse A Ainv hRight
  have hprod_pos : 0 < ∏ i : Fin (k + 2), sigma i := by
    rwa [higham14_problem14_13_abs_det_eq_prod_complex_singularValue A] at hdet_pos
  have hprod_ne : (∏ i : Fin (k + 2), sigma i) ≠ 0 := ne_of_gt hprod_pos
  have hlast_ne : sigma (Fin.last (k + 1)) ≠ 0 := by
    exact (Finset.prod_ne_zero_iff.mp hprod_ne)
      (Fin.last (k + 1)) (Finset.mem_univ _)
  exact lt_of_le_of_ne
    (complexMatrixSingularValue_nonneg (realRectToCMatrix A) (Fin.last (k + 1)))
    (Ne.symm hlast_ne)

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    product certificate for the source GEJ AM-GM family. -/
theorem higham14_problem14_13_gejAmgmFamily_prod
    {k : ℕ} (A Ainv : Fin (k + 2) → Fin (k + 2) → ℝ)
    (hRight : IsRightInverse (k + 2) A Ainv) :
    (∏ i : Fin (k + 2), higham14_problem14_13_gejAmgmFamily A i) =
      (kappa2 A Ainv *
        |Matrix.det (A : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ)| / 2) ^ 2 := by
  let sigma := fun i : Fin (k + 2) =>
    complexMatrixSingularValue (realRectToCMatrix A) i
  let midProd : ℝ := ∏ i : Fin k, sigma i.castSucc.succ
  have hlast_pos :=
    higham14_problem14_13_last_singularValue_pos_of_isRightInverse A Ainv hRight
  have hlast_ne : sigma (Fin.last (k + 1)) ≠ 0 := ne_of_gt hlast_pos
  have hmid_sq :
      (∏ i : Fin k, sigma i.castSucc.succ ^ 2) = midProd ^ 2 := by
    dsimp [midProd]
    rw [← Finset.prod_pow]
  have hprodz :
      (∏ i : Fin (k + 2), higham14_problem14_13_gejAmgmFamily A i) =
        (sigma 0 ^ 2 * midProd / 2) ^ 2 := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp [higham14_problem14_13_gejAmgmFamily, sigma, hmid_sq]
    ring
  have hprefixprod :
      (∏ i : Fin (k + 1), sigma (Fin.castSucc i)) = sigma 0 * midProd := by
    rw [Fin.prod_univ_succ]
    simp [midProd]
  have hprod_all :
      (∏ i : Fin (k + 2), sigma i) =
        (sigma 0 * midProd) * sigma (Fin.last (k + 1)) := by
    rw [Fin.prod_univ_castSucc]
    rw [hprefixprod]
  have hdet :
      |Matrix.det (A : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ)| =
        (sigma 0 * midProd) * sigma (Fin.last (k + 1)) := by
    rw [higham14_problem14_13_abs_det_eq_prod_complex_singularValue A]
    exact hprod_all
  have hkappa :=
    higham14_problem14_13_kappa2_eq_top_div_last_singularValue_of_rightInverse
      A Ainv hRight
  calc
    (∏ i : Fin (k + 2), higham14_problem14_13_gejAmgmFamily A i)
        = (sigma 0 ^ 2 * midProd / 2) ^ 2 := hprodz
    _ = (kappa2 A Ainv *
          |Matrix.det (A : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ)| / 2) ^ 2 := by
        rw [hkappa, hdet]
        dsimp [sigma]
        field_simp [hlast_ne]

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    the source GEJ AM-GM sum misses exactly the positive last singular-value
    square from the Frobenius-square sum. -/
theorem higham14_problem14_13_gejAmgmFamily_sum_add_last_singularValue_sq
    {k : ℕ} (A : Fin (k + 2) → Fin (k + 2) → ℝ) :
    (∑ i : Fin (k + 2), higham14_problem14_13_gejAmgmFamily A i) +
        complexMatrixSingularValue (realRectToCMatrix A) (Fin.last (k + 1)) ^ 2 =
      frobNorm A ^ 2 := by
  let sigma := fun i : Fin (k + 2) =>
    complexMatrixSingularValue (realRectToCMatrix A) i
  have hsumz :
      (∑ i : Fin (k + 2), higham14_problem14_13_gejAmgmFamily A i) =
        sigma 0 ^ 2 + ∑ i : Fin k, sigma i.castSucc.succ ^ 2 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp [higham14_problem14_13_gejAmgmFamily, sigma]
    ring
  have hprefix :
      (∑ i : Fin (k + 1), sigma (Fin.castSucc i) ^ 2) =
        sigma 0 ^ 2 + ∑ i : Fin k, sigma i.castSucc.succ ^ 2 := by
    rw [Fin.sum_univ_succ]
    simp [sigma]
  calc
    (∑ i : Fin (k + 2), higham14_problem14_13_gejAmgmFamily A i) +
        sigma (Fin.last (k + 1)) ^ 2
        = (∑ i : Fin (k + 1), sigma (Fin.castSucc i) ^ 2) +
            sigma (Fin.last (k + 1)) ^ 2 := by
            rw [hsumz, hprefix]
    _ = ∑ i : Fin (k + 2), sigma i ^ 2 := by
        rw [Fin.sum_univ_castSucc (fun i : Fin (k + 2) => sigma i ^ 2)]
    _ = frobNorm A ^ 2 := by
        rw [higham14_problem14_13_frobNorm_sq_eq_sum_complex_singularValue_sq A]

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    strict Frobenius-sum certificate for the source GEJ AM-GM family. -/
theorem higham14_problem14_13_gejAmgmFamily_sum_lt_frobNorm_sq
    {k : ℕ} (A Ainv : Fin (k + 2) → Fin (k + 2) → ℝ)
    (hRight : IsRightInverse (k + 2) A Ainv) :
    (∑ i : Fin (k + 2), higham14_problem14_13_gejAmgmFamily A i) <
      frobNorm A ^ 2 := by
  let sigma := fun i : Fin (k + 2) =>
    complexMatrixSingularValue (realRectToCMatrix A) i
  have hlast_pos :=
    higham14_problem14_13_last_singularValue_pos_of_isRightInverse A Ainv hRight
  have hlast_sq_pos : 0 < sigma (Fin.last (k + 1)) ^ 2 :=
    pow_pos hlast_pos 2
  have hsum_add :=
    higham14_problem14_13_gejAmgmFamily_sum_add_last_singularValue_sq A
  calc
    (∑ i : Fin (k + 2), higham14_problem14_13_gejAmgmFamily A i)
        < (∑ i : Fin (k + 2), higham14_problem14_13_gejAmgmFamily A i) +
            sigma (Fin.last (k + 1)) ^ 2 :=
            lt_add_of_pos_right _ hlast_sq_pos
    _ = frobNorm A ^ 2 := hsum_add

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 / equation (14.37):
    Guggenheimer-Edelman-Johnson determinant/condition inequality for
    matrices of dimension at least two, represented as `k + 2`. -/
theorem higham14_problem14_13_gej_bound_of_isRightInverse
    {k : ℕ} (A Ainv : Fin (k + 2) → Fin (k + 2) → ℝ)
    (hRight : IsRightInverse (k + 2) A Ainv) :
    kappa2 A Ainv <
      (2 / |Matrix.det (A : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ)|) *
        (frobNorm A / Real.sqrt ((k + 2 : ℕ) : ℝ)) ^ (k + 2) := by
  exact
    higham14_problem14_13_gej_bound_from_matrix_amgm_certificate
      (Nat.succ_pos (k + 1)) A Ainv
      (higham14_problem14_13_gejAmgmFamily A) hRight
      (higham14_problem14_13_gejAmgmFamily_nonneg A)
      (higham14_problem14_13_gejAmgmFamily_prod A Ainv hRight)
      (higham14_problem14_13_gejAmgmFamily_sum_lt_frobNorm_sq A Ainv hRight)

/-- Higham, 2nd ed., Chapter 14, Problem 14.13(b) support:
    if every row has Euclidean norm one, then the Frobenius norm is
    `sqrt(n)`. -/
theorem higham14_problem14_13_frobNorm_eq_sqrt_card_of_rowNorm2_eq_one
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hrow : ∀ i : Fin n, higham14_rowNorm2 A i = 1) :
    frobNorm A = Real.sqrt (n : ℝ) := by
  refine (sq_eq_sq₀ (frobNorm_nonneg A) (Real.sqrt_nonneg _)).mp ?_
  rw [frobNorm_sq, Real.sq_sqrt (Nat.cast_nonneg n)]
  unfold frobNormSq
  calc
    (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2)
        = ∑ i : Fin n, higham14_rowNorm2 A i ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            simp [higham14_rowNorm2, vecNorm2_sq, vecNorm2Sq]
    _ = ∑ _i : Fin n, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hrow i, one_pow]
    _ = (n : ℝ) := by
            simp [Fintype.card_fin]

/-- Higham, 2nd ed., Chapter 14, Problem 14.13(b) support:
    for unit row norms, the Hadamard condition number is `1 / |det(A)|`. -/
theorem higham14_problem14_13_hadamardConditionNumber_eq_inv_abs_det_of_rowNorm2_eq_one
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hrow : ∀ i : Fin n, higham14_rowNorm2 A i = 1) :
    higham14_hadamardConditionNumber A =
      1 / |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| := by
  unfold higham14_hadamardConditionNumber
  have hprod : (∏ i : Fin n, higham14_rowNorm2 A i) = 1 := by
    simpa using Finset.prod_eq_one (fun i _ => hrow i)
  rw [hprod]

/-- Higham, 2nd ed., Chapter 14, Problem 14.13(b) support:
    the `2/|det(A)|` endpoint is the same as `2 * psi(A)` when all row norms
    are one. -/
theorem higham14_problem14_13_two_over_abs_det_eq_two_mul_hadamardConditionNumber
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hrow : ∀ i : Fin n, higham14_rowNorm2 A i = 1) :
    2 / |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
      2 * higham14_hadamardConditionNumber A := by
  rw [higham14_problem14_13_hadamardConditionNumber_eq_inv_abs_det_of_rowNorm2_eq_one
    A hrow]
  ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.13(b) support:
    combine a supplied `kappa < 2/|det(A)|` bound with the unit-row
    Hadamard-condition-number identity. -/
theorem higham14_problem14_13_kappa_lt_two_mul_hadamardConditionNumber_of_unit_rows
    {n : ℕ} (A : Fin n → Fin n → ℝ) {kappa : ℝ}
    (hrow : ∀ i : Fin n, higham14_rowNorm2 A i = 1)
    (hkappa : kappa < 2 / |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)|) :
    kappa < 2 * higham14_hadamardConditionNumber A := by
  rwa [higham14_problem14_13_two_over_abs_det_eq_two_mul_hadamardConditionNumber
    A hrow] at hkappa

/-- Higham, 2nd ed., Chapter 14, Problem 14.13(b):
    if the rows are normalized to unit Euclidean norm, the GEJ inequality gives
    `kappa_2(A) < 2 * psi(A)` for dimensions at least two. -/
theorem higham14_problem14_13_kappa2_lt_two_mul_hadamardConditionNumber_of_unit_rows
    {k : ℕ} (A Ainv : Fin (k + 2) → Fin (k + 2) → ℝ)
    (hRight : IsRightInverse (k + 2) A Ainv)
    (hrow : ∀ i : Fin (k + 2), higham14_rowNorm2 A i = 1) :
    kappa2 A Ainv < 2 * higham14_hadamardConditionNumber A := by
  refine
    higham14_problem14_13_kappa_lt_two_mul_hadamardConditionNumber_of_unit_rows
      A hrow ?_
  have hgej := higham14_problem14_13_gej_bound_of_isRightInverse A Ainv hRight
  have hfrob :=
    higham14_problem14_13_frobNorm_eq_sqrt_card_of_rowNorm2_eq_one A hrow
  have hsqrt_pos : 0 < Real.sqrt (((k + 2 : ℕ) : ℝ)) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos (k + 1)))
  rw [hfrob] at hgej
  rw [div_self hsqrt_pos.ne', one_pow, mul_one] at hgej
  exact hgej

end NumStability
