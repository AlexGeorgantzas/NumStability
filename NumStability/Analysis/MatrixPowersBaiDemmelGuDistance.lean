/-
# Bai--Demmel--Gu stability radius as a perturbation distance

This file supplies the finite-dimensional bridge intentionally left separate
from `MatrixPowersBaiDemmelGu`: the inverse-resolvent minimum is the operator
two-norm distance to a perturbation having a unit-modulus eigenvalue.
-/

import NumStability.Analysis.MatrixPowersBaiDemmelGu
import NumStability.Analysis.Norms

namespace NumStability

open scoped ComplexOrder Matrix.Norms.L2Operator

open Complex Set

lemma cstarPi_norm_eq_euclidean
    {n : ℕ} (x : WithCStarModule ℂ (Fin n → ℂ)) :
    ‖x‖ = ‖(WithLp.toLp 2 (WithCStarModule.equiv ℂ _ x) :
      EuclideanSpace ℂ (Fin n))‖ := by
  rw [WithCStarModule.pi_norm, EuclideanSpace.norm_eq]
  change Real.sqrt ‖∑ i, x i * star (x i)‖ =
    Real.sqrt (∑ i, ‖x i‖ ^ 2)
  congr 1
  have hcomplex :
      (∑ i, x i * star (x i)) =
        (((∑ i, ‖x i‖ ^ 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    simpa [← starRingEnd_apply, RCLike.mul_conj, pow_two]
  rw [hcomplex, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun i _hi => sq_nonneg ‖x i‖)]

/-- The finite Hilbert `C⋆`-module over `ℂ` is isometric to the usual
Euclidean coordinate space. -/
noncomputable def cstarPiEuclideanLinearIsometryEquiv (n : ℕ) :
    WithCStarModule ℂ (Fin n → ℂ) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n) where
  toFun x := WithLp.toLp 2 (WithCStarModule.equiv ℂ _ x)
  invFun x := (WithCStarModule.equiv ℂ _).symm (WithLp.ofLp x)
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' c x := rfl
  norm_map' x := (cstarPi_norm_eq_euclidean x).symm

@[simp]
lemma cstarPiEuclideanLinearIsometryEquiv_symm_apply_apply
    {n : ℕ} (x : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    (cstarPiEuclideanLinearIsometryEquiv n).symm x i = x i := rfl

@[simp]
lemma cstarPiEuclideanLinearIsometryEquiv_apply_apply
    {n : ℕ} (x : WithCStarModule ℂ (Fin n → ℂ)) (i : Fin n) :
    (cstarPiEuclideanLinearIsometryEquiv n) x i = x i := rfl

lemma cstarMatrix_toCLM_conjugate_eq_euclideanTranspose
    {n : ℕ} (M : CMatrix n n) :
    (cstarPiEuclideanLinearIsometryEquiv n).toLinearIsometry.toContinuousLinearMap.comp
        ((CStarMatrix.toCLM
          (CStarMatrix.ofMatrix (M : Matrix (Fin n) (Fin n) ℂ))).comp
          (cstarPiEuclideanLinearIsometryEquiv n).symm.toLinearIsometry.toContinuousLinearMap) =
      (complexMatrixEuclideanLin (fun i j => M j i)).toContinuousLinearMap := by
  ext x j
  simp [CStarMatrix.toCLM_apply_eq_sum, complexMatrixEuclideanLin,
    Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem cstarMatrix_norm_ofMatrix_eq_complexMatrixOp2
    {n : ℕ} (M : CMatrix n n) :
    ‖CStarMatrix.ofMatrix (M : Matrix (Fin n) (Fin n) ℂ)‖ =
      complexMatrixOp2 (fun i j => M j i) := by
  let E := cstarPiEuclideanLinearIsometryEquiv n
  let T := CStarMatrix.toCLM
    (CStarMatrix.ofMatrix (M : Matrix (Fin n) (Fin n) ℂ))
  have hpost : ‖E.toLinearIsometry.toContinuousLinearMap.comp T‖ = ‖T‖ :=
    E.toLinearIsometry.norm_toContinuousLinearMap_comp (g := T)
  have hpre :
      ‖(E.toLinearIsometry.toContinuousLinearMap.comp T).comp
          E.symm.toLinearIsometry.toContinuousLinearMap‖ =
        ‖E.toLinearIsometry.toContinuousLinearMap.comp T‖ :=
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv
      (E.toLinearIsometry.toContinuousLinearMap.comp T) E.symm
  rw [CStarMatrix.norm_def, complexMatrixOp2_eq_norm_euclideanLin]
  change ‖T‖ =
    ‖(complexMatrixEuclideanLin (fun i j => M j i)).toContinuousLinearMap‖
  rw [← hpost, ← hpre]
  change ‖E.toLinearIsometry.toContinuousLinearMap.comp
      (T.comp E.symm.toLinearIsometry.toContinuousLinearMap)‖ = _
  rw [show E.toLinearIsometry.toContinuousLinearMap.comp
      (T.comp E.symm.toLinearIsometry.toContinuousLinearMap) =
        (complexMatrixEuclideanLin (fun i j => M j i)).toContinuousLinearMap by
      simpa [E, T] using cstarMatrix_toCLM_conjugate_eq_euclideanTranspose M]

/-- Coordinatewise complex conjugation on Euclidean space, viewed as a real
linear isometric involution. -/
noncomputable def euclideanConjLinearIsometryEquiv (n : ℕ) :
    EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin n => Complex.conjLIE)

@[simp]
lemma euclideanConjLinearIsometryEquiv_apply_apply
    {n : ℕ} (x : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    euclideanConjLinearIsometryEquiv n x i = star (x i) := rfl

@[simp]
lemma euclideanConjLinearIsometryEquiv_symm_apply_apply
    {n : ℕ} (x : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    (euclideanConjLinearIsometryEquiv n).symm x i = star (x i) := by
  rw [show (euclideanConjLinearIsometryEquiv n).symm =
      euclideanConjLinearIsometryEquiv n by
    ext y i
    rfl]
  rfl

lemma complexMatrixEuclideanLin_conj_apply
    {n : ℕ} (M : CMatrix n n) :
    ∀ x : EuclideanSpace ℂ (Fin n),
      complexMatrixEuclideanLin (complexConjMatrix M) x =
        euclideanConjLinearIsometryEquiv n
          (complexMatrixEuclideanLin M (euclideanConjLinearIsometryEquiv n x)) := by
  intro x
  ext i
  simp [complexMatrixEuclideanLin, complexConjMatrix, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem complexMatrixOp2_conj_eq {n : ℕ} (M : CMatrix n n) :
    complexMatrixOp2 (complexConjMatrix M) = complexMatrixOp2 M := by
  let J := euclideanConjLinearIsometryEquiv n
  let T := (complexMatrixEuclideanLin M).toContinuousLinearMap
  let Tc := (complexMatrixEuclideanLin (complexConjMatrix M)).toContinuousLinearMap
  have haction (x : EuclideanSpace ℂ (Fin n)) : Tc x = J (T (J x)) := by
    simpa [J, T, Tc] using complexMatrixEuclideanLin_conj_apply M x
  have hJJ (x : EuclideanSpace ℂ (Fin n)) : J (J x) = x := by
    ext i
    simp [J]
  rw [complexMatrixOp2_eq_norm_euclideanLin,
    complexMatrixOp2_eq_norm_euclideanLin]
  change ‖Tc‖ = ‖T‖
  apply le_antisymm
  · apply Tc.opNorm_le_bound (norm_nonneg T)
    intro x
    rw [haction]
    calc
      ‖J (T (J x))‖ = ‖T (J x)‖ := J.norm_map _
      _ ≤ ‖T‖ * ‖J x‖ := T.le_opNorm _
      _ = ‖T‖ * ‖x‖ := by rw [J.norm_map]
  · apply T.opNorm_le_bound (norm_nonneg Tc)
    intro x
    calc
      ‖T x‖ = ‖Tc (J x)‖ := by
        rw [haction, hJJ]
        exact (J.norm_map (T x)).symm
      _ ≤ ‖Tc‖ * ‖J x‖ := Tc.le_opNorm _
      _ = ‖Tc‖ * ‖x‖ := by rw [J.norm_map]

/-- The source-facing operator two-norm is invariant under ordinary
transpose, also over complex matrices. -/
theorem complexMatrixOp2_transpose_eq {n : ℕ} (M : CMatrix n n) :
    complexMatrixOp2 (fun i j => M j i) = complexMatrixOp2 M := by
  calc
    complexMatrixOp2 (fun i j => M j i) =
        complexMatrixOp2 (complexMatrixAdjoint (complexConjMatrix M)) := by
      congr 1
      ext i j
      simp [complexMatrixAdjoint, complexMatrixTranspose, complexConjMatrix]
    _ = complexMatrixOp2 (complexConjMatrix M) :=
      complexMatrixOp2_adjoint_eq (complexConjMatrix M)
    _ = complexMatrixOp2 M := complexMatrixOp2_conj_eq M

/-- Exact norm bridge: the `CStarMatrix` norm over `ℂ` is precisely the
usual Euclidean operator two-norm of the represented matrix. -/
theorem cstarMatrix_norm_eq_complexMatrixOp2
    {n : ℕ} (M : CMatrix n n) :
    ‖CStarMatrix.ofMatrix (M : Matrix (Fin n) (Fin n) ℂ)‖ =
      complexMatrixOp2 M := by
  rw [cstarMatrix_norm_ofMatrix_eq_complexMatrixOp2,
    complexMatrixOp2_transpose_eq]

/-! ## Exact operator-two-norm distance to singularity -/

noncomputable def complexVectorMapMatrix
    {n : ℕ} (T : ComplexVectorMap n n) : CMatrix n n :=
  fun i j => T (standardBasisCVec j) i

theorem complexMatrixVecMul_complexVectorMapMatrix
    {n : ℕ} {T : ComplexVectorMap n n}
    (hT : IsComplexVectorMapLinear T) :
    complexMatrixVecMul (complexVectorMapMatrix T) = T := by
  funext x
  ext i
  let phi : CVec n → ℂ := fun y => T y i
  have hphi : IsComplexLinearForm phi := by
    constructor
    · intro y z
      exact congrFun (hT.map_add y z) i
    · intro c y
      exact congrFun (hT.map_smul c y) i
  change (∑ j : Fin n, T (standardBasisCVec j) i * x j) = T x i
  rw [show T x i = ∑ j : Fin n, x j * T (standardBasisCVec j) i by
    simpa [phi] using hphi.apply_eq_sum_basis x]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

theorem complexMatrixVecMul_add
    {m n : ℕ} (A B : CMatrix m n) :
    complexMatrixVecMul (A + B) =
      complexVectorMapAdd (complexMatrixVecMul A) (complexMatrixVecMul B) := by
  funext x
  ext i
  simp [complexMatrixVecMul, complexVectorMapAdd, complexVecAdd,
    Finset.sum_add_distrib, add_mul]

theorem isComplexMatrixLpNormValue_two_op2
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    IsComplexMatrixLpNormValue (ENNReal.ofReal (2 : ℝ)) A
      (complexMatrixOp2 A) := by
  haveI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  have h := complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
    (m := m) (n := n) hn (2 : ℝ) (by norm_num) A
  rw [complexMatrixLpNormOfReal_two_eq_complexMatrixOp2 hn] at h
  exact h

theorem complexMatrixOp2_pos_of_inverse_left
    {n : ℕ} (hn : 0 < n) {A Ainv : CMatrix n n}
    (hInv : IsComplexMatrixInverse A Ainv) :
    0 < complexMatrixOp2 Ainv := by
  refine lt_of_le_of_ne (complexMatrixOp2_nonneg Ainv) ?_
  intro hzero
  have hAinv0 : Ainv = 0 :=
    complexMatrix_eq_zero_of_op2_eq_zero hzero.symm
  let j : Fin n := ⟨0, hn⟩
  have h := hInv.1 (standardBasisCVec j)
  rw [hAinv0] at h
  have hz : complexMatrixVecMul (0 : CMatrix n n)
      (complexMatrixVecMul A (standardBasisCVec j)) = 0 := by
    ext i
    simp [complexMatrixVecMul]
  rw [hz] at h
  exact standardBasisCVec_ne_zero j h.symm

theorem complexMatrixOp2_pos_of_inverse_right
    {n : ℕ} (hn : 0 < n) {A Ainv : CMatrix n n}
    (hInv : IsComplexMatrixInverse A Ainv) :
    0 < complexMatrixOp2 A := by
  refine lt_of_le_of_ne (complexMatrixOp2_nonneg A) ?_
  intro hzero
  have hA0 : A = 0 := complexMatrix_eq_zero_of_op2_eq_zero hzero.symm
  let j : Fin n := ⟨0, hn⟩
  have h := hInv.2 (standardBasisCVec j)
  rw [hA0] at h
  have hz : complexMatrixVecMul (0 : CMatrix n n)
      (complexMatrixVecMul Ainv (standardBasisCVec j)) = 0 := by
    ext i
    simp [complexMatrixVecMul]
  rw [hz] at h
  exact standardBasisCVec_ne_zero j h.symm

/-- Candidate absolute operator-two-norm distances from `B` to a singular
matrix. -/
def singularPerturbationOp2Set {n : ℕ} (B : CMatrix n n) : Set ℝ :=
  {d | ∃ Δ : CMatrix n n,
    IsSingularComplexVectorMap (complexMatrixVecMul (B + Δ)) ∧
      d = complexMatrixOp2 Δ}

/-- The finite-dimensional Gastinel--Kahan theorem in the absolute operator
two-norm form needed in Chapter 18.  The minimum is attained. -/
theorem singularPerturbationOp2_isLeast
    {n : ℕ} (hn : 0 < n) {B Binv : CMatrix n n}
    (hInv : IsComplexMatrixInverse B Binv) :
    IsLeast (singularPerturbationOp2Set B) (complexMatrixOp2 Binv)⁻¹ := by
  haveI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  let nu : CVec n → ℝ := complexVecLpNorm (ENNReal.ofReal (2 : ℝ))
  have hnu : IsComplexVectorNorm nu :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal (2 : ℝ))
  let a : ℝ := complexMatrixOp2 B
  let s : ℝ := complexMatrixOp2 Binv
  have ha : 0 < a := by
    simpa [a] using complexMatrixOp2_pos_of_inverse_right hn hInv
  have hs : 0 < s := by
    simpa [s] using complexMatrixOp2_pos_of_inverse_left hn hInv
  have hB : IsMixedSubordinateMatrixNormValue nu nu B a := by
    simpa [nu, a, IsComplexMatrixLpNormValue] using
      isComplexMatrixLpNormValue_two_op2 hn B
  have hBinv : IsMixedSubordinateMatrixNormValue nu nu Binv s := by
    simpa [nu, s, IsComplexMatrixLpNormValue] using
      isComplexMatrixLpNormValue_two_op2 hn Binv
  constructor
  · obtain ⟨T, hTlin, hTval, hsing⟩ :=
      exists_singular_perturbation_attaining_inverse_bound
        hnu hnu hInv.2 (complexMatrixVecMul_linear Binv) hBinv hs
    let Δ : CMatrix n n := complexVectorMapMatrix T
    have hTaction : complexMatrixVecMul Δ = T := by
      simpa [Δ] using complexMatrixVecMul_complexVectorMapMatrix hTlin
    have hΔval : IsComplexMatrixLpNormValue (ENNReal.ofReal (2 : ℝ)) Δ s⁻¹ := by
      change IsMixedSubordinateMatrixNormValue nu nu Δ s⁻¹
      change IsMixedSubordinateNormValue nu nu (complexMatrixVecMul Δ) s⁻¹
      rw [hTaction]
      exact hTval
    have hΔnorm : complexMatrixOp2 Δ = s⁻¹ := by
      exact (isComplexMatrixLpNormValue_two_eq_complexMatrixOp2 hn hΔval).symm
    refine ⟨Δ, ?_, by simpa [s, hΔnorm]⟩
    rw [complexMatrixVecMul_add, hTaction]
    exact hsing
  · intro d hd
    obtain ⟨Δ, hsing, rfl⟩ := hd
    have hΔ : IsMixedSubordinateMatrixNormValue nu nu Δ
        (complexMatrixOp2 Δ) := by
      simpa [nu, IsComplexMatrixLpNormValue] using
        isComplexMatrixLpNormValue_two_op2 hn Δ
    have hsing' : IsSingularComplexVectorMap
        (complexVectorMapAdd (complexMatrixVecMul B)
          (complexMatrixVecMul Δ)) := by
      rw [← complexMatrixVecMul_add]
      exact hsing
    have hrel := singular_perturbation_inv_condition_le_relative_bound
      hnu hnu ha hs hInv.1 hBinv.1 hΔ.1 hsing'
    have hrewrite : (a * s)⁻¹ = s⁻¹ / a := by
      field_simp [ha.ne', hs.ne']
    rw [hrewrite] at hrel
    have habs : s⁻¹ ≤ complexMatrixOp2 Δ :=
      (div_le_div_iff_of_pos_right ha).mp hrel
    simpa [s] using habs

theorem cstarMatrix_ringInverse_isComplexMatrixInverse
    {n : ℕ} (M : CStarMatrix (Fin n) (Fin n) ℂ) (hM : IsUnit M) :
    IsComplexMatrixInverse
      (fun i j => M i j)
      (fun i j => Ring.inverse M i j) := by
  constructor
  · intro x
    change Matrix.mulVec (Ring.inverse M) (Matrix.mulVec M x) = x
    have hprod : Ring.inverse M * M = 1 :=
      Ring.inverse_mul_cancel M hM
    rw [Matrix.mulVec_mulVec]
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    have hentry (j : Fin n) :
        (∑ k, Ring.inverse M i k * M k j) = if i = j then 1 else 0 := by
      have hij := congrArg
        (fun N : CStarMatrix (Fin n) (Fin n) ℂ => N i j) hprod
      simpa [CStarMatrix.mul_apply, CStarMatrix.one_apply] using hij
    calc
      (∑ j, (∑ k, Ring.inverse M i k * M k j) * x j) =
          ∑ j, (if i = j then 1 else 0) * x j := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [hentry j]
      _ = x i := by simp
  · intro x
    change Matrix.mulVec M (Matrix.mulVec (Ring.inverse M) x) = x
    have hprod : M * Ring.inverse M = 1 :=
      Ring.mul_inverse_cancel M hM
    rw [Matrix.mulVec_mulVec]
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    have hentry (j : Fin n) :
        (∑ k, M i k * Ring.inverse M k j) = if i = j then 1 else 0 := by
      have hij := congrArg
        (fun N : CStarMatrix (Fin n) (Fin n) ℂ => N i j) hprod
      simpa [CStarMatrix.mul_apply, CStarMatrix.one_apply] using hij
    calc
      (∑ j, (∑ k, M i k * Ring.inverse M k j) * x j) =
          ∑ j, (if i = j then 1 else 0) * x j := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [hentry j]
      _ = x i := by simp

noncomputable def complexShiftMatrix
    {n : ℕ} (A : CMatrix n n) (z : ℂ) : CMatrix n n :=
  fun i j => (if i = j then z else 0) - A i j

theorem cstarMatrix_of_complexShiftMatrix
    {n : ℕ} (A : CMatrix n n) (z : ℂ) :
    CStarMatrix.ofMatrix
        (complexShiftMatrix A z : Matrix (Fin n) (Fin n) ℂ) =
      algebraMap ℂ (CStarMatrix (Fin n) (Fin n) ℂ) z -
        CStarMatrix.ofMatrix (A : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  simp [complexShiftMatrix, CStarMatrix.algebraMap_apply]

theorem complexMatrixVecMul_complexShiftMatrix_apply
    {n : ℕ} (A : CMatrix n n) (z : ℂ) (x : CVec n) (i : Fin n) :
    complexMatrixVecMul (complexShiftMatrix A z) x i =
      z * x i - complexMatrixVecMul A x i := by
  simp [complexMatrixVecMul, complexShiftMatrix, Finset.sum_sub_distrib,
    sub_mul, Finset.sum_ite_irrel, Finset.filter_eq']

theorem complexMatrixOp2_neg {m n : ℕ} (A : CMatrix m n) :
    complexMatrixOp2 (-A) = complexMatrixOp2 A := by
  have h := complexMatrixOp2_smul (-1 : ℂ) A
  simpa using h

/-- Fixed-target candidate perturbation sizes: `A + Δ` has eigenvalue `z`. -/
def fixedEigenvaluePerturbationOp2Set
    {n : ℕ} (A : CMatrix n n) (z : ℂ) : Set ℝ :=
  {d | ∃ Δ : CMatrix n n, ∃ x : CVec n,
    x ≠ 0 ∧
      complexMatrixVecMul (A + Δ) x = complexVecSMul z x ∧
      d = complexMatrixOp2 Δ}

theorem fixedEigenvaluePerturbationOp2Set_iff_singularShift
    {n : ℕ} {A : CMatrix n n} {z : ℂ} {d : ℝ} :
    d ∈ fixedEigenvaluePerturbationOp2Set A z ↔
      d ∈ singularPerturbationOp2Set (complexShiftMatrix A z) := by
  constructor
  · rintro ⟨Δ, x, hx, heig, rfl⟩
    refine ⟨-Δ, ⟨x, hx, ?_⟩, ?_⟩
    · ext i
      have hi := congrFun heig i
      simp only [complexMatrixVecMul_add, complexVectorMapAdd,
        complexVecAdd] at hi ⊢
      rw [complexMatrixVecMul_complexShiftMatrix_apply]
      simp only [complexMatrixVecMul, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib,
        complexVecSMul, Pi.zero_apply] at hi ⊢
      linear_combination -hi
    · exact (complexMatrixOp2_neg Δ).symm
  · rintro ⟨E, ⟨x, hx, hsing⟩, rfl⟩
    refine ⟨-E, x, hx, ?_, ?_⟩
    · ext i
      have hi := congrFun hsing i
      simp only [complexMatrixVecMul_add, complexVectorMapAdd,
        complexVecAdd] at hi ⊢
      rw [complexMatrixVecMul_complexShiftMatrix_apply] at hi
      simp only [complexMatrixVecMul, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib,
        complexVecSMul, Pi.zero_apply] at hi ⊢
      linear_combination -hi
    · exact (complexMatrixOp2_neg E).symm

/-- For a fixed resolvent point `z`, the reciprocal resolvent norm is exactly
the attained operator-two-norm distance to matrices having eigenvalue `z`. -/
theorem fixedEigenvaluePerturbationOp2_isLeast
    {n : ℕ} (hn : 0 < n) (A : CMatrix n n) (z : ℂ)
    (hzRes : z ∈ resolventSet ℂ
      (CStarMatrix.ofMatrix (A : Matrix (Fin n) (Fin n) ℂ))) :
    IsLeast (fixedEigenvaluePerturbationOp2Set A z)
      ‖resolvent
        (CStarMatrix.ofMatrix (A : Matrix (Fin n) (Fin n) ℂ)) z‖⁻¹ := by
  let a : CStarMatrix (Fin n) (Fin n) ℂ :=
    CStarMatrix.ofMatrix (A : Matrix (Fin n) (Fin n) ℂ)
  let M : CStarMatrix (Fin n) (Fin n) ℂ := algebraMap ℂ _ z - a
  let B : CMatrix n n := complexShiftMatrix A z
  let R : CMatrix n n := fun i j => resolvent a z i j
  have hMunit : IsUnit M := by
    simpa [M, a] using hzRes
  have hInv : IsComplexMatrixInverse B R := by
    have h := cstarMatrix_ringInverse_isComplexMatrixInverse M hMunit
    simpa [B, R, M, a, resolvent, cstarMatrix_of_complexShiftMatrix] using h
  have hleast := singularPerturbationOp2_isLeast hn hInv
  have hRnorm : complexMatrixOp2 R = ‖resolvent a z‖ := by
    have h := cstarMatrix_norm_eq_complexMatrixOp2 R
    simpa [R] using h.symm
  have hfixed : IsLeast (fixedEigenvaluePerturbationOp2Set A z)
      (complexMatrixOp2 R)⁻¹ := by
    constructor
    · exact fixedEigenvaluePerturbationOp2Set_iff_singularShift.mpr hleast.1
    · intro d hd
      exact hleast.2
        (fixedEigenvaluePerturbationOp2Set_iff_singularShift.mp hd)
  simpa [a, hRnorm] using hfixed

/-! ## The unit-circle perturbation distance -/

/-- Literal Higham/Bai--Demmel--Gu perturbation set: operator-two-norm sizes
of perturbations for which `A + Δ` has an eigenvalue on the unit circle. -/
def unitCircleEigenvaluePerturbationOp2Set
    {n : ℕ} (A : CMatrix n n) : Set ℝ :=
  {d | ∃ Δ : CMatrix n n, ∃ z : ℂ, ∃ x : CVec n,
    ‖z‖ = 1 ∧ x ≠ 0 ∧
      complexMatrixVecMul (A + Δ) x = complexVecSMul z x ∧
      d = complexMatrixOp2 Δ}

/-- The literal operator-two-norm perturbation distance. -/
noncomputable def unitCircleEigenvaluePerturbationOp2Distance
    {n : ℕ} (A : CMatrix n n) : ℝ :=
  sInf (unitCircleEigenvaluePerturbationOp2Set A)

/-- **Chapter 18 distance identification.**  For a nonempty finite complex
matrix with spectral radius below one, the Bai--Demmel--Gu unit-circle
inverse-resolvent minimum is exactly the attained minimum operator-two-norm
perturbation that moves an eigenvalue to the unit circle. -/
theorem unitCircleEigenvaluePerturbationOp2_isLeast
    {n : ℕ} (hn : 0 < n) (A : CMatrix n n)
    (hrho : spectralRadius ℂ
      (CStarMatrix.ofMatrix (A : Matrix (Fin n) (Fin n) ℂ)) < 1) :
    IsLeast (unitCircleEigenvaluePerturbationOp2Set A)
      (unitCircleStabilityRadius
        (CStarMatrix.ofMatrix (A : Matrix (Fin n) (Fin n) ℂ))) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let a : CStarMatrix (Fin n) (Fin n) ℂ :=
    CStarMatrix.ofMatrix (A : Matrix (Fin n) (Fin n) ℂ)
  have hcircle := unitCircleStabilityRadius_isLeast a hrho
  constructor
  · rcases hcircle.1 with ⟨z, hz, hEq⟩
    have hzSphere : z ∈ Metric.sphere (0 : ℂ) 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hz
    have hzRes := unitSphere_subset_resolventSet_of_spectralRadius_lt_one
      a hrho hzSphere
    have hfixed := fixedEigenvaluePerturbationOp2_isLeast hn A z
      (by simpa [a] using hzRes)
    rcases hfixed.1 with ⟨Δ, x, hx, heig, hΔ⟩
    refine ⟨Δ, z, x, hz, hx, heig, ?_⟩
    calc
      unitCircleStabilityRadius a = ‖resolvent a z‖⁻¹ := hEq
      _ = complexMatrixOp2 Δ := hΔ
  · intro d hd
    rcases hd with ⟨Δ, z, x, hz, hx, heig, rfl⟩
    have hzSphere : z ∈ Metric.sphere (0 : ℂ) 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hz
    have hzRes := unitSphere_subset_resolventSet_of_spectralRadius_lt_one
      a hrho hzSphere
    have hfixed := fixedEigenvaluePerturbationOp2_isLeast hn A z
      (by simpa [a] using hzRes)
    have hlocal : ‖resolvent a z‖⁻¹ ≤ complexMatrixOp2 Δ :=
      hfixed.2 ⟨Δ, x, hx, heig, rfl⟩
    have hglobal : unitCircleStabilityRadius a ≤ ‖resolvent a z‖⁻¹ :=
      hcircle.2 ⟨z, hz, rfl⟩
    exact hglobal.trans hlocal

/-- Equality form of the Chapter 18 identification
`d(A) = min_{‖z‖=1} ‖(zI-A)⁻¹‖⁻¹`. -/
theorem unitCircleEigenvaluePerturbationOp2Distance_eq_stabilityRadius
    {n : ℕ} (hn : 0 < n) (A : CMatrix n n)
    (hrho : spectralRadius ℂ
      (CStarMatrix.ofMatrix (A : Matrix (Fin n) (Fin n) ℂ)) < 1) :
    unitCircleEigenvaluePerturbationOp2Distance A =
      unitCircleStabilityRadius
        (CStarMatrix.ofMatrix (A : Matrix (Fin n) (Fin n) ℂ)) := by
  exact (unitCircleEigenvaluePerturbationOp2_isLeast hn A hrho).csInf_eq

end NumStability
