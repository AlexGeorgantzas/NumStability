-- Analysis/MatrixNorms/SpectralRadius.lean
--
-- Spectral-radius constructions and norm bounds for complex matrices.

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import NumStability.Analysis.LinearOperators.Triangularization
import NumStability.Analysis.MatrixNorms.Basic

/-!
# Spectral-radius norm constructions

Relates matrix spectra and maximal eigenvalue modulus to spectral radius,
including triangularization-based norm constructions and comparison bounds.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


/-- Concrete matrix-facing triangularization bridge for Higham Problem 6.8:
    every square complex matrix has a coordinate basis in which the associated
    source-facing matrix-vector map is upper triangular. -/
theorem exists_complexMatrixVecMul_blockTriangular_toMatrix
    {n : ℕ} (A : CMatrix n n) :
    ∃ b : Module.Basis (Fin n) ℂ (CVec n),
      (show Matrix (Fin n) (Fin n) ℂ from
        complexMatrixVecMulCoordinateMatrix A b).BlockTriangular id := by
  have hfin : Module.finrank ℂ (CVec n) = n := by
    calc
      Module.finrank ℂ (CVec n) = Fintype.card (Fin n) := by
        simp [CVec, Module.finrank_fintype_fun_eq_card]
      _ = n := Fintype.card_fin n
  simpa [complexMatrixVecMulCoordinateMatrix] using
    exists_blockTriangular_toMatrix_of_finrank (K := ℂ) n hfin
    (complexVectorMapLinearMap (complexMatrixVecMul A)
      (complexMatrixVecMul_linear A))

/-- Matrix version of the eigenvalue-modulus set. -/
def ComplexMatrixEigenvalueModulusSet {n : ℕ}
    (A : CMatrix n n) : Set ℝ :=
  ComplexVectorMapEigenvalueModulusSet (complexMatrixVecMul A)

/-- Matrix version of a maximum spectral modulus. -/
def IsMaxComplexMatrixEigenvalueModulus {n : ℕ}
    (A : CMatrix n n) (ρ : ℝ) : Prop :=
  IsMaxComplexVectorMapEigenvalueModulus (complexMatrixVecMul A) ρ

/-- The generic finite complex-matrix eigenvalue-modulus carrier is exactly
the moduli of Mathlib spectrum elements for the corresponding `toLin'`
endomorphism. -/
theorem complexMatrixEigenvalueModulusSet_eq_toLin_spectrum_modulusSet
    {n : ℕ} (A : CMatrix n n) :
    ComplexMatrixEigenvalueModulusSet A =
      {r : ℝ | ∃ lam : ℂ,
        lam ∈ spectrum ℂ
          (Matrix.toLin' (show Matrix (Fin n) (Fin n) ℂ from A)) ∧
        r = ‖lam‖} := by
  ext r
  constructor
  · intro hr
    rcases hr with ⟨lam, x, hx_ne, hx_eig, rfl⟩
    let M : Matrix (Fin n) (Fin n) ℂ := A
    have happly : Matrix.toLin' M x = lam • x := by
      ext i
      have hi := congrFun hx_eig i
      simpa [M, complexMatrixVecMul, complexVecSMul, Matrix.toLin'_apply,
        Matrix.mulVec, dotProduct] using hi
    have hx_vec :
        Module.End.HasEigenvector (Matrix.toLin' M) lam x := by
      rw [Module.End.hasEigenvector_iff]
      constructor
      · rwa [Module.End.mem_eigenspace_iff]
      · exact hx_ne
    have hlam :
        Module.End.HasEigenvalue (Matrix.toLin' M) lam :=
      Module.End.hasEigenvalue_of_hasEigenvector hx_vec
    exact ⟨lam, by simpa [M] using Module.End.HasEigenvalue.mem_spectrum hlam, rfl⟩
  · intro hr
    rcases hr with ⟨lam, hspec, rfl⟩
    let M : Matrix (Fin n) (Fin n) ℂ := A
    have hlam :
        Module.End.HasEigenvalue (Matrix.toLin' M) lam :=
      Module.End.HasEigenvalue.of_mem_spectrum (by simpa [M] using hspec)
    rcases Module.End.HasEigenvalue.exists_hasEigenvector hlam with ⟨x, hx⟩
    have hx_ne : x ≠ 0 := (Module.End.hasEigenvector_iff.mp hx).2
    refine ⟨lam, x, hx_ne, ?_, rfl⟩
    have happly := Module.End.HasEigenvector.apply_eq_smul hx
    rw [Matrix.toLin'_apply] at happly
    ext i
    have hi := congrFun happly i
    simpa [M, complexMatrixVecMul, complexVecSMul, Matrix.mulVec, dotProduct]
      using hi

/-- If the Mathlib spectrum-modulus carrier for a concrete complex matrix has
    greatest real value `ρ`, then Mathlib's Banach-algebra `spectralRadius`
    of the corresponding `toLin'` endomorphism is exactly `ENNReal.ofReal ρ`.
    This is the reusable bridge between the source-facing real spectral radius
    and Mathlib's `ℝ≥0∞` spectral-radius API. -/
theorem toLin_spectralRadius_eq_of_spectrum_modulusSet_isGreatest
    {n : ℕ} (A : CMatrix n n) {ρ : ℝ}
    (hgreatest : IsGreatest
      {r : ℝ | ∃ lam : ℂ,
        lam ∈ spectrum ℂ
          (Matrix.toLin' (show Matrix (Fin n) (Fin n) ℂ from A)) ∧
        r = ‖lam‖} ρ) :
    spectralRadius ℂ
      (Matrix.toLin' (show Matrix (Fin n) (Fin n) ℂ from A)) =
      ENNReal.ofReal ρ := by
  unfold spectralRadius
  apply le_antisymm
  · apply iSup₂_le
    intro lam hlam
    have hle_real : ‖lam‖ ≤ ρ := by
      exact hgreatest.2 ⟨lam, hlam, rfl⟩
    calc
      (nnnorm lam : ENNReal) = ENNReal.ofReal (‖lam‖) := by
        simp [ENNReal.ofReal]
      _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal hle_real
  · rcases hgreatest.1 with ⟨lam, hlam, hρ⟩
    rw [hρ]
    rw [show ENNReal.ofReal (‖lam‖) = (nnnorm lam : ENNReal) by
      simp [ENNReal.ofReal]]
    exact le_iSup₂ (α := ENNReal) lam hlam

/-- Real-valued form of
    `toLin_spectralRadius_eq_of_spectrum_modulusSet_isGreatest`. -/
theorem toLin_spectralRadius_toReal_eq_of_spectrum_modulusSet_isGreatest
    {n : ℕ} (A : CMatrix n n) {ρ : ℝ}
    (hgreatest : IsGreatest
      {r : ℝ | ∃ lam : ℂ,
        lam ∈ spectrum ℂ
          (Matrix.toLin' (show Matrix (Fin n) (Fin n) ℂ from A)) ∧
        r = ‖lam‖} ρ) :
    (spectralRadius ℂ
      (Matrix.toLin' (show Matrix (Fin n) (Fin n) ℂ from A))).toReal = ρ := by
  have hρ_nonneg : 0 ≤ ρ := by
    rcases hgreatest.1 with ⟨lam, _hlam, hρ⟩
    rw [hρ]
    exact norm_nonneg lam
  rw [toLin_spectralRadius_eq_of_spectrum_modulusSet_isGreatest A hgreatest,
    ENNReal.toReal_ofReal hρ_nonneg]

/-- A maximum complex-matrix eigenvalue-modulus certificate identifies the
    Mathlib `spectralRadius` of the matrix's `toLin'` endomorphism. -/
theorem complexMatrix_toLin_spectralRadius_eq_of_isMaxComplexMatrixEigenvalueModulus
    {n : ℕ} {A : CMatrix n n} {ρ : ℝ}
    (hρ : IsMaxComplexMatrixEigenvalueModulus A ρ) :
    spectralRadius ℂ
      (Matrix.toLin' (show Matrix (Fin n) (Fin n) ℂ from A)) =
      ENNReal.ofReal ρ := by
  have hgreatest : IsGreatest (ComplexMatrixEigenvalueModulusSet A) ρ := hρ
  rw [complexMatrixEigenvalueModulusSet_eq_toLin_spectrum_modulusSet A] at hgreatest
  exact toLin_spectralRadius_eq_of_spectrum_modulusSet_isGreatest A hgreatest

/-- Eigenvalue-modulus witnesses are invariant when a concrete matrix is
    replaced by its coordinate matrix in an arbitrary basis. -/
theorem complexMatrixEigenvalueModulusSet_coordinateMatrix_subset
    {n : ℕ} (A : CMatrix n n)
    (b : Module.Basis (Fin n) ℂ (CVec n)) :
    ComplexMatrixEigenvalueModulusSet
        (complexMatrixVecMulCoordinateMatrix A b) ⊆
      ComplexMatrixEigenvalueModulusSet A := by
  intro r hr
  rcases hr with ⟨lam, y, hyne, hy, rfl⟩
  let x : CVec n := b.equivFun.symm y
  have hxne : x ≠ 0 := by
    intro hx
    apply hyne
    apply b.equivFun.symm.injective
    simpa [x] using hx
  refine ⟨lam, x, hxne, ?_, rfl⟩
  let L : CVec n →ₗ[ℂ] CVec n :=
    complexVectorMapLinearMap (complexMatrixVecMul A) (complexMatrixVecMul_linear A)
  have hxcoord : ∀ j : Fin n, b.repr x j = y j := by
    intro j
    have hxy : b.equivFun x = y := by
      dsimp [x]
      exact b.equivFun.apply_symm_apply y
    exact congrFun hxy j
  have hcoord_mul :
      complexMatrixVecMul (complexMatrixVecMulCoordinateMatrix A b) y =
        b.equivFun (complexMatrixVecMul A x) := by
    ext i
    have hmat := congrFun
      (LinearMap.toMatrix_mulVec_repr
        (v₁ := b) (v₂ := b) L x) i
    calc
      complexMatrixVecMul (complexMatrixVecMulCoordinateMatrix A b) y i =
          ∑ j : Fin n, (LinearMap.toMatrix b b L) i j * y j := by
            rfl
      _ = ∑ j : Fin n, (LinearMap.toMatrix b b L) i j * b.repr x j := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            rw [hxcoord j]
      _ = b.repr (L x) i := by
            simpa [Matrix.mulVec, dotProduct] using hmat
      _ = b.equivFun (complexMatrixVecMul A x) i := rfl
  apply b.equivFun.injective
  have hleft :
      b.equivFun (complexMatrixVecMul A x) = fun i : Fin n => lam * y i := by
    rw [← hcoord_mul, hy]
    ext i
    simp [complexVecSMul]
  have hright :
      b.equivFun (complexVecSMul lam x) = fun i : Fin n => lam * y i := by
    ext i
    have hsmul : complexVecSMul lam x = lam • x := by
      ext k
      rfl
    rw [hsmul]
    have hmap := congrFun (b.equivFun.map_smul lam x) i
    have hxy : b.equivFun x = y := by
      dsimp [x]
      exact b.equivFun.apply_symm_apply y
    rw [hmap, hxy]
    rfl
  exact hleft.trans hright.symm

/-- For an upper-triangular complex matrix, every diagonal entry contributes
    an eigenvalue-modulus witness to the local spectral-radius carrier. -/
theorem upperTriangular_diagonal_mem_complexMatrixEigenvalueModulusSet
    {n : ℕ} (T : CMatrix n n)
    (hT : (show Matrix (Fin n) (Fin n) ℂ from T).BlockTriangular id)
    (i : Fin n) :
    Membership.mem (ComplexMatrixEigenvalueModulusSet T) (norm (T i i)) := by
  let M : Matrix (Fin n) (Fin n) ℂ := T
  have hTM : M.BlockTriangular id := by
    simpa [M] using hT
  have hroot : M.charpoly.IsRoot (M i i) := by
    rw [Matrix.charpoly_of_upperTriangular M hTM, Polynomial.IsRoot,
      Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hspecM : Membership.mem (spectrum ℂ M) (M i i) :=
    Matrix.mem_spectrum_of_isRoot_charpoly hroot
  have hspecLin : Membership.mem (spectrum ℂ (Matrix.toLin' M)) (M i i) := by
    rwa [Matrix.spectrum_toLin' M]
  have heig : Module.End.HasEigenvalue (Matrix.toLin' M) (M i i) :=
    Module.End.HasEigenvalue.of_mem_spectrum hspecLin
  cases Module.End.HasEigenvalue.exists_hasEigenvector heig with
  | intro x hx =>
      have hxne : x = 0 -> False := (Module.End.hasEigenvector_iff.mp hx).2
      refine Exists.intro (M i i) ?_
      refine Exists.intro x ?_
      refine And.intro hxne ?_
      refine And.intro ?_ rfl
      have hxeq := Module.End.HasEigenvector.apply_eq_smul hx
      rw [Matrix.toLin'_apply] at hxeq
      ext k
      exact congrFun hxeq k

/-- A locally represented spectral-radius maximum bounds the diagonal entries
    of any upper-triangular coordinate model. -/
theorem upperTriangular_diagonal_norm_le_maxComplexMatrixEigenvalueModulus
    {n : ℕ} {T : CMatrix n n} {ρ : ℝ}
    (hT : (show Matrix (Fin n) (Fin n) ℂ from T).BlockTriangular id)
    (hρ : IsMaxComplexMatrixEigenvalueModulus T ρ) (i : Fin n) :
    norm (T i i) <= ρ :=
  hρ.2 (norm (T i i))
    (upperTriangular_diagonal_mem_complexMatrixEigenvalueModulusSet T hT i)

/-- Higham Problem 6.7, concrete matrix form. -/
theorem complexMatrixEigenvalueModulus_le_mixedSubordinateMatrixNormValue
    {n : ℕ} {ν : CVec n → ℝ} {A : CMatrix n n} {c r : ℝ}
    (hν : IsComplexVectorNorm ν)
    (hA : IsMixedSubordinateMatrixNormValue ν ν A c)
    (hr : r ∈ ComplexMatrixEigenvalueModulusSet A) :
    r ≤ c :=
  eigenvalueModulus_le_mixedSubordinateNormValue hν hA hr

/-- Higham Problem 6.7, concrete matrix maximum-modulus form. -/
theorem maxComplexMatrixEigenvalueModulus_le_mixedSubordinateMatrixNormValue
    {n : ℕ} {ν : CVec n → ℝ} {A : CMatrix n n} {c ρ : ℝ}
    (hν : IsComplexVectorNorm ν)
    (hA : IsMixedSubordinateMatrixNormValue ν ν A c)
    (hρ : IsMaxComplexMatrixEigenvalueModulus A ρ) :
    ρ ≤ c :=
  maxEigenvalueModulus_le_mixedSubordinateNormValue hν hA hρ

lemma geomWeight_later_le {n : ℕ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {i j : Fin n} (hij : i < j) :
    r ^ j.val ≤ r * r ^ i.val := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hij
  have hpowk : r ^ k ≤ 1 := pow_le_one₀ hr0 hr1
  have hnonneg : 0 ≤ r * r ^ i.val := by
    exact mul_nonneg hr0 (pow_nonneg hr0 _)
  calc
    r ^ j.val = r ^ (i.val + k + 1) := by rw [hk]
    _ = (r * r ^ i.val) * r ^ k := by
      rw [pow_succ, pow_add]
      ring
    _ ≤ (r * r ^ i.val) * 1 :=
      mul_le_mul_of_nonneg_left hpowk hnonneg
    _ = r * r ^ i.val := by ring

theorem complexVecWeightedInfNorm_matrix_bound_of_weighted_rows
    {n : ℕ} {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (T : CMatrix n n)
    (hrow : ∀ i : Fin n,
      (∑ j : Fin n, ‖T i j‖ * r ^ j.val) ≤ C * r ^ i.val) :
    MixedSubordinateMatrixBound
      (complexVecWeightedInfNorm (n := n) r)
      (complexVecWeightedInfNorm (n := n) r)
      T C := by
  intro x
  unfold complexVecWeightedInfNorm
  apply complexVecInfNorm_le_of_coord_le
  · exact mul_nonneg hC (complexVecInfNorm_nonneg _)
  intro i
  have hpow_pos : 0 < r ^ i.val := pow_pos hr i.val
  have hinv_nonneg : 0 ≤ (r ^ i.val)⁻¹ := inv_nonneg.mpr (le_of_lt hpow_pos)
  have hscale :
      ‖(((r ^ i.val : ℝ) : ℂ)⁻¹ * complexMatrixVecMul T x i)‖ =
        (r ^ i.val)⁻¹ * ‖complexMatrixVecMul T x i‖ := by
    rw [norm_mul, norm_inv]
    have hnorm : ‖((r ^ i.val : ℝ) : ℂ)‖ = r ^ i.val :=
      Complex.norm_of_nonneg (le_of_lt hpow_pos)
    rw [hnorm]
  rw [hscale]
  have hsum_norm :
      ‖complexMatrixVecMul T x i‖ ≤ ∑ j : Fin n, ‖T i j‖ * ‖x j‖ := by
    unfold complexMatrixVecMul
    calc
      ‖∑ j : Fin n, T i j * x j‖
          ≤ ∑ j : Fin n, ‖T i j * x j‖ := norm_sum_le _ _
      _ = ∑ j : Fin n, ‖T i j‖ * ‖x j‖ := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact norm_mul (T i j) (x j)
  let μ : ℝ :=
    complexVecInfNorm (fun i : Fin n => (((r ^ i.val : ℝ) : ℂ)⁻¹ * x i))
  have hμ_nonneg : 0 ≤ μ := complexVecInfNorm_nonneg _
  have hcoord :
      ∀ j : Fin n, ‖x j‖ ≤ μ * r ^ j.val := by
    intro j
    exact complexVecWeightedInfNorm_coord_le hr x j
  have hsum_bound :
      (∑ j : Fin n, ‖T i j‖ * ‖x j‖) ≤
        ∑ j : Fin n, ‖T i j‖ * (μ * r ^ j.val) := by
    apply Finset.sum_le_sum
    intro j _hj
    exact mul_le_mul_of_nonneg_left (hcoord j) (norm_nonneg (T i j))
  have hsum_factor :
      (∑ j : Fin n, ‖T i j‖ * (μ * r ^ j.val)) =
        μ * ∑ j : Fin n, ‖T i j‖ * r ^ j.val := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hrow_mu :
      μ * (∑ j : Fin n, ‖T i j‖ * r ^ j.val) ≤ μ * (C * r ^ i.val) :=
    mul_le_mul_of_nonneg_left (hrow i) hμ_nonneg
  calc
    (r ^ i.val)⁻¹ * ‖complexMatrixVecMul T x i‖
        ≤ (r ^ i.val)⁻¹ * (∑ j : Fin n, ‖T i j‖ * ‖x j‖) :=
          mul_le_mul_of_nonneg_left hsum_norm hinv_nonneg
    _ ≤ (r ^ i.val)⁻¹ *
          (∑ j : Fin n, ‖T i j‖ * (μ * r ^ j.val)) :=
          mul_le_mul_of_nonneg_left hsum_bound hinv_nonneg
    _ = (r ^ i.val)⁻¹ *
          (μ * ∑ j : Fin n, ‖T i j‖ * r ^ j.val) := by
          rw [hsum_factor]
    _ ≤ (r ^ i.val)⁻¹ * (μ * (C * r ^ i.val)) :=
          mul_le_mul_of_nonneg_left hrow_mu hinv_nonneg
    _ = C * μ := by
          field_simp [ne_of_gt hpow_pos]

/-- Total strict-upper-triangular mass used to make the off-diagonal part
    small in Higham Problem 6.8's weighted-sup proof. -/
noncomputable def complexMatrixStrictUpperMass {n : ℕ} (T : CMatrix n n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then ‖T i j‖ else 0

lemma complexMatrixStrictUpperMass_nonneg {n : ℕ} (T : CMatrix n n) :
    0 ≤ complexMatrixStrictUpperMass T := by
  unfold complexMatrixStrictUpperMass
  apply Finset.sum_nonneg
  intro i _hi
  apply Finset.sum_nonneg
  intro j _hj
  by_cases hij : i < j
  · simp [hij]
  · simp [hij]

lemma complexMatrixStrictUpperRowSum_le_mass {n : ℕ} (T : CMatrix n n)
    (i : Fin n) :
    (∑ j : Fin n, if i < j then ‖T i j‖ else 0) ≤
      complexMatrixStrictUpperMass T := by
  unfold complexMatrixStrictUpperMass
  have h :=
    Finset.single_le_sum
      (s := Finset.univ)
      (a := i)
      (f := fun k : Fin n => ∑ j : Fin n, if k < j then ‖T k j‖ else 0)
      (by
        intro k _hk
        apply Finset.sum_nonneg
        intro j _hj
        by_cases hkj : k < j
        · simp [hkj]
        · simp [hkj])
      (by simp)
  simpa using h

lemma spectralRadiusScale_pos_le_one {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ) :
    0 < δ / (M + δ) ∧ δ / (M + δ) ≤ 1 := by
  have hden_pos : 0 < M + δ := add_pos_of_nonneg_of_pos hM hδ
  constructor
  · exact div_pos hδ hden_pos
  · rw [div_le_one₀ hden_pos]
    exact le_add_of_nonneg_left hM

lemma spectralRadiusScale_mul_mass_le_delta {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 < δ) :
    (δ / (M + δ)) * M ≤ δ := by
  have hden_pos : 0 < M + δ := add_pos_of_nonneg_of_pos hM hδ
  rw [div_mul_eq_mul_div]
  rw [div_le_iff₀ hden_pos]
  nlinarith [mul_nonneg (le_of_lt hδ) hM]

lemma complexMatrixUpperTriangular_weighted_row_bound
    {n : ℕ} {T : CMatrix n n} {ρ δ r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hupper : ∀ i j : Fin n, j < i → T i j = 0)
    (hdiag : ∀ i : Fin n, ‖T i i‖ ≤ ρ)
    (hoff : r * complexMatrixStrictUpperMass T ≤ δ) :
    ∀ i : Fin n,
      (∑ j : Fin n, ‖T i j‖ * r ^ j.val) ≤ (ρ + δ) * r ^ i.val := by
  intro i
  have hpow_nonneg : 0 ≤ r ^ i.val := pow_nonneg hr0 _
  let diagTerm : Fin n → ℝ := fun j => if j = i then ρ * r ^ i.val else 0
  let offTerm : Fin n → ℝ :=
    fun j => (r * r ^ i.val) * (if i < j then ‖T i j‖ else 0)
  have hterm :
      ∀ j : Fin n, ‖T i j‖ * r ^ j.val ≤ diagTerm j + offTerm j := by
    intro j
    by_cases hji_eq : j = i
    · have hdiag_mul := mul_le_mul_of_nonneg_right (hdiag i) hpow_nonneg
      simpa [diagTerm, offTerm, hji_eq] using hdiag_mul
    · by_cases hij : i < j
      · have hweight := geomWeight_later_le hr0 hr1 hij
        have hnorm_nonneg : 0 ≤ ‖T i j‖ := norm_nonneg _
        have hmul := mul_le_mul_of_nonneg_left hweight hnorm_nonneg
        have hrew : ‖T i j‖ * (r * r ^ i.val) =
            (r * r ^ i.val) * ‖T i j‖ := by ring
        simp [diagTerm, offTerm, hji_eq, hij]
        nlinarith
      · have hlt : j < i := by
          exact lt_of_le_of_ne (not_lt.mp hij) hji_eq
        have hzero : T i j = 0 := hupper i j hlt
        simp [diagTerm, offTerm, hji_eq, hij, hzero]
  have hsum_terms :
      (∑ j : Fin n, ‖T i j‖ * r ^ j.val) ≤
        ∑ j : Fin n, (diagTerm j + offTerm j) := by
    exact Finset.sum_le_sum (fun j _hj => hterm j)
  have hsum_split :
      (∑ j : Fin n, (diagTerm j + offTerm j)) =
        (∑ j : Fin n, diagTerm j) + ∑ j : Fin n, offTerm j := by
    exact Finset.sum_add_distrib
  have hdiag_sum : (∑ j : Fin n, diagTerm j) = ρ * r ^ i.val := by
    simp [diagTerm]
  have hoff_sum :
      (∑ j : Fin n, offTerm j) =
        (r * r ^ i.val) *
          (∑ j : Fin n, if i < j then ‖T i j‖ else 0) := by
    simp [offTerm, Finset.mul_sum]
  have hoff_row :=
    complexMatrixStrictUpperRowSum_le_mass T i
  have hfactor_nonneg : 0 ≤ r * r ^ i.val := mul_nonneg hr0 hpow_nonneg
  have hoff_le_mass :
      (r * r ^ i.val) *
          (∑ j : Fin n, if i < j then ‖T i j‖ else 0) ≤
        (r * r ^ i.val) * complexMatrixStrictUpperMass T :=
    mul_le_mul_of_nonneg_left hoff_row hfactor_nonneg
  have hoff_to_delta :
      (r * r ^ i.val) * complexMatrixStrictUpperMass T ≤
        δ * r ^ i.val := by
    nlinarith
  calc
    (∑ j : Fin n, ‖T i j‖ * r ^ j.val)
        ≤ ∑ j : Fin n, (diagTerm j + offTerm j) := hsum_terms
    _ = (ρ * r ^ i.val) +
          (r * r ^ i.val) *
            (∑ j : Fin n, if i < j then ‖T i j‖ else 0) := by
          rw [hsum_split, hdiag_sum, hoff_sum]
    _ ≤ (ρ * r ^ i.val) + (r * r ^ i.val) *
          complexMatrixStrictUpperMass T :=
          add_le_add_right hoff_le_mass _
    _ ≤ (ρ * r ^ i.val) + δ * r ^ i.val :=
          add_le_add_right hoff_to_delta _
    _ = (ρ + δ) * r ^ i.val := by ring

/-- Higham Problem 6.8, triangular-coordinate analytic core: for an upper
    triangular coordinate matrix whose diagonal entries have modulus at most
    `ρ`, the weighted infinity norm with
    `r = δ / (strictUpperMass + δ)` gives a subordinate bound `ρ + δ`. -/
theorem complexMatrixUpperTriangular_weighted_subordinate_bound_of_delta
    {n : ℕ} (T : CMatrix n n) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hupper : ∀ i j : Fin n, j < i → T i j = 0)
    (hdiag : ∀ i : Fin n, ‖T i i‖ ≤ ρ) :
    let M := complexMatrixStrictUpperMass T
    let r := δ / (M + δ)
    MixedSubordinateMatrixBound
      (complexVecWeightedInfNorm (n := n) r)
      (complexVecWeightedInfNorm (n := n) r)
      T (ρ + δ) := by
  dsimp
  let M := complexMatrixStrictUpperMass T
  let r := δ / (M + δ)
  have hM : 0 ≤ M := complexMatrixStrictUpperMass_nonneg T
  have hr_bounds := spectralRadiusScale_pos_le_one hM hδ
  have hrpos : 0 < r := by
    simpa [r, M] using hr_bounds.1
  have hr0 : 0 ≤ r := le_of_lt hrpos
  have hr1 : r ≤ 1 := by
    simpa [r, M] using hr_bounds.2
  have hoff : r * complexMatrixStrictUpperMass T ≤ δ := by
    simpa [r, M] using spectralRadiusScale_mul_mass_le_delta hM hδ
  have hrow :
      ∀ i : Fin n,
        (∑ j : Fin n, ‖T i j‖ * r ^ j.val) ≤ (ρ + δ) * r ^ i.val :=
    complexMatrixUpperTriangular_weighted_row_bound
      hr0 hr1 hupper hdiag hoff
  exact complexVecWeightedInfNorm_matrix_bound_of_weighted_rows
    hrpos (add_nonneg hρ (le_of_lt hδ)) T hrow

/-- Higham Problem 6.8, checked conditional form: once `A` is put into an
    upper triangular coordinate model with diagonal bounded by `ρ`, the
    constructed pullback weighted norm has a least subordinate matrix value
    at most `ρ + δ`.  The remaining global algebraic dependency is the
    triangularization/diagonal-eigenvalue bridge producing the model from an
    arbitrary complex matrix and its spectral radius. -/
theorem exists_mixedSubordinateMatrixNormValue_le_of_upperTriangular_similarity
    {n : ℕ} (hn : 0 < n) (A T : CMatrix n n)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (toTri : ComplexVectorMap n n)
    (htoTri : IsComplexVectorMapLinear toTri)
    (htoTri_inj_zero : ∀ x : CVec n, toTri x = 0 → x = 0)
    (hconj : ∀ x : CVec n,
      toTri (complexMatrixVecMul A x) = complexMatrixVecMul T (toTri x))
    (hupper : ∀ i j : Fin n, j < i → T i j = 0)
    (hdiag : ∀ i : Fin n, ‖T i i‖ ≤ ρ) :
    ∃ (ν : CVec n → ℝ) (c : ℝ),
      IsComplexVectorNorm ν ∧
        IsMixedSubordinateMatrixNormValue ν ν A c ∧ c ≤ ρ + δ := by
  let M := complexMatrixStrictUpperMass T
  let r := δ / (M + δ)
  let μ : CVec n → ℝ := complexVecWeightedInfNorm (n := n) r
  have hM : 0 ≤ M := complexMatrixStrictUpperMass_nonneg T
  have hrpos : 0 < r := by
    simpa [r, M] using (spectralRadiusScale_pos_le_one hM hδ).1
  have hμ : IsComplexVectorNorm μ :=
    complexVecWeightedInfNorm_isComplexVectorNorm hrpos
  have hTbound : MixedSubordinateMatrixBound μ μ T (ρ + δ) := by
    simpa [μ, r, M] using
      complexMatrixUpperTriangular_weighted_subordinate_bound_of_delta
        T hρ hδ hupper hdiag
  let ν : CVec n → ℝ := fun x => μ (toTri x)
  have hν : IsComplexVectorNorm ν :=
    complexVectorNorm_pullback_of_linear_injective hμ htoTri htoTri_inj_zero
  have hAbound : MixedSubordinateMatrixBound ν ν A (ρ + δ) := by
    simpa [ν] using
      mixedSubordinateMatrixBound_pullback (S := toTri) hconj hTbound
  obtain ⟨c, hc⟩ :=
    exists_mixedSubordinateMatrixNormValue_of_bound_nonempty
      hn hν hν A hAbound
  exact ⟨ν, c, hν, hc, hc.2 (ρ + δ) hAbound⟩

/-- Higham Problem 6.8, source-facing matrix form: if `ρ` is represented as
    the maximum eigenvalue modulus of a nonempty complex square matrix, then
    every positive `δ` admits a consistent matrix norm value at most `ρ + δ`.
    The proof triangularizes the concrete matrix map, bounds the diagonal
    through the original spectral-radius carrier, and then applies the
    weighted-infinity pullback construction. -/
theorem exists_mixedSubordinateMatrixNormValue_le_of_maxComplexMatrixEigenvalueModulus
    {n : ℕ} (hn : 0 < n) (A : CMatrix n n)
    {ρ δ : ℝ} (hρmax : IsMaxComplexMatrixEigenvalueModulus A ρ)
    (hδ : 0 < δ) :
    ∃ (ν : CVec n → ℝ) (c : ℝ),
      IsComplexVectorNorm ν ∧
        IsMixedSubordinateMatrixNormValue ν ν A c ∧ c ≤ ρ + δ := by
  obtain ⟨b, hb⟩ := exists_complexMatrixVecMul_blockTriangular_toMatrix A
  let L : CVec n →ₗ[ℂ] CVec n :=
    complexVectorMapLinearMap (complexMatrixVecMul A) (complexMatrixVecMul_linear A)
  let T : CMatrix n n := complexMatrixVecMulCoordinateMatrix A b
  let toTri : ComplexVectorMap n n := fun x i => b.equivFun x i
  have hρ_nonneg : 0 ≤ ρ := by
    rcases hρmax.1 with ⟨lam, _x, _hxne, _hAx, rfl⟩
    exact norm_nonneg lam
  have htoTri : IsComplexVectorMapLinear toTri := by
    constructor
    · intro x y
      have hadd : complexVecAdd x y = x + y := by
        ext k
        rfl
      ext i
      rw [hadd]
      have hmap := congrFun (b.equivFun.map_add x y) i
      change (b.equivFun (x + y)) i = (b.equivFun x) i + (b.equivFun y) i
      exact hmap
    · intro a x
      ext i
      have hsmul : complexVecSMul a x = a • x := by
        ext k
        rfl
      rw [hsmul]
      have hmap := congrFun (b.equivFun.map_smul a x) i
      change (b.equivFun (a • x)) i = a * (b.equivFun x) i
      exact hmap
  have htoTri_inj_zero : ∀ x : CVec n, toTri x = 0 → x = 0 := by
    intro x hx
    apply b.equivFun.injective
    ext i
    simpa [toTri] using congrFun hx i
  have hconj : ∀ x : CVec n,
      toTri (complexMatrixVecMul A x) = complexMatrixVecMul T (toTri x) := by
    intro x
    ext i
    have hmat := congrFun
      (LinearMap.toMatrix_mulVec_repr
        (v₁ := b) (v₂ := b) L x) i
    calc
      toTri (complexMatrixVecMul A x) i = b.repr (L x) i := rfl
      _ = ∑ j : Fin n, (LinearMap.toMatrix b b L) i j * b.repr x j := by
            simpa [Matrix.mulVec, dotProduct] using hmat.symm
      _ = complexMatrixVecMul T (toTri x) i := by
            rfl
  have hupperBlock : (show Matrix (Fin n) (Fin n) ℂ from T).BlockTriangular id := by
    simpa [T] using hb
  have hupper : ∀ i j : Fin n, j < i → T i j = 0 := by
    intro i j hji
    exact hupperBlock (i := i) (j := j) hji
  have hdiag : ∀ i : Fin n, ‖T i i‖ ≤ ρ := by
    intro i
    have hmemT :
        ‖T i i‖ ∈ ComplexMatrixEigenvalueModulusSet T :=
      upperTriangular_diagonal_mem_complexMatrixEigenvalueModulusSet T hupperBlock i
    have hmemTcoord :
        ‖complexMatrixVecMulCoordinateMatrix A b i i‖ ∈
          ComplexMatrixEigenvalueModulusSet
            (complexMatrixVecMulCoordinateMatrix A b) := by
      simpa [T] using hmemT
    have hmemA :
        ‖complexMatrixVecMulCoordinateMatrix A b i i‖ ∈
          ComplexMatrixEigenvalueModulusSet A :=
      complexMatrixEigenvalueModulusSet_coordinateMatrix_subset A b hmemTcoord
    simpa [T] using hρmax.2 _ hmemA
  exact
    exists_mixedSubordinateMatrixNormValue_le_of_upperTriangular_similarity
      hn A T hρ_nonneg hδ toTri htoTri htoTri_inj_zero hconj hupper hdiag

/-- Higham Problem 6.8, contractive corollary: if the represented spectral
    radius is strictly less than `1`, then some consistent matrix norm value is
    strictly less than `1`. -/
theorem exists_mixedSubordinateMatrixNormValue_lt_one_of_maxComplexMatrixEigenvalueModulus_lt_one
    {n : ℕ} (hn : 0 < n) (A : CMatrix n n)
    {ρ : ℝ} (hρmax : IsMaxComplexMatrixEigenvalueModulus A ρ)
    (hρlt : ρ < 1) :
    ∃ (ν : CVec n → ℝ) (c : ℝ),
      IsComplexVectorNorm ν ∧ IsMixedSubordinateMatrixNormValue ν ν A c ∧ c < 1 := by
  let δ : ℝ := (1 - ρ) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  obtain ⟨ν, c, hν, hc, hcle⟩ :=
    exists_mixedSubordinateMatrixNormValue_le_of_maxComplexMatrixEigenvalueModulus
      hn A hρmax hδ
  refine ⟨ν, c, hν, hc, ?_⟩
  have hsum_lt : ρ + δ < 1 := by
    dsimp [δ]
    linarith
  exact lt_of_le_of_lt hcle hsum_lt
end NumStability
