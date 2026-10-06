import HighamBench.P11Definitions

namespace HighamBench

open scoped Matrix.Norms.L2Operator

private lemma p11C1_nonneg (m k : ℕ) : 0 ≤ p11C1 m k := by
  unfold p11C1
  split
  · norm_num
  · positivity

private lemma p11C2_succ_nonneg (m k : ℕ) : 0 ≤ p11C2 m (k + 1) := by
  by_cases hk : k = 0
  · subst k
    simp only [p11C2, Nat.zero_add, if_pos rfl]
    exact add_nonneg (Nat.cast_nonneg _) (by norm_num)
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
    have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have hkp : (0 : ℝ) ≤ (k + 1 : ℕ) := by positivity
    rw [p11C2, if_neg (by omega)]
    have hfactor :
        ((7 : ℝ) / 2) * (m : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 2 -
              ((3 : ℝ) / 2) * (m : ℝ) * ((k + 1 : ℕ) : ℝ) +
              16 * ((k + 1 : ℕ) : ℝ) =
          ((m : ℝ) * ((k + 1 : ℕ) : ℝ) / 2) *
              (7 * ((k + 1 : ℕ) : ℝ) - 3) +
            16 * ((k + 1 : ℕ) : ℝ) := by ring
    rw [hfactor]
    have : (0 : ℝ) ≤ 7 * ((k + 1 : ℕ) : ℝ) - 3 := by
      push_cast
      nlinarith
    positivity

private lemma p11C3_succ_nonneg (m k : ℕ) : 0 ≤ p11C3 m (k + 1) := by
  unfold p11C3
  positivity [p11C2_succ_nonneg m k]

private lemma p11C4_succ_nonneg (m k : ℕ) : 0 ≤ p11C4 m (k + 1) := by
  unfold p11C4
  positivity [p11C1_nonneg m (k + 1), p11C2_succ_nonneg m k]

private lemma p11_rect_defect_identity {m k : ℕ}
    (A dA Q : P11RectMatrix m k) (R Rinv : P11Matrix k)
    (hfactor : p11RectMatMul Q R - A = dA)
    (hright : p11MatMul k R Rinv = p11Identity k) :
    p11RectOrthogonalityDefect Q =
      p11MatMul k
        (p11MatMul k (p11Transpose Rinv) (p11RectDefectCore A dA R)) Rinv := by
  have hQR : p11RectMatMul Q R = A + dA := by
    have h := sub_eq_iff_eq_add.mp hfactor
    simpa [add_comm] using h
  have hQ : Q = p11RectMatMul (A + dA) Rinv := by
    calc
      Q = p11RectMatMul Q (p11Identity k) := by
        simp [p11RectMatMul, p11Identity]
      _ = p11RectMatMul Q (p11MatMul k R Rinv) := by rw [hright]
      _ = p11RectMatMul (p11RectMatMul Q R) Rinv := by
        simp [p11RectMatMul, p11MatMul, Matrix.mul_assoc]
      _ = p11RectMatMul (A + dA) Rinv := by rw [hQR]
  have hcore :
      p11RectDefectCore A dA R =
        p11MatMul k (p11Transpose R) R -
          p11RectMatMul (p11RectTranspose (A + dA)) (A + dA) := by
    simp only [p11RectDefectCore, p11RectNormalEquationResidual]
    simp only [p11RectTranspose, Matrix.transpose_add]
    simp only [p11MatMul, p11RectMatMul, p11Transpose]
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    abel
  have htranspose :
      p11MatMul k (p11Transpose Rinv) (p11Transpose R) = p11Identity k := by
    have h := congrArg Matrix.transpose hright
    simpa [p11MatMul, p11Transpose, p11Identity, Matrix.transpose_mul] using h
  have hright' : R * Rinv = (1 : P11Matrix k) := by
    simpa [p11MatMul, p11Identity] using hright
  have htranspose' : Rinv.transpose * R.transpose = (1 : P11Matrix k) := by
    simpa [p11MatMul, p11Transpose, p11Identity] using htranspose
  have hQtranspose :
      Q.transpose = Rinv.transpose * (A + dA).transpose := by
    have h := congrArg Matrix.transpose hQ
    simpa [p11RectMatMul, Matrix.transpose_mul] using h
  rw [hcore]
  symm
  calc
    p11MatMul k
          (p11MatMul k (p11Transpose Rinv)
            (p11MatMul k (p11Transpose R) R -
              p11RectMatMul (p11RectTranspose (A + dA)) (A + dA))) Rinv =
        p11Identity k -
          p11RectMatMul
            (p11RectMatMul (p11Transpose Rinv) (p11RectTranspose (A + dA)))
            (p11RectMatMul (A + dA) Rinv) := by
      simp only [p11MatMul, p11RectMatMul, p11Transpose, p11RectTranspose,
        p11Identity]
      rw [mul_sub, sub_mul]
      rw [← Matrix.mul_assoc (Rinv.transpose) (R.transpose) R]
      rw [htranspose', one_mul, hright']
      simp only [Matrix.mul_assoc]
    _ = p11RectOrthogonalityDefect Q := by
      rw [← hQ]
      simp only [p11RectOrthogonalityDefect, p11RectMatMul,
        p11RectTranspose, p11Transpose, p11Identity]
      rw [hQtranspose]

private lemma p11_opNorm_nonneg {k : ℕ} (A : P11Matrix k) :
    0 ≤ p11OpNorm2 A := by
  unfold p11OpNorm2
  exact norm_nonneg _

private lemma p11_rectOpNorm_nonneg {m k : ℕ} (A : P11RectMatrix m k) :
    0 ≤ p11RectOpNorm2 A := by
  unfold p11RectOpNorm2
  exact norm_nonneg _

private lemma p11_rectOpNorm_transpose {m k : ℕ} (A : P11RectMatrix m k) :
    p11RectOpNorm2 (p11RectTranspose A) = p11RectOpNorm2 A := by
  have h := Matrix.l2_opNorm_conjTranspose
    (A := (A : Matrix (Fin m) (Fin k) ℝ))
  have heq :
      Matrix.conjTranspose (A : Matrix (Fin m) (Fin k) ℝ) =
        Matrix.transpose A := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [heq] at h
  simpa [p11RectOpNorm2, p11RectTranspose] using h

private lemma p11_rectMatMul_opNorm_le {m k p : ℕ}
    (A : P11RectMatrix m k) (B : P11RectMatrix k p) :
    p11RectOpNorm2 (p11RectMatMul A B) ≤
      p11RectOpNorm2 A * p11RectOpNorm2 B := by
  simpa [p11RectOpNorm2, p11RectMatMul] using
    (Matrix.l2_opNorm_mul
      (A := (A : Matrix (Fin m) (Fin k) ℝ))
      (B := (B : Matrix (Fin k) (Fin p) ℝ)))

private lemma p11_matMul_opNorm_le {k : ℕ} (A B : P11Matrix k) :
    p11OpNorm2 (p11MatMul k A B) ≤ p11OpNorm2 A * p11OpNorm2 B := by
  simpa [p11OpNorm2, p11MatMul] using
    (Matrix.l2_opNorm_mul
      (A := (A : Matrix (Fin k) (Fin k) ℝ))
      (B := (B : Matrix (Fin k) (Fin k) ℝ)))

private lemma p11_opNorm_transpose {k : ℕ} (A : P11Matrix k) :
    p11OpNorm2 (p11Transpose A) = p11OpNorm2 A := by
  simpa [p11OpNorm2, p11RectOpNorm2] using
    (p11_rectOpNorm_transpose (A := A))

private lemma p11_rectProduct_opNorm_le {m k : ℕ}
    (A B : P11RectMatrix m k) :
    p11OpNorm2 (p11RectMatMul (p11RectTranspose A) B) ≤
      p11RectOpNorm2 A * p11RectOpNorm2 B := by
  have h := p11_rectMatMul_opNorm_le (p11RectTranspose A) B
  rw [p11_rectOpNorm_transpose] at h
  simpa [p11OpNorm2, p11RectOpNorm2] using h

private lemma p11_rect_defect_core_norm_le {m k : ℕ}
    (A dA : P11RectMatrix m k) (R : P11Matrix k) :
    p11OpNorm2 (p11RectDefectCore A dA R) ≤
      p11OpNorm2 (p11RectNormalEquationResidual A R) +
        2 * p11RectOpNorm2 A * p11RectOpNorm2 dA +
          p11RectOpNorm2 dA ^ 2 := by
  let E := p11RectNormalEquationResidual A R
  let X := p11RectMatMul (p11RectTranspose A) dA
  let Y := p11RectMatMul (p11RectTranspose dA) A
  let Z := p11RectMatMul (p11RectTranspose dA) dA
  have hX : p11OpNorm2 X ≤ p11RectOpNorm2 A * p11RectOpNorm2 dA := by
    exact p11_rectProduct_opNorm_le A dA
  have hY : p11OpNorm2 Y ≤ p11RectOpNorm2 dA * p11RectOpNorm2 A := by
    exact p11_rectProduct_opNorm_le dA A
  have hZ : p11OpNorm2 Z ≤ p11RectOpNorm2 dA * p11RectOpNorm2 dA := by
    exact p11_rectProduct_opNorm_le dA dA
  have htri : p11OpNorm2 (((E - X) - Y) - Z) ≤
      ((p11OpNorm2 E + p11OpNorm2 X) + p11OpNorm2 Y) + p11OpNorm2 Z := by
    unfold p11OpNorm2
    calc
      ‖((E - X) - Y) - Z‖ ≤ ‖(E - X) - Y‖ + ‖Z‖ := norm_sub_le _ _
      _ ≤ (‖E - X‖ + ‖Y‖) + ‖Z‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ ((‖E‖ + ‖X‖) + ‖Y‖) + ‖Z‖ := by
        gcongr
        exact norm_sub_le _ _
  change p11OpNorm2 (((E - X) - Y) - Z) ≤ _
  calc
    p11OpNorm2 (((E - X) - Y) - Z) ≤
        ((p11OpNorm2 E + p11OpNorm2 X) + p11OpNorm2 Y) + p11OpNorm2 Z := htri
    _ ≤ ((p11OpNorm2 E +
          p11RectOpNorm2 A * p11RectOpNorm2 dA) +
          p11RectOpNorm2 dA * p11RectOpNorm2 A) +
          p11RectOpNorm2 dA * p11RectOpNorm2 dA := by gcongr
    _ = p11OpNorm2 E + 2 * p11RectOpNorm2 A * p11RectOpNorm2 dA +
          p11RectOpNorm2 dA ^ 2 := by ring

theorem p11_t3_orthogonality_defect_bound {m n : ℕ}
    (family : P11CGSPTheorem1Family m n)
    (analysis : P11Theorem1ResidualAsymptotics family) :
    ∀ epsilonM : P11PositiveEpsilon,
      epsilonM.1 ≤ p11Theorem1OrthogonalityRadius family analysis →
      ∀ k : Fin n,
      p11OpNorm2
          (p11RectOrthogonalityDefect
            (p11ColumnPrefix (family.run epsilonM).Q k)) ≤
        p11C4 m (k.val + 1) *
              p11Kappa2 (p11LeadingBlock (family.run epsilonM).R k)
                  ((family.run epsilonM).leadingInverse k) ^ 2 *
            epsilonM.1 +
          p11Theorem1OrthogonalityRemainderCoeff family analysis k *
            epsilonM.1 ^ 2 := by
  -- PROOF_START P11-T3-H001
  intro epsilonM hepsilon k
  rcases le_min_iff.mp hepsilon with ⟨he_one, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨he_norm_radius, hepsilon⟩
  rcases le_min_iff.mp hepsilon with ⟨_he_condition_radius, he_analysis_radius⟩
  let A : P11RectMatrix m (k.val + 1) := p11ColumnPrefix family.A k
  let Q : P11RectMatrix m (k.val + 1) :=
    p11ColumnPrefix (family.run epsilonM).Q k
  let R : P11Matrix (k.val + 1) := p11LeadingBlock (family.run epsilonM).R k
  let Rinv : P11Matrix (k.val + 1) := (family.run epsilonM).leadingInverse k
  let dA : P11RectMatrix m (k.val + 1) :=
    p11Theorem1FactorizationResidual family epsilonM k
  let E : P11Matrix (k.val + 1) := p11RectNormalEquationResidual A R
  let C : P11Matrix (k.val + 1) := p11RectDefectCore A dA R
  let e : ℝ := epsilonM.1
  let a : ℝ := p11RectOpNorm2 A
  let r : ℝ := p11OpNorm2 R
  let ri : ℝ := p11OpNorm2 Rinv
  let d : ℝ := p11RectOpNorm2 dA
  let z : ℝ := p11OpNorm2 C
  let c1 : ℝ := p11C1 m (k.val + 1)
  let c2 : ℝ := p11C2 m (k.val + 1)
  let c3 : ℝ := p11C3 m (k.val + 1)
  let c4 : ℝ := p11C4 m (k.val + 1)
  let f : ℝ := analysis.factorizationSecondOrderCoeff k
  let ne : ℝ := analysis.normalEquationSecondOrderCoeff k
  let rev : ℝ := analysis.reverseNormSecondOrderCoeff k
  let rb : ℝ := family.rNormBound k
  let ib : ℝ := family.inverseNormBound k
  let slope : ℝ := c3 * rb + rev
  let asqRem : ℝ := 2 * rb * slope + slope ^ 2
  let coreRem : ℝ := ne + 2 * a * f + (c1 * a + f) ^ 2

  have he_pos : 0 < e := epsilonM.property
  have he_nonneg : 0 ≤ e := le_of_lt he_pos
  have he_sq_le : e ^ 2 ≤ e := by nlinarith
  have ha : 0 ≤ a := p11_rectOpNorm_nonneg A
  have hr : 0 ≤ r := p11_opNorm_nonneg R
  have hri : 0 ≤ ri := p11_opNorm_nonneg Rinv
  have hd : 0 ≤ d := p11_rectOpNorm_nonneg dA
  have hz : 0 ≤ z := p11_opNorm_nonneg C
  have hc1 : 0 ≤ c1 := p11C1_nonneg m (k.val + 1)
  have hc2 : 0 ≤ c2 := p11C2_succ_nonneg m k.val
  have hc3 : 0 ≤ c3 := p11C3_succ_nonneg m k.val
  have hc4 : 0 ≤ c4 := p11C4_succ_nonneg m k.val
  have hf : 0 ≤ f := analysis.factorization_second_order_nonneg k
  have hne : 0 ≤ ne := analysis.normal_equation_second_order_nonneg k
  have hrev : 0 ≤ rev := analysis.reverse_norm_second_order_nonneg k
  have hrb : 0 ≤ rb := family.r_norm_bound_nonneg k
  have hib : 0 ≤ ib := family.inverse_norm_bound_nonneg k
  have hslope : 0 ≤ slope := by
    dsimp [slope]
    positivity
  have hasqRem : 0 ≤ asqRem := by
    dsimp [asqRem]
    positivity
  have hcoreRem : 0 ≤ coreRem := by
    dsimp [coreRem]
    positivity

  have hfactor_bound : d ≤ c1 * a * e + f * e ^ 2 := by
    simpa [d, dA, c1, a, A, e] using
      analysis.factorization_bound epsilonM he_analysis_radius k
  have hnormal_bound : p11OpNorm2 E ≤ c2 * a ^ 2 * e + ne * e ^ 2 := by
    simpa [E, c2, a, A, R, e, ne] using
      analysis.normal_equation_bound epsilonM he_analysis_radius k
  have hreverse_bound : a ≤ (1 + c3 * e) * r + rev * e ^ 2 := by
    simpa [a, A, c3, e, r, R, rev] using
      analysis.reverse_norm_bound epsilonM he_analysis_radius k
  have hr_bound : r ≤ rb := by
    simpa [r, R, rb] using family.r_norm_bound epsilonM he_norm_radius k
  have hri_bound : ri ≤ ib := by
    simpa [ri, Rinv, ib] using family.inverse_norm_bound epsilonM he_norm_radius k

  have hresidual_identity : p11RectMatMul Q R - A = dA := by
    rfl
  have hright_inverse : p11MatMul (k.val + 1) R Rinv =
      p11Identity (k.val + 1) := by
    simpa [R, Rinv] using (family.run epsilonM).leading_right_inverse k
  have hdefect_identity :=
    p11_rect_defect_identity A dA Q R Rinv hresidual_identity hright_inverse
  have hinner :
      p11OpNorm2 (p11MatMul (k.val + 1) (p11Transpose Rinv) C) ≤ ri * z := by
    calc
      p11OpNorm2 (p11MatMul (k.val + 1) (p11Transpose Rinv) C) ≤
          p11OpNorm2 (p11Transpose Rinv) * p11OpNorm2 C :=
        p11_matMul_opNorm_le _ _
      _ = ri * z := by rw [p11_opNorm_transpose]
  have hdefect_norm : p11OpNorm2 (p11RectOrthogonalityDefect Q) ≤ ri ^ 2 * z := by
    rw [hdefect_identity]
    calc
      p11OpNorm2
          (p11MatMul (k.val + 1)
            (p11MatMul (k.val + 1) (p11Transpose Rinv) C) Rinv) ≤
          p11OpNorm2 (p11MatMul (k.val + 1) (p11Transpose Rinv) C) *
            p11OpNorm2 Rinv := p11_matMul_opNorm_le _ _
      _ ≤ (ri * z) * ri := by
        exact mul_le_mul_of_nonneg_right hinner hri
      _ = ri ^ 2 * z := by ring

  have hcore_raw :
      z ≤ p11OpNorm2 E + 2 * a * d + d ^ 2 := by
    simpa [z, C, E, a, d] using p11_rect_defect_core_norm_le A dA R
  have hfactor_linear : d ≤ (c1 * a + f) * e := by
    have hf_sq : f * e ^ 2 ≤ f * e :=
      mul_le_mul_of_nonneg_left he_sq_le hf
    nlinarith [hfactor_bound]
  have hfactor_linear_nonneg : 0 ≤ (c1 * a + f) * e := by positivity
  have hfactor_sq : d ^ 2 ≤ (c1 * a + f) ^ 2 * e ^ 2 := by
    calc
      d ^ 2 ≤ ((c1 * a + f) * e) ^ 2 :=
        (sq_le_sq₀ hd hfactor_linear_nonneg).mpr hfactor_linear
      _ = (c1 * a + f) ^ 2 * e ^ 2 := by ring
  have hfactor_twice :
      2 * a * d ≤ 2 * a * (c1 * a * e + f * e ^ 2) := by
    exact mul_le_mul_of_nonneg_left hfactor_bound (by positivity)
  have hcore_bound : z ≤ c4 * a ^ 2 * e + coreRem * e ^ 2 := by
    calc
      z ≤ p11OpNorm2 E + 2 * a * d + d ^ 2 := hcore_raw
      _ ≤ (c2 * a ^ 2 * e + ne * e ^ 2) +
            2 * a * (c1 * a * e + f * e ^ 2) +
              (c1 * a + f) ^ 2 * e ^ 2 := by
        gcongr
      _ = c4 * a ^ 2 * e + coreRem * e ^ 2 := by
        dsimp [c4, coreRem]
        rw [p11C4]
        ring

  have hc3r : c3 * r ≤ c3 * rb :=
    mul_le_mul_of_nonneg_left hr_bound hc3
  have hc3re : c3 * r * e ≤ c3 * rb * e :=
    mul_le_mul_of_nonneg_right hc3r he_nonneg
  have hrev_sq : rev * e ^ 2 ≤ rev * e :=
    mul_le_mul_of_nonneg_left he_sq_le hrev
  have ha_linear : a ≤ r + slope * e := by
    calc
      a ≤ (1 + c3 * e) * r + rev * e ^ 2 := hreverse_bound
      _ = (r + c3 * r * e) + rev * e ^ 2 := by ring
      _ ≤ (r + c3 * rb * e) + rev * e :=
        add_le_add (add_le_add_right hc3re r) hrev_sq
      _ = r + (c3 * rb + rev) * e := by ring
      _ = r + slope * e := by rfl
  have hright_linear_nonneg : 0 ≤ r + slope * e := by positivity
  have ha_square : a ^ 2 ≤ r ^ 2 + asqRem * e := by
    calc
      a ^ 2 ≤ (r + slope * e) ^ 2 :=
        (sq_le_sq₀ ha hright_linear_nonneg).mpr ha_linear
      _ = r ^ 2 + 2 * r * slope * e + slope ^ 2 * e ^ 2 := by ring
      _ ≤ r ^ 2 + 2 * rb * slope * e + slope ^ 2 * e := by
        gcongr
      _ = r ^ 2 + asqRem * e := by
        dsimp [asqRem]
        ring

  have hcore_with_r :
      z ≤ c4 * r ^ 2 * e + (c4 * asqRem + coreRem) * e ^ 2 := by
    calc
      z ≤ c4 * a ^ 2 * e + coreRem * e ^ 2 := hcore_bound
      _ ≤ c4 * (r ^ 2 + asqRem * e) * e + coreRem * e ^ 2 := by
        gcongr
      _ = c4 * r ^ 2 * e + (c4 * asqRem + coreRem) * e ^ 2 := by ring
  have htotal_nonneg : 0 ≤ c4 * asqRem + coreRem := by positivity
  have hri_sq : ri ^ 2 ≤ ib ^ 2 :=
    (sq_le_sq₀ hri hib).mpr hri_bound
  calc
    p11OpNorm2
        (p11RectOrthogonalityDefect
          (p11ColumnPrefix (family.run epsilonM).Q k)) =
        p11OpNorm2 (p11RectOrthogonalityDefect Q) := by rfl
    _ ≤ ri ^ 2 * z := hdefect_norm
    _ ≤ ri ^ 2 *
          (c4 * r ^ 2 * e + (c4 * asqRem + coreRem) * e ^ 2) := by
      exact mul_le_mul_of_nonneg_left hcore_with_r (sq_nonneg ri)
    _ = c4 * (r * ri) ^ 2 * e +
          ri ^ 2 * (c4 * asqRem + coreRem) * e ^ 2 := by ring
    _ ≤ c4 * (r * ri) ^ 2 * e +
          ib ^ 2 * (c4 * asqRem + coreRem) * e ^ 2 := by
      gcongr
    _ = p11C4 m (k.val + 1) *
              p11Kappa2 (p11LeadingBlock (family.run epsilonM).R k)
                  ((family.run epsilonM).leadingInverse k) ^ 2 *
            epsilonM.1 +
          p11Theorem1OrthogonalityRemainderCoeff family analysis k *
            epsilonM.1 ^ 2 := by
      rfl

end HighamBench
