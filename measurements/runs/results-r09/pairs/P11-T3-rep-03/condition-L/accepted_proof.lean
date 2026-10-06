import HighamBench.P11Definitions

open scoped Matrix.Norms.L2Operator

namespace HighamBench

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
  intro epsilonM hRadius k
  let A : P11RectMatrix m (k.val + 1) := p11ColumnPrefix family.A k
  let Q : P11RectMatrix m (k.val + 1) :=
    p11ColumnPrefix (family.run epsilonM).Q k
  let R : P11Matrix (k.val + 1) :=
    p11LeadingBlock (family.run epsilonM).R k
  let Rinv : P11Matrix (k.val + 1) :=
    (family.run epsilonM).leadingInverse k
  let dA : P11RectMatrix m (k.val + 1) :=
    p11Theorem1FactorizationResidual family epsilonM k
  let E : P11Matrix (k.val + 1) :=
    p11RectNormalEquationResidual A R
  let C : P11Matrix (k.val + 1) := p11RectDefectCore A dA R
  have hQR : p11RectMatMul Q R = A + dA := by
    simp only [Q, R, A, dA, p11Theorem1FactorizationResidual]
    abel
  have hRinv : p11MatMul (k.val + 1) R Rinv =
      p11Identity (k.val + 1) := by
    exact (family.run epsilonM).leading_right_inverse k
  have hQ : Q = p11RectMatMul (A + dA) Rinv := by
    calc
      Q = p11RectMatMul Q (p11Identity (k.val + 1)) := by
        simp [p11RectMatMul, p11Identity]
      _ = p11RectMatMul Q (p11MatMul (k.val + 1) R Rinv) := by rw [hRinv]
      _ = p11RectMatMul (p11RectMatMul Q R) Rinv := by
        simp [p11RectMatMul, p11MatMul, Matrix.mul_assoc]
      _ = p11RectMatMul (A + dA) Rinv := by rw [hQR]
  have hC : C = E - p11RectMatMul (p11RectTranspose A) dA -
        p11RectMatMul (p11RectTranspose dA) A -
        p11RectMatMul (p11RectTranspose dA) dA := by
    rfl
  have hDefect : p11RectOrthogonalityDefect Q =
      p11MatMul (k.val + 1) (p11Transpose Rinv)
        (p11MatMul (k.val + 1) C Rinv) := by
    have hRinv' : R * Rinv = 1 := by
      simpa [p11MatMul, p11Identity] using hRinv
    have hUnit : Rinv.transpose * (R.transpose * R) * Rinv = 1 := by
      calc
        Rinv.transpose * (R.transpose * R) * Rinv =
            (R * Rinv).transpose * (R * Rinv) := by
              simp only [Matrix.transpose_mul]
              noncomm_ring
        _ = 1 := by rw [hRinv']; simp
    rw [hQ, hC]
    simp only [p11RectOrthogonalityDefect, p11RectNormalEquationResidual,
      E, p11Identity, p11RectMatMul, p11MatMul, p11RectTranspose, p11Transpose]
    rw [Matrix.transpose_mul]
    simp only [Matrix.transpose_add]
    rw [← hUnit]
    simp only [Matrix.add_mul, Matrix.mul_add]
    noncomm_ring
    <;> simp only [Matrix.mul_assoc]
    <;> abel
  rw [show p11RectOrthogonalityDefect
      (p11ColumnPrefix (family.run epsilonM).Q k) =
      p11RectOrthogonalityDefect Q by rfl, hDefect]
  let e : ℝ := epsilonM.1
  let a : ℝ := p11RectOpNorm2 A
  let r : ℝ := p11OpNorm2 R
  let rinv : ℝ := p11OpNorm2 Rinv
  let da : ℝ := p11RectOpNorm2 dA
  let enorm : ℝ := p11OpNorm2 E
  let cnorm : ℝ := p11OpNorm2 C
  let c1 : ℝ := p11C1 m (k.val + 1)
  let c2 : ℝ := p11C2 m (k.val + 1)
  let c3 : ℝ := p11C3 m (k.val + 1)
  let c4 : ℝ := p11C4 m (k.val + 1)
  let f2 : ℝ := analysis.factorizationSecondOrderCoeff k
  let n2 : ℝ := analysis.normalEquationSecondOrderCoeff k
  let v2 : ℝ := analysis.reverseNormSecondOrderCoeff k
  let rBound : ℝ := family.rNormBound k
  let inverseBound : ℝ := family.inverseNormBound k
  let normSlope : ℝ := c3 * rBound + v2
  let aSquareRemainder : ℝ :=
    2 * rBound * normSlope + normSlope ^ 2
  let coreRemainder : ℝ :=
    n2 + 2 * a * f2 + (c1 * a + f2) ^ 2
  have he_pos : 0 < e := epsilonM.2
  have he : 0 ≤ e := le_of_lt he_pos
  have he_one : e ≤ 1 := by
    exact hRadius.trans (by simp [p11Theorem1OrthogonalityRadius])
  have he_sq : e ^ 2 ≤ e := by nlinarith [mul_nonneg he (sub_nonneg.mpr he_one)]
  have hNormRadius : e ≤ family.normBoundRadius := by
    exact hRadius.trans (by simp [p11Theorem1OrthogonalityRadius])
  have hAnalysisRadius : e ≤ analysis.radius := by
    exact hRadius.trans (by simp [p11Theorem1OrthogonalityRadius])
  have ha : 0 ≤ a := norm_nonneg _
  have hr : 0 ≤ r := norm_nonneg _
  have hrinv : 0 ≤ rinv := norm_nonneg _
  have hda : 0 ≤ da := norm_nonneg _
  have henorm : 0 ≤ enorm := norm_nonneg _
  have hcnorm : 0 ≤ cnorm := norm_nonneg _
  have hc1 : 0 ≤ c1 := by
    dsimp [c1]
    unfold p11C1
    split <;> positivity
  have hc2 : 0 ≤ c2 := by
    dsimp [c2]
    unfold p11C2
    split
    · positivity
    · have hk_nat : 1 ≤ k.val + 1 := Nat.succ_le_succ (Nat.zero_le k.val)
      have hk_one : (1 : ℝ) ≤ ((k.val + 1 : ℕ) : ℝ) := by exact_mod_cast hk_nat
      have hlin : 0 ≤ 7 * ((k.val + 1 : ℕ) : ℝ) - 3 := by linarith
      have hp : 0 ≤ (1 / 2 : ℝ) * (m : ℝ) * ((k.val + 1 : ℕ) : ℝ) *
          (7 * ((k.val + 1 : ℕ) : ℝ) - 3) := by positivity
      have hlast : 0 ≤ 16 * ((k.val + 1 : ℕ) : ℝ) := by positivity
      nlinarith
  have hc3 : 0 ≤ c3 := by
    dsimp [c3]
    exact mul_nonneg (by norm_num) hc2
  have hc4 : 0 ≤ c4 := by
    dsimp [c4]
    exact add_nonneg hc2 (mul_nonneg (by norm_num) hc1)
  have hf2 : 0 ≤ f2 := analysis.factorization_second_order_nonneg k
  have hn2 : 0 ≤ n2 := analysis.normal_equation_second_order_nonneg k
  have hv2 : 0 ≤ v2 := analysis.reverse_norm_second_order_nonneg k
  have hrBound : 0 ≤ rBound := family.r_norm_bound_nonneg k
  have hinverseBound : 0 ≤ inverseBound := family.inverse_norm_bound_nonneg k
  have hnormSlope : 0 ≤ normSlope := by
    exact add_nonneg (mul_nonneg hc3 hrBound) hv2
  have haSquareRemainder : 0 ≤ aSquareRemainder := by
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hrBound) hnormSlope)
      (sq_nonneg normSlope)
  have hcoreRemainder : 0 ≤ coreRemainder := by
    exact add_nonneg
      (add_nonneg hn2 (mul_nonneg (mul_nonneg (by norm_num) ha) hf2))
      (sq_nonneg (c1 * a + f2))
  have hr_le : r ≤ rBound := by
    simpa [r, R] using family.r_norm_bound epsilonM hNormRadius k
  have hrinv_le : rinv ≤ inverseBound := by
    simpa [rinv, Rinv] using family.inverse_norm_bound epsilonM hNormRadius k
  have hfactor : da ≤ c1 * a * e + f2 * e ^ 2 := by
    simpa [da, dA, c1, a, A, e, f2] using
      analysis.factorization_bound epsilonM hAnalysisRadius k
  have hnormal : enorm ≤ c2 * a ^ 2 * e + n2 * e ^ 2 := by
    simpa [enorm, E, c2, a, A, R, e, n2] using
      analysis.normal_equation_bound epsilonM hAnalysisRadius k
  have hreverse : a ≤ (1 + c3 * e) * r + v2 * e ^ 2 := by
    simpa [a, A, c3, e, r, R, v2] using
      analysis.reverse_norm_bound epsilonM hAnalysisRadius k
  have htranspose (X : P11Matrix (k.val + 1)) :
      p11OpNorm2 X.transpose = p11OpNorm2 X := by
    simpa [p11OpNorm2, Matrix.conjTranspose_apply] using
      (Matrix.l2_opNorm_conjTranspose X)
  have hrectTranspose (X : P11RectMatrix m (k.val + 1)) :
      p11RectOpNorm2 X.transpose = p11RectOpNorm2 X := by
    simpa [p11RectOpNorm2, Matrix.conjTranspose_apply] using
      (Matrix.l2_opNorm_conjTranspose X)
  have hC_triangle : cnorm ≤ enorm + 2 * a * da + da ^ 2 := by
    have hsub : cnorm ≤ enorm +
        p11OpNorm2 (p11RectMatMul (p11RectTranspose A) dA) +
        p11OpNorm2 (p11RectMatMul (p11RectTranspose dA) A) +
        p11OpNorm2 (p11RectMatMul (p11RectTranspose dA) dA) := by
      dsimp [cnorm, enorm]
      rw [hC]
      have h1 : p11OpNorm2
          (E - p11RectMatMul (p11RectTranspose A) dA) ≤
          p11OpNorm2 E +
            p11OpNorm2 (p11RectMatMul (p11RectTranspose A) dA) := by
        exact norm_sub_le _ _
      have h2 : p11OpNorm2
          (E - p11RectMatMul (p11RectTranspose A) dA -
            p11RectMatMul (p11RectTranspose dA) A) ≤
          p11OpNorm2 (E - p11RectMatMul (p11RectTranspose A) dA) +
            p11OpNorm2 (p11RectMatMul (p11RectTranspose dA) A) := by
        exact norm_sub_le _ _
      have h3 : p11OpNorm2
          (E - p11RectMatMul (p11RectTranspose A) dA -
            p11RectMatMul (p11RectTranspose dA) A -
            p11RectMatMul (p11RectTranspose dA) dA) ≤
          p11OpNorm2
              (E - p11RectMatMul (p11RectTranspose A) dA -
                p11RectMatMul (p11RectTranspose dA) A) +
            p11OpNorm2 (p11RectMatMul (p11RectTranspose dA) dA) := by
        exact norm_sub_le _ _
      linarith
    have hAdA : p11OpNorm2 (p11RectMatMul (p11RectTranspose A) dA) ≤ a * da := by
      calc
        p11OpNorm2 (p11RectMatMul (p11RectTranspose A) dA) ≤
            p11RectOpNorm2 (p11RectTranspose A) * p11RectOpNorm2 dA := by
              simpa [p11OpNorm2, p11RectOpNorm2, p11RectMatMul,
                p11RectTranspose] using Matrix.l2_opNorm_mul A.transpose dA
        _ = a * da := by simp [p11RectTranspose, hrectTranspose, a, da]
    have hdAA : p11OpNorm2 (p11RectMatMul (p11RectTranspose dA) A) ≤ da * a := by
      calc
        p11OpNorm2 (p11RectMatMul (p11RectTranspose dA) A) ≤
            p11RectOpNorm2 (p11RectTranspose dA) * p11RectOpNorm2 A := by
              simpa [p11OpNorm2, p11RectOpNorm2, p11RectMatMul,
                p11RectTranspose] using Matrix.l2_opNorm_mul dA.transpose A
        _ = da * a := by simp [p11RectTranspose, hrectTranspose, a, da]
    have hdAdA : p11OpNorm2 (p11RectMatMul (p11RectTranspose dA) dA) ≤ da * da := by
      calc
        p11OpNorm2 (p11RectMatMul (p11RectTranspose dA) dA) ≤
            p11RectOpNorm2 (p11RectTranspose dA) * p11RectOpNorm2 dA := by
              simpa [p11OpNorm2, p11RectOpNorm2, p11RectMatMul,
                p11RectTranspose] using Matrix.l2_opNorm_mul dA.transpose dA
        _ = da * da := by simp [p11RectTranspose, hrectTranspose, da]
    calc
      cnorm ≤ enorm +
          p11OpNorm2 (p11RectMatMul (p11RectTranspose A) dA) +
          p11OpNorm2 (p11RectMatMul (p11RectTranspose dA) A) +
          p11OpNorm2 (p11RectMatMul (p11RectTranspose dA) dA) := hsub
      _ ≤ enorm + (a * da) + (da * a) + (da * da) := by gcongr
      _ = enorm + 2 * a * da + da ^ 2 := by ring
  have hc4_eq : c4 = c2 + 2 * c1 := by rfl
  have hfactor_linear : da ≤ (c1 * a + f2) * e := by
    calc
      da ≤ c1 * a * e + f2 * e ^ 2 := hfactor
      _ ≤ c1 * a * e + f2 * e := by gcongr
      _ = (c1 * a + f2) * e := by ring
  have hfactor_linear_nonneg : 0 ≤ (c1 * a + f2) * e := by positivity
  have hfactor_square : da ^ 2 ≤ ((c1 * a + f2) * e) ^ 2 :=
    (sq_le_sq₀ hda hfactor_linear_nonneg).2 hfactor_linear
  have hfactor_cross : 2 * a * da ≤
      2 * a * (c1 * a * e + f2 * e ^ 2) := by
    exact mul_le_mul_of_nonneg_left hfactor (mul_nonneg (by norm_num) ha)
  have hcore_bound : cnorm ≤ c4 * a ^ 2 * e + coreRemainder * e ^ 2 := by
    calc
      cnorm ≤ enorm + 2 * a * da + da ^ 2 := hC_triangle
      _ ≤ (c2 * a ^ 2 * e + n2 * e ^ 2) +
          2 * a * (c1 * a * e + f2 * e ^ 2) +
          ((c1 * a + f2) * e) ^ 2 := by
            gcongr
      _ = c4 * a ^ 2 * e + coreRemainder * e ^ 2 := by
            rw [hc4_eq]
            dsimp [coreRemainder]
            ring
  have hv2e : v2 * e ^ 2 ≤ v2 * e := by gcongr
  have hc3r : c3 * r ≤ c3 * rBound :=
    mul_le_mul_of_nonneg_left hr_le hc3
  have ha_linear : a ≤ r + normSlope * e := by
    calc
      a ≤ (1 + c3 * e) * r + v2 * e ^ 2 := hreverse
      _ ≤ (1 + c3 * e) * r + v2 * e := by gcongr
      _ = r + (c3 * r + v2) * e := by ring
      _ ≤ r + (c3 * rBound + v2) * e := by gcongr
      _ = r + normSlope * e := by rfl
  have ha_linear_nonneg : 0 ≤ r + normSlope * e := by positivity
  have ha_square0 : a ^ 2 ≤ (r + normSlope * e) ^ 2 :=
    (sq_le_sq₀ ha ha_linear_nonneg).2 ha_linear
  have hrslope : r * normSlope ≤ rBound * normSlope :=
    mul_le_mul_of_nonneg_right hr_le hnormSlope
  have hcross_slope : 2 * r * normSlope * e ≤
      2 * rBound * normSlope * e := by gcongr
  have hslope_square : normSlope ^ 2 * e ^ 2 ≤ normSlope ^ 2 * e := by gcongr
  have ha_square : a ^ 2 ≤ r ^ 2 + aSquareRemainder * e := by
    calc
      a ^ 2 ≤ (r + normSlope * e) ^ 2 := ha_square0
      _ = r ^ 2 + 2 * r * normSlope * e + normSlope ^ 2 * e ^ 2 := by ring
      _ ≤ r ^ 2 + 2 * rBound * normSlope * e + normSlope ^ 2 * e := by gcongr
      _ = r ^ 2 + aSquareRemainder * e := by
        dsimp [aSquareRemainder]
        ring
  have hcore_r : cnorm ≤ c4 * r ^ 2 * e +
      (c4 * aSquareRemainder + coreRemainder) * e ^ 2 := by
    calc
      cnorm ≤ c4 * a ^ 2 * e + coreRemainder * e ^ 2 := hcore_bound
      _ ≤ c4 * (r ^ 2 + aSquareRemainder * e) * e +
          coreRemainder * e ^ 2 := by gcongr
      _ = c4 * r ^ 2 * e +
          (c4 * aSquareRemainder + coreRemainder) * e ^ 2 := by ring
  have hinner : p11OpNorm2 (p11MatMul (k.val + 1) C Rinv) ≤
      cnorm * rinv := by
    simpa [p11OpNorm2, p11MatMul, cnorm, rinv] using
      Matrix.l2_opNorm_mul C Rinv
  have houter : p11OpNorm2
      (p11MatMul (k.val + 1) (p11Transpose Rinv)
        (p11MatMul (k.val + 1) C Rinv)) ≤
      p11OpNorm2 (p11Transpose Rinv) *
        p11OpNorm2 (p11MatMul (k.val + 1) C Rinv) := by
    simpa [p11OpNorm2, p11MatMul, p11Transpose] using
      Matrix.l2_opNorm_mul Rinv.transpose (C * Rinv)
  have hmatrix : p11OpNorm2
      (p11MatMul (k.val + 1) (p11Transpose Rinv)
        (p11MatMul (k.val + 1) C Rinv)) ≤ rinv ^ 2 * cnorm := by
    calc
      p11OpNorm2
          (p11MatMul (k.val + 1) (p11Transpose Rinv)
            (p11MatMul (k.val + 1) C Rinv)) ≤
          p11OpNorm2 (p11Transpose Rinv) *
            p11OpNorm2 (p11MatMul (k.val + 1) C Rinv) := houter
      _ = rinv * p11OpNorm2 (p11MatMul (k.val + 1) C Rinv) := by
        rw [show p11OpNorm2 (p11Transpose Rinv) = rinv by
          simpa [p11Transpose, rinv] using htranspose Rinv]
      _ ≤ rinv * (cnorm * rinv) := by gcongr
      _ = rinv ^ 2 * cnorm := by ring
  have hrinv_square : rinv ^ 2 ≤ inverseBound ^ 2 :=
    (sq_le_sq₀ hrinv hinverseBound).2 hrinv_le
  have hremainder_base : 0 ≤ c4 * aSquareRemainder + coreRemainder :=
    add_nonneg (mul_nonneg hc4 haSquareRemainder) hcoreRemainder
  calc
    p11OpNorm2
        (p11MatMul (k.val + 1) (p11Transpose Rinv)
          (p11MatMul (k.val + 1) C Rinv)) ≤
        rinv ^ 2 * cnorm := hmatrix
    _ ≤ rinv ^ 2 *
        (c4 * r ^ 2 * e +
          (c4 * aSquareRemainder + coreRemainder) * e ^ 2) := by gcongr
    _ = c4 * (r * rinv) ^ 2 * e +
        rinv ^ 2 * (c4 * aSquareRemainder + coreRemainder) * e ^ 2 := by ring
    _ ≤ c4 * (r * rinv) ^ 2 * e +
        inverseBound ^ 2 *
          (c4 * aSquareRemainder + coreRemainder) * e ^ 2 := by gcongr
    _ = p11C4 m (k.val + 1) *
              p11Kappa2 (p11LeadingBlock (family.run epsilonM).R k)
                  ((family.run epsilonM).leadingInverse k) ^ 2 *
            epsilonM.1 +
          p11Theorem1OrthogonalityRemainderCoeff family analysis k *
            epsilonM.1 ^ 2 := by
      rfl

end HighamBench
