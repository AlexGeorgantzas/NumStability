import HighamBench.P11Definitions

namespace HighamBench

open scoped Matrix.Norms.L2Operator

private lemma p11_l2_opNorm_transpose {m n : ℕ}
    (A : P11RectMatrix m n) :
    ‖A.transpose‖ = ‖A‖ := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial A]
  exact Matrix.l2_opNorm_conjTranspose A

private lemma p11RectDefectCore_norm_le {m k : ℕ}
    (A dA : P11RectMatrix m k) (R : P11Matrix k) :
    p11OpNorm2 (p11RectDefectCore A dA R) ≤
      p11OpNorm2 (p11RectNormalEquationResidual A R) +
        2 * p11RectOpNorm2 A * p11RectOpNorm2 dA +
          p11RectOpNorm2 dA ^ 2 := by
  let E := p11RectNormalEquationResidual A R
  let X := p11RectMatMul (p11RectTranspose A) dA
  let Y := p11RectMatMul (p11RectTranspose dA) A
  let Z := p11RectMatMul (p11RectTranspose dA) dA
  have hX : ‖X‖ ≤ ‖A‖ * ‖dA‖ := by
    dsimp [X, p11RectMatMul, p11RectTranspose]
    simpa only [p11_l2_opNorm_transpose] using Matrix.l2_opNorm_mul A.transpose dA
  have hY : ‖Y‖ ≤ ‖dA‖ * ‖A‖ := by
    dsimp [Y, p11RectMatMul, p11RectTranspose]
    simpa only [p11_l2_opNorm_transpose] using Matrix.l2_opNorm_mul dA.transpose A
  have hZ : ‖Z‖ ≤ ‖dA‖ * ‖dA‖ := by
    dsimp [Z, p11RectMatMul, p11RectTranspose]
    simpa only [p11_l2_opNorm_transpose] using Matrix.l2_opNorm_mul dA.transpose dA
  have htriangle : ‖E - X - Y - Z‖ ≤ ‖E‖ + ‖X‖ + ‖Y‖ + ‖Z‖ := by
    calc
      ‖E - X - Y - Z‖ ≤ ‖E - X - Y‖ + ‖Z‖ := norm_sub_le _ _
      _ ≤ (‖E - X‖ + ‖Y‖) + ‖Z‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ ((‖E‖ + ‖X‖) + ‖Y‖) + ‖Z‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = ‖E‖ + ‖X‖ + ‖Y‖ + ‖Z‖ := by ring
  change ‖E - X - Y - Z‖ ≤
    ‖E‖ + 2 * ‖A‖ * ‖dA‖ + ‖dA‖ ^ 2
  calc
    ‖E - X - Y - Z‖ ≤ ‖E‖ + ‖X‖ + ‖Y‖ + ‖Z‖ := htriangle
    _ ≤ ‖E‖ + (‖A‖ * ‖dA‖) + (‖dA‖ * ‖A‖) +
        (‖dA‖ * ‖dA‖) := by gcongr
    _ = ‖E‖ + 2 * ‖A‖ * ‖dA‖ + ‖dA‖ ^ 2 := by ring

private lemma p11C1_nonneg (m k : ℕ) : 0 ≤ p11C1 m k := by
  by_cases hk : k = 1
  · simp [p11C1, hk]
  · rw [p11C1, if_neg hk]
    positivity

private lemma p11C2_nonneg (m k : ℕ) (hk : 0 < k) : 0 ≤ p11C2 m k := by
  by_cases hk1 : k = 1
  · rw [p11C2, if_pos hk1]
    positivity
  · rw [p11C2, if_neg hk1]
    have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hfactor : 0 ≤ (7 / 2 : ℝ) * (k : ℝ) - 3 / 2 := by nlinarith
    calc
      (7 / 2 : ℝ) * (m : ℝ) * (k : ℝ) ^ 2 -
            (3 / 2 : ℝ) * (m : ℝ) * (k : ℝ) + 16 * (k : ℝ) =
          (m : ℝ) * (k : ℝ) *
              ((7 / 2 : ℝ) * (k : ℝ) - 3 / 2) + 16 * (k : ℝ) := by ring
      _ ≥ 0 := by positivity

set_option maxHeartbeats 1000000 in
private lemma p11_orthogonality_scalar_bound
    (e a r s rBound inverseBound c1 c2 c3 c4 f g h d en x z : ℝ)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (ha0 : 0 ≤ a) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hrBound0 : 0 ≤ rBound) (hinverseBound0 : 0 ≤ inverseBound)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3)
    (hf : 0 ≤ f) (hg : 0 ≤ g) (hh : 0 ≤ h)
    (hd0 : 0 ≤ d) (hen0 : 0 ≤ en) (hx0 : 0 ≤ x)
    (hc4 : c4 = c2 + 2 * c1)
    (hr : r ≤ rBound) (hs : s ≤ inverseBound)
    (ha : a ≤ (1 + c3 * e) * r + h * e ^ 2)
    (hd : d ≤ c1 * a * e + f * e ^ 2)
    (hen : en ≤ c2 * a ^ 2 * e + g * e ^ 2)
    (hx : x ≤ en + 2 * a * d + d ^ 2)
    (hz : z ≤ s ^ 2 * x) :
    z ≤ c4 * (r * s) ^ 2 * e +
      inverseBound ^ 2 *
        (c4 * (2 * rBound * (c3 * rBound + h) +
                    (c3 * rBound + h) ^ 2) +
          (g + 2 * a * f + (c1 * a + f) ^ 2)) * e ^ 2 := by
  have hc4nonneg : 0 ≤ c4 := by rw [hc4]; positivity
  have he2 : e ^ 2 ≤ e := by nlinarith
  have hmultC : c3 * e * r ≤ c3 * e * rBound := by
    exact mul_le_mul_of_nonneg_left hr (by positivity)
  have hhe : h * e ^ 2 ≤ h * e :=
    mul_le_mul_of_nonneg_left he2 hh
  have haSlope : a ≤ r + (c3 * rBound + h) * e := by
    nlinarith
  have hslope0 : 0 ≤ c3 * rBound + h := by positivity
  have haSlope0 : 0 ≤ r + (c3 * rBound + h) * e := by positivity
  have haSq0 : a ^ 2 ≤ (r + (c3 * rBound + h) * e) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haSlope) (add_nonneg haSlope0 ha0)]
  have hslopeSq :
      (c3 * rBound + h) ^ 2 * e ^ 2 ≤ (c3 * rBound + h) ^ 2 * e :=
    mul_le_mul_of_nonneg_left he2 (sq_nonneg _)
  have haSq :
      a ^ 2 ≤ r ^ 2 +
        (2 * rBound * (c3 * rBound + h) + (c3 * rBound + h) ^ 2) * e := by
    nlinarith [mul_nonneg (mul_nonneg (by nlinarith : 0 ≤ 2 * (rBound - r)) hslope0) he0]
  have hdCoarse : d ≤ (c1 * a + f) * e := by
    have hfe : f * e ^ 2 ≤ f * e := mul_le_mul_of_nonneg_left he2 hf
    nlinarith
  have hcross : 2 * a * d ≤ 2 * a * (c1 * a * e + f * e ^ 2) := by
    exact mul_le_mul_of_nonneg_left hd (by positivity)
  have hdSq : d ^ 2 ≤ ((c1 * a + f) * e) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdCoarse)
      (add_nonneg (by positivity : 0 ≤ (c1 * a + f) * e) hd0)]
  have hxBound :
      x ≤ c4 * a ^ 2 * e +
        (g + 2 * a * f + (c1 * a + f) ^ 2) * e ^ 2 := by
    rw [hc4]
    nlinarith
  have hLeading :
      c4 * a ^ 2 * e ≤
        c4 * r ^ 2 * e +
          c4 * (2 * rBound * (c3 * rBound + h) +
            (c3 * rBound + h) ^ 2) * e ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg hc4nonneg he0)
      (sub_nonneg.mpr haSq)]
  have hxFinal :
      x ≤ c4 * r ^ 2 * e +
        (c4 * (2 * rBound * (c3 * rBound + h) +
                    (c3 * rBound + h) ^ 2) +
          (g + 2 * a * f + (c1 * a + f) ^ 2)) * e ^ 2 := by
    nlinarith
  have hrem0 :
      0 ≤ c4 * (2 * rBound * (c3 * rBound + h) +
                    (c3 * rBound + h) ^ 2) +
          (g + 2 * a * f + (c1 * a + f) ^ 2) := by positivity
  have hsSq : s ^ 2 ≤ inverseBound ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (add_nonneg hinverseBound0 hs0)]
  have hscale : s ^ 2 * x ≤ s ^ 2 *
      (c4 * r ^ 2 * e +
        (c4 * (2 * rBound * (c3 * rBound + h) +
                    (c3 * rBound + h) ^ 2) +
          (g + 2 * a * f + (c1 * a + f) ^ 2)) * e ^ 2) :=
    mul_le_mul_of_nonneg_left hxFinal (sq_nonneg s)
  have hremScale :
      s ^ 2 *
          ((c4 * (2 * rBound * (c3 * rBound + h) +
                    (c3 * rBound + h) ^ 2) +
            (g + 2 * a * f + (c1 * a + f) ^ 2)) * e ^ 2) ≤
      inverseBound ^ 2 *
          ((c4 * (2 * rBound * (c3 * rBound + h) +
                    (c3 * rBound + h) ^ 2) +
            (g + 2 * a * f + (c1 * a + f) ^ 2)) * e ^ 2) :=
    mul_le_mul_of_nonneg_right hsSq (mul_nonneg hrem0 (sq_nonneg e))
  -- Preserve the actual norms in the first-order term, and use the uniform
  -- bounds only for the second-order remainder.
  have hfirstRewrite :
      s ^ 2 * (c4 * r ^ 2 * e) = c4 * (r * s) ^ 2 * e := by ring
  nlinarith [hscale, hremScale, hfirstRewrite]

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
  let S : P11Matrix (k.val + 1) := (family.run epsilonM).leadingInverse k
  let D : P11RectMatrix m (k.val + 1) :=
    p11Theorem1FactorizationResidual family epsilonM k
  let E : P11Matrix (k.val + 1) := p11RectNormalEquationResidual A R
  let C : P11Matrix (k.val + 1) := p11RectDefectCore A D R

  have hQR : Q * R = A + D := by
    dsimp [D, p11Theorem1FactorizationResidual, p11RectMatMul]
    abel
  have hRS : R * S = (1 : P11Matrix (k.val + 1)) := by
    simpa only [R, S, p11MatMul, p11Identity] using
      (family.run epsilonM).leading_right_inverse k
  have hQ : Q = (A + D) * S := by
    calc
      Q = Q * (1 : P11Matrix (k.val + 1)) := (Matrix.mul_one Q).symm
      _ = Q * (R * S) := by rw [hRS]
      _ = (Q * R) * S := (Matrix.mul_assoc Q R S).symm
      _ = (A + D) * S := by rw [hQR]
  have hRST : S.transpose * R.transpose = (1 : P11Matrix (k.val + 1)) := by
    rw [← Matrix.transpose_mul, hRS, Matrix.transpose_one]
  have hOne : (1 : P11Matrix (k.val + 1)) =
      (S.transpose * R.transpose) * (R * S) := by
    rw [hRST, hRS, Matrix.one_mul]
  have hCore : C =
      R.transpose * R - (A + D).transpose * (A + D) := by
    dsimp [C, p11RectDefectCore, p11RectNormalEquationResidual,
      p11MatMul, p11Transpose, p11RectMatMul, p11RectTranspose]
    rw [Matrix.transpose_add]
    simp only [Matrix.add_mul, Matrix.mul_add]
    abel
  have hDefect : p11RectOrthogonalityDefect Q =
      S.transpose * C * S := by
    change (1 : P11Matrix (k.val + 1)) - Q.transpose * Q =
      S.transpose * C * S
    rw [hQ, hOne, Matrix.transpose_mul, hCore]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]

  have hz : p11OpNorm2 (p11RectOrthogonalityDefect Q) ≤
      p11OpNorm2 S ^ 2 * p11OpNorm2 C := by
    rw [hDefect]
    change ‖S.transpose * C * S‖ ≤ ‖S‖ ^ 2 * ‖C‖
    calc
      ‖S.transpose * C * S‖ ≤ ‖S.transpose * C‖ * ‖S‖ :=
        Matrix.l2_opNorm_mul (S.transpose * C) S
      _ ≤ (‖S.transpose‖ * ‖C‖) * ‖S‖ := by
        gcongr
        exact Matrix.l2_opNorm_mul S.transpose C
      _ = ‖S‖ ^ 2 * ‖C‖ := by
        rw [p11_l2_opNorm_transpose]
        ring
  have hx : p11OpNorm2 C ≤ p11OpNorm2 E +
      2 * p11RectOpNorm2 A * p11RectOpNorm2 D + p11RectOpNorm2 D ^ 2 := by
    simpa only [C, E] using p11RectDefectCore_norm_le A D R

  have hOneRadius : epsilonM.1 ≤ 1 :=
    hRadius.trans (min_le_left _ _)
  have hNormRadius : epsilonM.1 ≤ family.normBoundRadius := by
    calc
      epsilonM.1 ≤ p11Theorem1OrthogonalityRadius family analysis := hRadius
      _ ≤ family.normBoundRadius := by
        unfold p11Theorem1OrthogonalityRadius
        exact (min_le_right _ _).trans (min_le_left _ _)
  have hAnalysisRadius : epsilonM.1 ≤ analysis.radius := by
    calc
      epsilonM.1 ≤ p11Theorem1OrthogonalityRadius family analysis := hRadius
      _ ≤ analysis.radius := by
        unfold p11Theorem1OrthogonalityRadius
        exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr : p11OpNorm2 R ≤ family.rNormBound k := by
    simpa only [R] using family.r_norm_bound epsilonM hNormRadius k
  have hs : p11OpNorm2 S ≤ family.inverseNormBound k := by
    simpa only [S] using family.inverse_norm_bound epsilonM hNormRadius k
  have ha : p11RectOpNorm2 A ≤
      (1 + p11C3 m (k.val + 1) * epsilonM.1) * p11OpNorm2 R +
        analysis.reverseNormSecondOrderCoeff k * epsilonM.1 ^ 2 := by
    simpa only [A, R] using analysis.reverse_norm_bound epsilonM hAnalysisRadius k
  have hd : p11RectOpNorm2 D ≤
      p11C1 m (k.val + 1) * p11RectOpNorm2 A * epsilonM.1 +
        analysis.factorizationSecondOrderCoeff k * epsilonM.1 ^ 2 := by
    simpa only [D, A] using analysis.factorization_bound epsilonM hAnalysisRadius k
  have hen : p11OpNorm2 E ≤
      p11C2 m (k.val + 1) * p11RectOpNorm2 A ^ 2 * epsilonM.1 +
        analysis.normalEquationSecondOrderCoeff k * epsilonM.1 ^ 2 := by
    simpa only [E, A, R] using
      analysis.normal_equation_bound epsilonM hAnalysisRadius k
  have hc1 : 0 ≤ p11C1 m (k.val + 1) := p11C1_nonneg _ _
  have hc2 : 0 ≤ p11C2 m (k.val + 1) :=
    p11C2_nonneg _ _ (Nat.succ_pos k.val)
  have hc3 : 0 ≤ p11C3 m (k.val + 1) := by
    rw [p11C3]
    positivity

  have hscalar := p11_orthogonality_scalar_bound
    epsilonM.1
    (p11RectOpNorm2 A) (p11OpNorm2 R) (p11OpNorm2 S)
    (family.rNormBound k) (family.inverseNormBound k)
    (p11C1 m (k.val + 1)) (p11C2 m (k.val + 1))
    (p11C3 m (k.val + 1)) (p11C4 m (k.val + 1))
    (analysis.factorizationSecondOrderCoeff k)
    (analysis.normalEquationSecondOrderCoeff k)
    (analysis.reverseNormSecondOrderCoeff k)
    (p11RectOpNorm2 D) (p11OpNorm2 E) (p11OpNorm2 C)
    (p11OpNorm2 (p11RectOrthogonalityDefect Q))
    epsilonM.property.le hOneRadius
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (family.r_norm_bound_nonneg k) (family.inverse_norm_bound_nonneg k)
    hc1 hc2 hc3
    (analysis.factorization_second_order_nonneg k)
    (analysis.normal_equation_second_order_nonneg k)
    (analysis.reverse_norm_second_order_nonneg k)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (by rfl) hr hs ha hd hen hx hz
  simpa only [Q, R, S, A, p11Kappa2,
    p11Theorem1OrthogonalityRemainderCoeff] using hscalar

end HighamBench
