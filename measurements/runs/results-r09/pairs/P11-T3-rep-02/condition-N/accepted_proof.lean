import HighamBench.P11Definitions

open scoped Matrix.Norms.L2Operator

namespace HighamBench

private lemma p11_c1_nonneg (m k : ℕ) : 0 ≤ p11C1 m k := by
  rw [p11C1]
  split_ifs
  · norm_num
  · positivity

private lemma p11_c2_nonneg (m k : ℕ) (hk : 1 ≤ k) : 0 ≤ p11C2 m k := by
  rw [p11C2]
  split_ifs
  · positivity
  · have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hfactor : 0 ≤ (7 / 2 : ℝ) * (k : ℝ) - 3 / 2 := by nlinarith
    have hm : 0 ≤ (m : ℝ) := by positivity
    have hkn : 0 ≤ (k : ℝ) := by positivity
    calc
      (7 / 2 : ℝ) * (m : ℝ) * (k : ℝ) ^ 2 -
            (3 / 2 : ℝ) * (m : ℝ) * (k : ℝ) + 16 * (k : ℝ) =
          (m : ℝ) * (k : ℝ) * ((7 / 2 : ℝ) * (k : ℝ) - 3 / 2) +
            16 * (k : ℝ) := by ring
      _ ≥ 0 := by positivity

private lemma p11_c3_nonneg (m k : ℕ) (hk : 1 ≤ k) : 0 ≤ p11C3 m k := by
  rw [p11C3]
  exact mul_nonneg (by norm_num) (p11_c2_nonneg m k hk)

private lemma p11_c4_nonneg (m k : ℕ) (hk : 1 ≤ k) : 0 ≤ p11C4 m k := by
  rw [p11C4]
  exact add_nonneg (p11_c2_nonneg m k hk)
    (mul_nonneg (by norm_num) (p11_c1_nonneg m k))

private lemma p11_rect_defect_identity {m k : ℕ}
    (A dA Q : P11RectMatrix m k) (R S : P11Matrix k)
    (hdA : dA = p11RectMatMul Q R - A)
    (hRS : p11MatMul k R S = p11Identity k) :
    p11RectOrthogonalityDefect Q =
      p11MatMul k (p11MatMul k (p11Transpose S) (p11RectDefectCore A dA R)) S := by
  have hQ : p11RectMatMul (A + dA) S = Q := by
    change (A + dA) * S = Q
    change dA = Q * R - A at hdA
    change R * S = 1 at hRS
    rw [hdA]
    calc
      (A + (Q * R - A)) * S = (Q * R) * S := by noncomm_ring
      _ = Q * (R * S) := Matrix.mul_assoc _ _ _
      _ = Q := by rw [hRS, Matrix.mul_one]
  change 1 - Q.transpose * Q = S.transpose * p11RectDefectCore A dA R * S
  change R * S = 1 at hRS
  rw [p11RectDefectCore, p11RectNormalEquationResidual, p11MatMul,
    p11RectMatMul, p11Transpose, p11RectTranspose]
  rw [show Q = (A + dA) * S from hQ.symm]
  rw [Matrix.transpose_mul, Matrix.transpose_add]
  have hId : S.transpose * (R.transpose * R) * S = (1 : P11Matrix k) := by
    calc
      S.transpose * (R.transpose * R) * S =
          (S.transpose * R.transpose) * (R * S) := by
            simp only [Matrix.mul_assoc]
      _ = (R * S).transpose * (R * S) := by rw [Matrix.transpose_mul]
      _ = 1 := by rw [hRS, Matrix.transpose_one, Matrix.one_mul]
  calc
    1 - S.transpose * (A.transpose + dA.transpose) * ((A + dA) * S) =
        S.transpose * (R.transpose * R) * S -
          S.transpose * (A.transpose + dA.transpose) * ((A + dA) * S) := by rw [hId]
    _ = S.transpose *
          (R.transpose * R - A.transpose * A - A.transpose * dA -
            dA.transpose * A - dA.transpose * dA) * S := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
            Matrix.mul_assoc]
          abel

private lemma p11_l2_opNorm_transpose {m n : ℕ} (A : P11RectMatrix m n) :
    ‖A.transpose‖ = ‖A‖ := by
  simpa [Matrix.conjTranspose] using Matrix.l2_opNorm_conjTranspose A

private lemma p11_rect_defect_norm_bound {m k : ℕ}
    (A dA Q : P11RectMatrix m k) (R S : P11Matrix k)
    (hdA : dA = p11RectMatMul Q R - A)
    (hRS : p11MatMul k R S = p11Identity k) :
    p11OpNorm2 (p11RectOrthogonalityDefect Q) ≤
      p11OpNorm2 S ^ 2 *
        (p11OpNorm2 (p11RectNormalEquationResidual A R) +
          2 * p11RectOpNorm2 A * p11RectOpNorm2 dA +
          p11RectOpNorm2 dA ^ 2) := by
  rw [p11_rect_defect_identity A dA Q R S hdA hRS]
  change ‖S.transpose * p11RectDefectCore A dA R * S‖ ≤
    ‖S‖ ^ 2 *
      (‖p11RectNormalEquationResidual A R‖ + 2 * ‖A‖ * ‖dA‖ + ‖dA‖ ^ 2)
  have hcore : ‖p11RectDefectCore A dA R‖ ≤
      ‖p11RectNormalEquationResidual A R‖ + 2 * ‖A‖ * ‖dA‖ + ‖dA‖ ^ 2 := by
    rw [p11RectDefectCore, p11RectMatMul, p11RectTranspose]
    have htri :
        ‖p11RectNormalEquationResidual A R - A.transpose * dA - dA.transpose * A -
            dA.transpose * dA‖ ≤
          ‖p11RectNormalEquationResidual A R‖ + ‖A.transpose * dA‖ +
            ‖dA.transpose * A‖ + ‖dA.transpose * dA‖ := by
      calc
        ‖p11RectNormalEquationResidual A R - A.transpose * dA - dA.transpose * A -
            dA.transpose * dA‖ ≤
            ‖p11RectNormalEquationResidual A R - A.transpose * dA - dA.transpose * A‖ +
              ‖dA.transpose * dA‖ := norm_sub_le _ _
        _ ≤ (‖p11RectNormalEquationResidual A R - A.transpose * dA‖ +
              ‖dA.transpose * A‖) + ‖dA.transpose * dA‖ := by
            gcongr
            exact norm_sub_le _ _
        _ ≤ ((‖p11RectNormalEquationResidual A R‖ + ‖A.transpose * dA‖) +
              ‖dA.transpose * A‖) + ‖dA.transpose * dA‖ := by
            gcongr
            exact norm_sub_le _ _
        _ = ‖p11RectNormalEquationResidual A R‖ + ‖A.transpose * dA‖ +
              ‖dA.transpose * A‖ + ‖dA.transpose * dA‖ := by ring
    refine htri.trans ?_
    have hAd : ‖A.transpose * dA‖ ≤ ‖A‖ * ‖dA‖ := by
      simpa [p11_l2_opNorm_transpose A] using Matrix.l2_opNorm_mul A.transpose dA
    have hdA' : ‖dA.transpose * A‖ ≤ ‖dA‖ * ‖A‖ := by
      simpa [p11_l2_opNorm_transpose dA] using Matrix.l2_opNorm_mul dA.transpose A
    have hdd : ‖dA.transpose * dA‖ ≤ ‖dA‖ ^ 2 := by
      simpa [p11_l2_opNorm_transpose dA, pow_two] using
        Matrix.l2_opNorm_mul dA.transpose dA
    nlinarith
  calc
    ‖S.transpose * p11RectDefectCore A dA R * S‖ ≤
        ‖S.transpose * p11RectDefectCore A dA R‖ * ‖S‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ (‖S.transpose‖ * ‖p11RectDefectCore A dA R‖) * ‖S‖ := by
      gcongr
      exact Matrix.l2_opNorm_mul _ _
    _ = ‖S‖ ^ 2 * ‖p11RectDefectCore A dA R‖ := by
      rw [p11_l2_opNorm_transpose S]
      ring
    _ ≤ ‖S‖ ^ 2 *
        (‖p11RectNormalEquationResidual A R‖ + 2 * ‖A‖ * ‖dA‖ +
          ‖dA‖ ^ 2) := by gcongr

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
  rw [p11Theorem1OrthogonalityRadius, le_min_iff, le_min_iff, le_min_iff] at hRadius
  rcases hRadius with ⟨hEpsOne, hNormRadius, _hConditionRadius, hAnalysisRadius⟩
  let A : P11RectMatrix m (k.val + 1) := p11ColumnPrefix family.A k
  let Q : P11RectMatrix m (k.val + 1) :=
    p11ColumnPrefix (family.run epsilonM).Q k
  let R : P11Matrix (k.val + 1) := p11LeadingBlock (family.run epsilonM).R k
  let S : P11Matrix (k.val + 1) := (family.run epsilonM).leadingInverse k
  let dA : P11RectMatrix m (k.val + 1) :=
    p11Theorem1FactorizationResidual family epsilonM k
  have hdA : dA = p11RectMatMul Q R - A := by rfl
  have hRS : p11MatMul (k.val + 1) R S = p11Identity (k.val + 1) := by
    exact (family.run epsilonM).leading_right_inverse k
  have hMatrix := p11_rect_defect_norm_bound A dA Q R S hdA hRS
  have hFactor := analysis.factorization_bound epsilonM hAnalysisRadius k
  have hNormal := analysis.normal_equation_bound epsilonM hAnalysisRadius k
  have hReverse := analysis.reverse_norm_bound epsilonM hAnalysisRadius k
  have hRBound := family.r_norm_bound epsilonM hNormRadius k
  have hSBound := family.inverse_norm_bound epsilonM hNormRadius k
  change p11OpNorm2 (p11RectOrthogonalityDefect Q) ≤ _
  change p11RectOpNorm2 dA ≤ _ at hFactor
  change p11OpNorm2 (p11RectNormalEquationResidual A R) ≤ _ at hNormal
  change p11RectOpNorm2 A ≤ _ at hReverse
  change p11OpNorm2 R ≤ _ at hRBound
  change p11OpNorm2 S ≤ _ at hSBound
  change p11OpNorm2 (p11RectOrthogonalityDefect Q) ≤ _ at hMatrix
  dsimp only [A, R, S] at hFactor hNormal hReverse hRBound hSBound ⊢
  dsimp only [dA] at hFactor hMatrix
  dsimp only [Q, R, S, A] at hMatrix
  -- The remaining argument is scalar bookkeeping for the first- and second-order terms.
  let eps : ℝ := epsilonM.1
  let a : ℝ := p11RectOpNorm2 (p11ColumnPrefix family.A k)
  let d : ℝ :=
    p11RectOpNorm2 (p11Theorem1FactorizationResidual family epsilonM k)
  let e : ℝ := p11OpNorm2
    (p11RectNormalEquationResidual (p11ColumnPrefix family.A k)
      (p11LeadingBlock (family.run epsilonM).R k))
  let r : ℝ := p11OpNorm2 (p11LeadingBlock (family.run epsilonM).R k)
  let s : ℝ := p11OpNorm2 ((family.run epsilonM).leadingInverse k)
  let rBound : ℝ := family.rNormBound k
  let inverseBound : ℝ := family.inverseNormBound k
  let c1 : ℝ := p11C1 m (k.val + 1)
  let c2 : ℝ := p11C2 m (k.val + 1)
  let c3 : ℝ := p11C3 m (k.val + 1)
  let c4 : ℝ := p11C4 m (k.val + 1)
  let factorRem : ℝ := analysis.factorizationSecondOrderCoeff k
  let normalRem : ℝ := analysis.normalEquationSecondOrderCoeff k
  let reverseRem : ℝ := analysis.reverseNormSecondOrderCoeff k
  let normSlope : ℝ := c3 * rBound + reverseRem
  let aSquareRem : ℝ := 2 * rBound * normSlope + normSlope ^ 2
  let coreRem : ℝ :=
    normalRem + 2 * a * factorRem + (c1 * a + factorRem) ^ 2
  change d ≤ c1 * a * eps + factorRem * eps ^ 2 at hFactor
  change e ≤ c2 * a ^ 2 * eps + normalRem * eps ^ 2 at hNormal
  change a ≤ (1 + c3 * eps) * r + reverseRem * eps ^ 2 at hReverse
  change r ≤ rBound at hRBound
  change s ≤ inverseBound at hSBound
  change p11OpNorm2
      (p11RectOrthogonalityDefect (p11ColumnPrefix (family.run epsilonM).Q k)) ≤
    s ^ 2 * (e + 2 * a * d + d ^ 2) at hMatrix
  have hkpos : 1 ≤ k.val + 1 := by omega
  have hEpsPos : 0 < eps := epsilonM.2
  have hEpsNonneg : 0 ≤ eps := hEpsPos.le
  have hEpsLeOne : eps ≤ 1 := hEpsOne
  have hEpsSqLe : eps ^ 2 ≤ eps := by nlinarith [sq_nonneg (eps - 1 / 2)]
  have ha : 0 ≤ a := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have he : 0 ≤ e := norm_nonneg _
  have hr : 0 ≤ r := norm_nonneg _
  have hs : 0 ≤ s := norm_nonneg _
  have hrBound : 0 ≤ rBound := family.r_norm_bound_nonneg k
  have hiBound : 0 ≤ inverseBound := family.inverse_norm_bound_nonneg k
  have hc1 : 0 ≤ c1 := p11_c1_nonneg m (k.val + 1)
  have hc2 : 0 ≤ c2 := p11_c2_nonneg m (k.val + 1) hkpos
  have hc3 : 0 ≤ c3 := p11_c3_nonneg m (k.val + 1) hkpos
  have hc4 : 0 ≤ c4 := p11_c4_nonneg m (k.val + 1) hkpos
  have hFactorRem : 0 ≤ factorRem :=
    analysis.factorization_second_order_nonneg k
  have hNormalRem : 0 ≤ normalRem :=
    analysis.normal_equation_second_order_nonneg k
  have hReverseRem : 0 ≤ reverseRem :=
    analysis.reverse_norm_second_order_nonneg k
  have hNormSlope : 0 ≤ normSlope := by
    dsimp only [normSlope]
    positivity
  have hASquareRem : 0 ≤ aSquareRem := by
    dsimp only [aSquareRem]
    positivity
  have hCoreRem : 0 ≤ coreRem := by
    dsimp only [coreRem]
    positivity
  have hc4_def : c4 = c2 + 2 * c1 := by
    rfl
  have hFactorSimple : d ≤ (c1 * a + factorRem) * eps := by
    have hrem := mul_le_mul_of_nonneg_left hEpsSqLe hFactorRem
    nlinarith
  have hFactorSquare : d ^ 2 ≤ (c1 * a + factorRem) ^ 2 * eps ^ 2 := by
    have hright : 0 ≤ (c1 * a + factorRem) * eps := by positivity
    calc
      d ^ 2 ≤ ((c1 * a + factorRem) * eps) ^ 2 :=
        (sq_le_sq₀ hd hright).2 hFactorSimple
      _ = (c1 * a + factorRem) ^ 2 * eps ^ 2 := by ring
  have hCross : 2 * a * d ≤
      2 * c1 * a ^ 2 * eps + 2 * a * factorRem * eps ^ 2 := by
    have htwoa : 0 ≤ 2 * a := mul_nonneg (by norm_num) ha
    have hmul : (2 * a) * d ≤
        (2 * a) * (c1 * a * eps + factorRem * eps ^ 2) :=
      mul_le_mul_of_nonneg_left hFactor htwoa
    calc
      2 * a * d ≤ 2 * a * (c1 * a * eps + factorRem * eps ^ 2) := hmul
      _ = 2 * c1 * a ^ 2 * eps + 2 * a * factorRem * eps ^ 2 := by ring
  have hCore : e + 2 * a * d + d ^ 2 ≤
      c4 * a ^ 2 * eps + coreRem * eps ^ 2 := by
    calc
      e + 2 * a * d + d ^ 2 ≤
          (c2 * a ^ 2 * eps + normalRem * eps ^ 2) +
            (2 * c1 * a ^ 2 * eps + 2 * a * factorRem * eps ^ 2) +
              (c1 * a + factorRem) ^ 2 * eps ^ 2 := by
            exact add_le_add (add_le_add hNormal hCross) hFactorSquare
      _ = c4 * a ^ 2 * eps + coreRem * eps ^ 2 := by
        rw [hc4_def]
        dsimp only [coreRem]
        ring
  have hReverseSimple : a ≤ r + normSlope * eps := by
    have hcr := mul_le_mul_of_nonneg_left hRBound hc3
    have hrev := mul_le_mul_of_nonneg_left hEpsSqLe hReverseRem
    calc
      a ≤ (1 + c3 * eps) * r + reverseRem * eps ^ 2 := hReverse
      _ = r + (c3 * r) * eps + reverseRem * eps ^ 2 := by ring
      _ ≤ r + (c3 * rBound) * eps + reverseRem * eps := by gcongr
      _ = r + normSlope * eps := by
        dsimp only [normSlope]
        ring
  have hASquare : a ^ 2 ≤ r ^ 2 + aSquareRem * eps := by
    have hsum : 0 ≤ r + normSlope * eps := by positivity
    have hsquare := (sq_le_sq₀ ha hsum).2 hReverseSimple
    have hcrossBound : 2 * r * normSlope * eps ≤
        2 * rBound * normSlope * eps := by gcongr
    have hslopeSquare := mul_le_mul_of_nonneg_left hEpsSqLe (sq_nonneg normSlope)
    calc
      a ^ 2 ≤ (r + normSlope * eps) ^ 2 := hsquare
      _ = r ^ 2 + 2 * r * normSlope * eps + normSlope ^ 2 * eps ^ 2 := by ring
      _ ≤ r ^ 2 + 2 * rBound * normSlope * eps + normSlope ^ 2 * eps := by
        exact add_le_add (add_le_add le_rfl hcrossBound) hslopeSquare
      _ = r ^ 2 + aSquareRem * eps := by
        dsimp only [aSquareRem]
        ring
  have hsSquare : s ^ 2 ≤ inverseBound ^ 2 :=
    (sq_le_sq₀ hs hiBound).2 hSBound
  have hInside : c4 * a ^ 2 * eps + coreRem * eps ^ 2 ≤
      c4 * r ^ 2 * eps + (c4 * aSquareRem + coreRem) * eps ^ 2 := by
    calc
      c4 * a ^ 2 * eps + coreRem * eps ^ 2 ≤
          c4 * (r ^ 2 + aSquareRem * eps) * eps + coreRem * eps ^ 2 := by
            gcongr
      _ = c4 * r ^ 2 * eps + (c4 * aSquareRem + coreRem) * eps ^ 2 := by ring
  have hRemainderFactor : 0 ≤ (c4 * aSquareRem + coreRem) * eps ^ 2 := by
    positivity
  calc
    p11OpNorm2
        (p11RectOrthogonalityDefect (p11ColumnPrefix (family.run epsilonM).Q k)) ≤
        s ^ 2 * (e + 2 * a * d + d ^ 2) := hMatrix
    _ ≤ s ^ 2 * (c4 * a ^ 2 * eps + coreRem * eps ^ 2) := by gcongr
    _ ≤ s ^ 2 *
        (c4 * r ^ 2 * eps + (c4 * aSquareRem + coreRem) * eps ^ 2) := by gcongr
    _ = c4 * (r * s) ^ 2 * eps +
        s ^ 2 * ((c4 * aSquareRem + coreRem) * eps ^ 2) := by ring
    _ ≤ c4 * (r * s) ^ 2 * eps +
        inverseBound ^ 2 * ((c4 * aSquareRem + coreRem) * eps ^ 2) := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_right hsSquare hRemainderFactor) _
    _ = p11C4 m (k.val + 1) *
          p11Kappa2 (p11LeadingBlock (family.run epsilonM).R k)
            ((family.run epsilonM).leadingInverse k) ^ 2 * epsilonM.1 +
        p11Theorem1OrthogonalityRemainderCoeff family analysis k *
          epsilonM.1 ^ 2 := by
      set_option maxHeartbeats 800000 in
        dsimp only [c4, r, s, eps, inverseBound, aSquareRem, normSlope, coreRem,
          a, rBound, factorRem, normalRem, reverseRem,
          p11Kappa2, p11Theorem1OrthogonalityRemainderCoeff]
        ring

end HighamBench
