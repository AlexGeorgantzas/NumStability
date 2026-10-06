import HighamBench.P11Definitions

open scoped Matrix.Norms.L2Operator

namespace HighamBench

private lemma p11_c1_nonneg (m k : ℕ) : 0 ≤ p11C1 m k := by
  unfold p11C1
  split <;> positivity

private lemma p11_c2_nonneg (m k : ℕ) : 0 ≤ p11C2 m k := by
  unfold p11C2
  split
  · positivity
  · rename_i hk
    by_cases hk0 : k = 0
    · subst k
      norm_num
    · have hk2 : 2 ≤ k := by omega
      have hk2r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
      have hfactor : 0 ≤ (7 / 2 : ℝ) * (k : ℝ) - 3 / 2 := by
        nlinarith
      calc
        (7 / 2 : ℝ) * (m : ℝ) * (k : ℝ) ^ 2 -
              (3 / 2 : ℝ) * (m : ℝ) * (k : ℝ) + 16 * (k : ℝ) =
            (m : ℝ) * (k : ℝ) *
                ((7 / 2 : ℝ) * (k : ℝ) - 3 / 2) + 16 * (k : ℝ) := by ring
        _ ≥ 0 := by positivity

private lemma p11_c3_nonneg (m k : ℕ) : 0 ≤ p11C3 m k := by
  unfold p11C3
  exact mul_nonneg (by norm_num) (p11_c2_nonneg m k)

private lemma p11_c4_nonneg (m k : ℕ) : 0 ≤ p11C4 m k := by
  unfold p11C4
  exact add_nonneg (p11_c2_nonneg m k)
    (mul_nonneg (by norm_num) (p11_c1_nonneg m k))

private lemma p11_rect_transpose_norm {m n : ℕ} (X : P11RectMatrix m n) :
    p11RectOpNorm2 (p11RectTranspose X) = p11RectOpNorm2 X := by
  change ‖X.transpose‖ = ‖X‖
  simpa [Matrix.conjTranspose] using (Matrix.l2_opNorm_conjTranspose X)

private lemma p11_transpose_norm {n : ℕ} (X : P11Matrix n) :
    p11OpNorm2 (p11Transpose X) = p11OpNorm2 X := by
  change ‖X.transpose‖ = ‖X‖
  simpa [Matrix.conjTranspose] using (Matrix.l2_opNorm_conjTranspose X)

private lemma p11_orthogonality_scalar_bound
    (e z core en d a r s rBound inverseBound c1 c2 c3 c4 f g v : ℝ)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hz0 : 0 ≤ z) (hcore0 : 0 ≤ core) (hen0 : 0 ≤ en) (hd0 : 0 ≤ d)
    (ha0 : 0 ≤ a) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hrBound0 : 0 ≤ rBound) (hinverseBound0 : 0 ≤ inverseBound)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3) (hc4 : 0 ≤ c4)
    (hf : 0 ≤ f) (hg : 0 ≤ g) (hv : 0 ≤ v)
    (hc4eq : c4 = c2 + 2 * c1)
    (hrle : r ≤ rBound) (hsle : s ≤ inverseBound)
    (ha : a ≤ (1 + c3 * e) * r + v * e ^ 2)
    (hd : d ≤ c1 * a * e + f * e ^ 2)
    (hen : en ≤ c2 * a ^ 2 * e + g * e ^ 2)
    (hcore : core ≤ en + 2 * a * d + d ^ 2)
    (hz : z ≤ s ^ 2 * core) :
    z ≤ c4 * (r * s) ^ 2 * e +
      inverseBound ^ 2 *
        (c4 * (2 * rBound * (c3 * rBound + v) +
              (c3 * rBound + v) ^ 2) +
          (g + 2 * a * f + (c1 * a + f) ^ 2)) * e ^ 2 := by
  have he2 : e ^ 2 ≤ e := by nlinarith [sq_nonneg e]
  have hfe : f * e ≤ f := by
    nlinarith [mul_nonneg hf (sub_nonneg.mpr he1)]
  have hdSimple : d ≤ (c1 * a + f) * e := by
    calc
      d ≤ c1 * a * e + f * e ^ 2 := hd
      _ = (c1 * a + f * e) * e := by ring
      _ ≤ (c1 * a + f) * e := by
        exact mul_le_mul_of_nonneg_right (by linarith) he0
  have hdUpper0 : 0 ≤ (c1 * a + f) * e := by positivity
  have hdsq : d ^ 2 ≤ ((c1 * a + f) * e) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdSimple)
      (add_nonneg hdUpper0 hd0)]
  have hcross : 2 * a * d ≤ 2 * a * (c1 * a * e + f * e ^ 2) := by
    exact mul_le_mul_of_nonneg_left hd (by positivity)
  have hcoreFirst :
      core ≤ c4 * a ^ 2 * e +
        (g + 2 * a * f + (c1 * a + f) ^ 2) * e ^ 2 := by
    calc
      core ≤ en + 2 * a * d + d ^ 2 := hcore
      _ ≤ (c2 * a ^ 2 * e + g * e ^ 2) +
          2 * a * (c1 * a * e + f * e ^ 2) +
          ((c1 * a + f) * e) ^ 2 := by
            exact add_le_add (add_le_add hen hcross) hdsq
      _ = c4 * a ^ 2 * e +
          (g + 2 * a * f + (c1 * a + f) ^ 2) * e ^ 2 := by
            rw [hc4eq]
            ring
  have haSimple : a ≤ r + (c3 * rBound + v) * e := by
    have hcr : c3 * r * e ≤ c3 * rBound * e := by
      gcongr
    have hve : v * e ^ 2 ≤ v * e := by
      exact mul_le_mul_of_nonneg_left he2 hv
    calc
      a ≤ (1 + c3 * e) * r + v * e ^ 2 := ha
      _ = r + c3 * r * e + v * e ^ 2 := by ring
      _ ≤ r + c3 * rBound * e + v * e := by linarith only [hcr, hve]
      _ = r + (c3 * rBound + v) * e := by ring
  have ht0 : 0 ≤ c3 * rBound + v := by positivity
  have haUpper0 : 0 ≤ r + (c3 * rBound + v) * e := by positivity
  have haSq : a ^ 2 ≤ (r + (c3 * rBound + v) * e) ^ 2 := by
    exact (sq_le_sq₀ ha0 haUpper0).2 haSimple
  have hupperSq :
      (r + (c3 * rBound + v) * e) ^ 2 ≤
        r ^ 2 +
          (2 * rBound * (c3 * rBound + v) +
            (c3 * rBound + v) ^ 2) * e := by
    have hrt :
        2 * r * (c3 * rBound + v) * e ≤
          2 * rBound * (c3 * rBound + v) * e := by
      gcongr
    have hete :
        (c3 * rBound + v) ^ 2 * e ^ 2 ≤
          (c3 * rBound + v) ^ 2 * e := by
      exact mul_le_mul_of_nonneg_left he2 (sq_nonneg _)
    calc
      (r + (c3 * rBound + v) * e) ^ 2 =
          r ^ 2 + 2 * r * (c3 * rBound + v) * e +
            (c3 * rBound + v) ^ 2 * e ^ 2 := by ring
      _ ≤ r ^ 2 + 2 * rBound * (c3 * rBound + v) * e +
            (c3 * rBound + v) ^ 2 * e := by linarith only [hrt, hete]
      _ = r ^ 2 +
          (2 * rBound * (c3 * rBound + v) +
            (c3 * rBound + v) ^ 2) * e := by ring
  have haSqFinal :
      a ^ 2 ≤ r ^ 2 +
        (2 * rBound * (c3 * rBound + v) +
          (c3 * rBound + v) ^ 2) * e :=
    haSq.trans hupperSq
  have hcoreFinal :
      core ≤ c4 * r ^ 2 * e +
        (c4 * (2 * rBound * (c3 * rBound + v) +
              (c3 * rBound + v) ^ 2) +
          (g + 2 * a * f + (c1 * a + f) ^ 2)) * e ^ 2 := by
    calc
      core ≤ c4 * a ^ 2 * e +
          (g + 2 * a * f + (c1 * a + f) ^ 2) * e ^ 2 := hcoreFirst
      _ ≤ c4 *
            (r ^ 2 +
              (2 * rBound * (c3 * rBound + v) +
                (c3 * rBound + v) ^ 2) * e) * e +
          (g + 2 * a * f + (c1 * a + f) ^ 2) * e ^ 2 := by
            gcongr
      _ = c4 * r ^ 2 * e +
          (c4 * (2 * rBound * (c3 * rBound + v) +
                (c3 * rBound + v) ^ 2) +
            (g + 2 * a * f + (c1 * a + f) ^ 2)) * e ^ 2 := by ring
  have hsSq : s ^ 2 ≤ inverseBound ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsle)
      (add_nonneg hinverseBound0 hs0)]
  have hrem0 :
      0 ≤ (c4 * (2 * rBound * (c3 * rBound + v) +
              (c3 * rBound + v) ^ 2) +
          (g + 2 * a * f + (c1 * a + f) ^ 2)) * e ^ 2 := by
    positivity
  calc
    z ≤ s ^ 2 * core := hz
    _ ≤ s ^ 2 *
        (c4 * r ^ 2 * e +
          (c4 * (2 * rBound * (c3 * rBound + v) +
                (c3 * rBound + v) ^ 2) +
            (g + 2 * a * f + (c1 * a + f) ^ 2)) * e ^ 2) := by
              exact mul_le_mul_of_nonneg_left hcoreFinal (sq_nonneg s)
    _ = c4 * (r * s) ^ 2 * e + s ^ 2 *
          ((c4 * (2 * rBound * (c3 * rBound + v) +
                (c3 * rBound + v) ^ 2) +
            (g + 2 * a * f + (c1 * a + f) ^ 2)) * e ^ 2) := by ring
    _ ≤ c4 * (r * s) ^ 2 * e + inverseBound ^ 2 *
          ((c4 * (2 * rBound * (c3 * rBound + v) +
                (c3 * rBound + v) ^ 2) +
            (g + 2 * a * f + (c1 * a + f) ^ 2)) * e ^ 2) := by
              exact add_le_add_right
                (mul_le_mul_of_nonneg_right hsSq hrem0) _
    _ = c4 * (r * s) ^ 2 * e +
        inverseBound ^ 2 *
          (c4 * (2 * rBound * (c3 * rBound + v) +
                (c3 * rBound + v) ^ 2) +
            (g + 2 * a * f + (c1 * a + f) ^ 2)) * e ^ 2 := by ring

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
  classical
  let e : ℝ := epsilonM.1
  let A : P11RectMatrix m (k.val + 1) := p11ColumnPrefix family.A k
  let Q : P11RectMatrix m (k.val + 1) :=
    p11ColumnPrefix (family.run epsilonM).Q k
  let R : P11Matrix (k.val + 1) := p11LeadingBlock (family.run epsilonM).R k
  let S : P11Matrix (k.val + 1) := (family.run epsilonM).leadingInverse k
  let dA : P11RectMatrix m (k.val + 1) := p11RectMatMul Q R - A
  let E : P11Matrix (k.val + 1) := p11RectNormalEquationResidual A R
  have hradius : e ≤ analysis.radius := by
    dsimp [e]
    exact le_trans hepsilon (by
      unfold p11Theorem1OrthogonalityRadius
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hnormRadius : e ≤ family.normBoundRadius := by
    dsimp [e]
    exact le_trans hepsilon (by
      unfold p11Theorem1OrthogonalityRadius
      exact min_le_of_right_le (min_le_left _ _))
  have hepos : 0 < e := epsilonM.2
  have hele : e ≤ 1 := by
    dsimp [e]
    exact le_trans hepsilon (by
      unfold p11Theorem1OrthogonalityRadius
      exact min_le_left _ _)
  have hRinvR : p11MatMul (k.val + 1) S R = p11Identity (k.val + 1) := by
    simpa [S, R] using (family.run epsilonM).leading_left_inverse k
  have hRRinv : p11MatMul (k.val + 1) R S = p11Identity (k.val + 1) := by
    simpa [S, R] using (family.run epsilonM).leading_right_inverse k
  change S * R = 1 at hRinvR
  change R * S = 1 at hRRinv
  have hdA : A + dA = Q * R := by
    simp only [dA, p11RectMatMul]
    abel
  have hQ : Q = p11RectMatMul (A + dA) S := by
    change Q = (A + dA) * S
    rw [hdA, Matrix.mul_assoc, hRRinv, Matrix.mul_one]
  have hcore :
      p11RectDefectCore A dA R =
        R.transpose * R - (A + dA).transpose * (A + dA) := by
    simp only [p11RectDefectCore, p11RectNormalEquationResidual,
      p11MatMul, p11Transpose, p11RectMatMul, p11RectTranspose,
      Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
    abel
  have hdefect :
      p11RectOrthogonalityDefect Q =
        p11MatMul (k.val + 1) (p11Transpose S)
          (p11MatMul (k.val + 1) (p11RectDefectCore A dA R) S) := by
    have hStRt : S.transpose * R.transpose = 1 := by
      rw [← Matrix.transpose_mul, hRRinv]
      exact Matrix.transpose_one
    simp only [p11RectOrthogonalityDefect, p11Identity, p11RectMatMul,
      p11RectTranspose, p11MatMul, p11Transpose]
    rw [hQ, hcore]
    simp only [p11RectMatMul]
    rw [Matrix.transpose_mul]
    calc
      1 - S.transpose * (A + dA).transpose * ((A + dA) * S) =
          (S.transpose * R.transpose) * (R * S) -
            (S.transpose * (A + dA).transpose) * ((A + dA) * S) := by
              rw [hStRt, hRRinv]
              simp
      _ = S.transpose *
            ((R.transpose * R - (A + dA).transpose * (A + dA)) * S) := by
              simp only [Matrix.mul_sub, Matrix.sub_mul]
              simp only [Matrix.mul_assoc]
  have hnormDefect :
      p11OpNorm2 (p11RectOrthogonalityDefect Q) ≤
        p11OpNorm2 S ^ 2 * p11OpNorm2 (p11RectDefectCore A dA R) := by
    rw [hdefect]
    calc
      p11OpNorm2
          (p11MatMul (k.val + 1) (p11Transpose S)
            (p11MatMul (k.val + 1) (p11RectDefectCore A dA R) S)) ≤
          p11OpNorm2 (p11Transpose S) *
            p11OpNorm2 (p11MatMul (k.val + 1) (p11RectDefectCore A dA R) S) := by
              exact Matrix.l2_opNorm_mul _ _
      _ ≤ p11OpNorm2 (p11Transpose S) *
            (p11OpNorm2 (p11RectDefectCore A dA R) * p11OpNorm2 S) := by
              apply mul_le_mul_of_nonneg_left
              · exact Matrix.l2_opNorm_mul
                  (p11RectDefectCore A dA R) S
              · exact norm_nonneg _
      _ = p11OpNorm2 S ^ 2 * p11OpNorm2 (p11RectDefectCore A dA R) := by
              rw [p11_transpose_norm]
              ring
  have hcoreNorm :
      p11OpNorm2 (p11RectDefectCore A dA R) ≤
        p11OpNorm2 E +
          2 * p11RectOpNorm2 A * p11RectOpNorm2 dA +
          p11RectOpNorm2 dA ^ 2 := by
    have hEA : E = p11RectNormalEquationResidual A R := rfl
    have htriangle :
        p11OpNorm2 (p11RectDefectCore A dA R) ≤
          p11OpNorm2 E +
            p11OpNorm2 (p11RectMatMul (p11RectTranspose A) dA) +
            p11OpNorm2 (p11RectMatMul (p11RectTranspose dA) A) +
            p11OpNorm2 (p11RectMatMul (p11RectTranspose dA) dA) := by
      simp only [p11RectDefectCore, ← hEA]
      change ‖E - p11RectTranspose A * dA - p11RectTranspose dA * A -
          p11RectTranspose dA * dA‖ ≤
        ‖E‖ + ‖p11RectTranspose A * dA‖ + ‖p11RectTranspose dA * A‖ +
          ‖p11RectTranspose dA * dA‖
      calc
        ‖E - p11RectTranspose A * dA - p11RectTranspose dA * A -
            p11RectTranspose dA * dA‖ ≤
            ‖E - p11RectTranspose A * dA - p11RectTranspose dA * A‖ +
              ‖p11RectTranspose dA * dA‖ := norm_sub_le _ _
        _ ≤ (‖E - p11RectTranspose A * dA‖ +
              ‖p11RectTranspose dA * A‖) +
              ‖p11RectTranspose dA * dA‖ := by
                gcongr
                exact norm_sub_le _ _
        _ ≤ ((‖E‖ + ‖p11RectTranspose A * dA‖) +
              ‖p11RectTranspose dA * A‖) +
              ‖p11RectTranspose dA * dA‖ := by
                gcongr
                exact norm_sub_le _ _
        _ = ‖E‖ + ‖p11RectTranspose A * dA‖ +
              ‖p11RectTranspose dA * A‖ +
              ‖p11RectTranspose dA * dA‖ := by ring
    have hAd :
        p11OpNorm2 (p11RectMatMul (p11RectTranspose A) dA) ≤
          p11RectOpNorm2 A * p11RectOpNorm2 dA := by
      calc
        p11OpNorm2 (p11RectMatMul (p11RectTranspose A) dA) ≤
            p11RectOpNorm2 (p11RectTranspose A) * p11RectOpNorm2 dA := by
              exact Matrix.l2_opNorm_mul _ _
        _ = _ := by rw [p11_rect_transpose_norm]
    have hdA' :
        p11OpNorm2 (p11RectMatMul (p11RectTranspose dA) A) ≤
          p11RectOpNorm2 dA * p11RectOpNorm2 A := by
      calc
        p11OpNorm2 (p11RectMatMul (p11RectTranspose dA) A) ≤
            p11RectOpNorm2 (p11RectTranspose dA) * p11RectOpNorm2 A := by
              exact Matrix.l2_opNorm_mul _ _
        _ = _ := by rw [p11_rect_transpose_norm]
    have hdd :
        p11OpNorm2 (p11RectMatMul (p11RectTranspose dA) dA) ≤
          p11RectOpNorm2 dA ^ 2 := by
      calc
        p11OpNorm2 (p11RectMatMul (p11RectTranspose dA) dA) ≤
            p11RectOpNorm2 (p11RectTranspose dA) * p11RectOpNorm2 dA := by
              exact Matrix.l2_opNorm_mul _ _
        _ = _ := by rw [p11_rect_transpose_norm]; ring
    linarith
  have hfactorization :
      p11RectOpNorm2 dA ≤
        p11C1 m (k.val + 1) * p11RectOpNorm2 A * e +
          analysis.factorizationSecondOrderCoeff k * e ^ 2 := by
    simpa [dA, Q, R, A, e, p11Theorem1FactorizationResidual] using
      (analysis.factorization_bound epsilonM hradius k)
  have hnormal :
      p11OpNorm2 E ≤
        p11C2 m (k.val + 1) * p11RectOpNorm2 A ^ 2 * e +
          analysis.normalEquationSecondOrderCoeff k * e ^ 2 := by
    simpa [E, A, R, e] using
      (analysis.normal_equation_bound epsilonM hradius k)
  have hreverse :
      p11RectOpNorm2 A ≤
        (1 + p11C3 m (k.val + 1) * e) * p11OpNorm2 R +
          analysis.reverseNormSecondOrderCoeff k * e ^ 2 := by
    simpa [A, R, e] using
      (analysis.reverse_norm_bound epsilonM hradius k)
  have hRbound : p11OpNorm2 R ≤ family.rNormBound k := by
    simpa [R] using (family.r_norm_bound epsilonM hnormRadius k)
  have hSbound : p11OpNorm2 S ≤ family.inverseNormBound k := by
    simpa [S] using (family.inverse_norm_bound epsilonM hnormRadius k)
  have hscalar := p11_orthogonality_scalar_bound
    e
    (p11OpNorm2 (p11RectOrthogonalityDefect Q))
    (p11OpNorm2 (p11RectDefectCore A dA R))
    (p11OpNorm2 E)
    (p11RectOpNorm2 dA)
    (p11RectOpNorm2 A)
    (p11OpNorm2 R)
    (p11OpNorm2 S)
    (family.rNormBound k)
    (family.inverseNormBound k)
    (p11C1 m (k.val + 1))
    (p11C2 m (k.val + 1))
    (p11C3 m (k.val + 1))
    (p11C4 m (k.val + 1))
    (analysis.factorizationSecondOrderCoeff k)
    (analysis.normalEquationSecondOrderCoeff k)
    (analysis.reverseNormSecondOrderCoeff k)
    (le_of_lt hepos) hele
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (family.r_norm_bound_nonneg k) (family.inverse_norm_bound_nonneg k)
    (p11_c1_nonneg _ _) (p11_c2_nonneg _ _) (p11_c3_nonneg _ _)
    (p11_c4_nonneg _ _)
    (analysis.factorization_second_order_nonneg k)
    (analysis.normal_equation_second_order_nonneg k)
    (analysis.reverse_norm_second_order_nonneg k)
    (by rfl) hRbound hSbound hreverse hfactorization hnormal hcoreNorm
    hnormDefect
  simpa [Q, R, S, A, e, p11Kappa2,
    p11Theorem1OrthogonalityRemainderCoeff] using hscalar

end HighamBench
