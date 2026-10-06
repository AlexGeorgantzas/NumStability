import HighamBench.P11Definitions

namespace HighamBench

open scoped Matrix.Norms.L2Operator

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
  intro epsilonM he k
  classical
  rw [p11Theorem1OrthogonalityRadius, le_min_iff, le_min_iff,
    le_min_iff] at he
  rcases he with ⟨he_one, he_norm, _he_condition, he_analysis⟩

  let e : ℝ := epsilonM.1
  let A : P11RectMatrix m (k.val + 1) := p11ColumnPrefix family.A k
  let Q : P11RectMatrix m (k.val + 1) :=
    p11ColumnPrefix (family.run epsilonM).Q k
  let R : P11Matrix (k.val + 1) :=
    p11LeadingBlock (family.run epsilonM).R k
  let Ri : P11Matrix (k.val + 1) :=
    (family.run epsilonM).leadingInverse k
  let dA : P11RectMatrix m (k.val + 1) :=
    p11Theorem1FactorizationResidual family epsilonM k
  let E : P11Matrix (k.val + 1) := p11RectNormalEquationResidual A R
  let K : P11Matrix (k.val + 1) := p11RectDefectCore A dA R

  let a : ℝ := p11RectOpNorm2 A
  let r : ℝ := p11OpNorm2 R
  let ri : ℝ := p11OpNorm2 Ri
  let d : ℝ := p11RectOpNorm2 dA
  let en : ℝ := p11OpNorm2 E
  let c1 : ℝ := p11C1 m (k.val + 1)
  let c2 : ℝ := p11C2 m (k.val + 1)
  let c3 : ℝ := p11C3 m (k.val + 1)
  let c4 : ℝ := p11C4 m (k.val + 1)
  let f : ℝ := analysis.factorizationSecondOrderCoeff k
  let g : ℝ := analysis.normalEquationSecondOrderCoeff k
  let v : ℝ := analysis.reverseNormSecondOrderCoeff k
  let rb : ℝ := family.rNormBound k
  let ib : ℝ := family.inverseNormBound k

  have he0 : 0 ≤ e := le_of_lt epsilonM.2
  have he1 : e ≤ 1 := he_one
  have ha0 : 0 ≤ a := by exact norm_nonneg _
  have hr0 : 0 ≤ r := by exact norm_nonneg _
  have hri0 : 0 ≤ ri := by exact norm_nonneg _
  have hd0 : 0 ≤ d := by exact norm_nonneg _
  have hf0 : 0 ≤ f := analysis.factorization_second_order_nonneg k
  have hg0 : 0 ≤ g := analysis.normal_equation_second_order_nonneg k
  have hv0 : 0 ≤ v := analysis.reverse_norm_second_order_nonneg k
  have hrb0 : 0 ≤ rb := family.r_norm_bound_nonneg k
  have hib0 : 0 ≤ ib := family.inverse_norm_bound_nonneg k

  have hc1 : 0 ≤ c1 := by
    dsimp [c1, p11C1]
    split_ifs <;> positivity
  have hc2 : 0 ≤ c2 := by
    dsimp [c2, p11C2]
    split_ifs with hk
    · positivity
    · have hk_nat : 2 ≤ k.val + 1 := by omega
      have hk_real : (2 : ℝ) ≤ (k.val + 1 : ℕ) := by exact_mod_cast hk_nat
      have hm_real : 0 ≤ (m : ℝ) := by positivity
      let x : ℝ := (k.val + 1 : ℕ)
      have hx : 2 ≤ x := hk_real
      have hcoef : 0 ≤ (7 / 2 : ℝ) * x - 3 / 2 := by nlinarith
      change 0 ≤ (7 / 2 : ℝ) * (m : ℝ) * x ^ 2 -
        (3 / 2 : ℝ) * (m : ℝ) * x + 16 * x
      rw [show (7 / 2 : ℝ) * (m : ℝ) * x ^ 2 -
          (3 / 2 : ℝ) * (m : ℝ) * x + 16 * x =
          (m : ℝ) * x * ((7 / 2 : ℝ) * x - 3 / 2) + 16 * x by ring]
      positivity
  have hc3 : 0 ≤ c3 := by
    dsimp [c3, p11C3]
    positivity
  have hc4 : 0 ≤ c4 := by
    dsimp [c4, p11C4]
    positivity

  have hr : r ≤ rb := by
    have h := family.r_norm_bound epsilonM he_norm k
    exact h
  have hri : ri ≤ ib := by
    have h := family.inverse_norm_bound epsilonM he_norm k
    exact h
  have hd : d ≤ c1 * a * e + f * e ^ 2 := by
    have h := analysis.factorization_bound epsilonM he_analysis k
    exact h
  have hE : en ≤ c2 * a ^ 2 * e + g * e ^ 2 := by
    have h := analysis.normal_equation_bound epsilonM he_analysis k
    exact h
  have hreverse : a ≤ (1 + c3 * e) * r + v * e ^ 2 := by
    have h := analysis.reverse_norm_bound epsilonM he_analysis k
    exact h

  let slope : ℝ := c3 * rb + v
  let asqRem : ℝ := 2 * rb * slope + slope ^ 2
  let coreRem : ℝ := g + 2 * a * f + (c1 * a + f) ^ 2
  have hslope0 : 0 ≤ slope := by
    dsimp [slope]
    positivity
  have hasqRem0 : 0 ≤ asqRem := by
    dsimp [asqRem]
    positivity
  have hcoreRem0 : 0 ≤ coreRem := by
    dsimp [coreRem]
    positivity

  have he_sq : e ^ 2 ≤ e := by nlinarith
  have hcr : c3 * e * r ≤ c3 * e * rb := by
    exact mul_le_mul_of_nonneg_left hr (mul_nonneg hc3 he0)
  have hve : v * e ^ 2 ≤ v * e :=
    mul_le_mul_of_nonneg_left he_sq hv0
  have ha_linear : a ≤ r + slope * e := by
    dsimp [slope]
    nlinarith [hreverse, hcr, hve]
  have ha_square_first : a ^ 2 ≤ (r + slope * e) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha_linear)
      (add_nonneg ha0 (add_nonneg hr0 (mul_nonneg hslope0 he0)))]
  have hrs : r * slope ≤ rb * slope :=
    mul_le_mul_of_nonneg_right hr hslope0
  have hrs_e : r * slope * e ≤ rb * slope * e :=
    mul_le_mul_of_nonneg_right hrs he0
  have hslope_e : slope ^ 2 * e ^ 2 ≤ slope ^ 2 * e :=
    mul_le_mul_of_nonneg_left he_sq (sq_nonneg slope)
  have ha_square : a ^ 2 ≤ r ^ 2 + asqRem * e := by
    dsimp [asqRem]
    calc
      a ^ 2 ≤ (r + slope * e) ^ 2 := ha_square_first
      _ = r ^ 2 + (2 * (r * slope) * e + slope ^ 2 * e ^ 2) := by ring
      _ ≤ r ^ 2 + (2 * (rb * slope) * e + slope ^ 2 * e) := by
        gcongr
      _ = r ^ 2 + (2 * rb * slope + slope ^ 2) * e := by ring

  have hd_simple : d ≤ (c1 * a + f) * e := by
    have hfe : f * e ^ 2 ≤ f * e :=
      mul_le_mul_of_nonneg_left he_sq hf0
    calc
      d ≤ c1 * a * e + f * e ^ 2 := hd
      _ ≤ c1 * a * e + f * e := add_le_add (le_refl _) hfe
      _ = (c1 * a + f) * e := by ring

  have hRri : R * Ri = 1 := by
    exact family.run epsilonM |>.leading_right_inverse k
  have hRiRt : Ri.transpose * R.transpose = 1 := by
    have h := congrArg Matrix.transpose hRri
    simpa [Matrix.transpose_mul] using h
  have hdA_eq : dA = Q * R - A := by
    rfl
  have hQ : Q = (A + dA) * Ri := by
    calc
      Q = Q * (R * Ri) := by rw [hRri]; simp
      _ = (Q * R) * Ri := by rw [Matrix.mul_assoc]
      _ = (A + dA) * Ri := by
        congr 1
        rw [hdA_eq]
        abel
  have hone_factor : (1 : P11Matrix (k.val + 1)) =
      Ri.transpose * R.transpose * R * Ri := by
    calc
      (1 : P11Matrix (k.val + 1)) = 1 * 1 := by simp
      _ = (Ri.transpose * R.transpose) * (R * Ri) := by
        rw [hRiRt, hRri]
      _ = Ri.transpose * R.transpose * R * Ri := by
        simp only [Matrix.mul_assoc]
  have hdefect : p11RectOrthogonalityDefect Q =
      Ri.transpose * K * Ri := by
    rw [hQ]
    simp only [p11RectOrthogonalityDefect, p11Identity,
      p11RectMatMul, p11RectTranspose, Matrix.transpose_mul,
      Matrix.transpose_add]
    rw [hone_factor]
    dsimp [K, p11RectDefectCore, p11RectNormalEquationResidual,
      p11MatMul, p11Transpose, p11RectMatMul, p11RectTranspose]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_assoc]
    abel

  have hcore_triangle : p11OpNorm2 K ≤ en + 2 * a * d + d ^ 2 := by
    dsimp [K, p11RectDefectCore]
    change ‖E - A.transpose * dA - dA.transpose * A - dA.transpose * dA‖ ≤
      en + 2 * a * d + d ^ 2
    calc
      ‖E - A.transpose * dA - dA.transpose * A - dA.transpose * dA‖
          ≤ ‖E‖ + ‖A.transpose * dA‖ + ‖dA.transpose * A‖ +
              ‖dA.transpose * dA‖ := by
            calc
              _ ≤ ‖E - A.transpose * dA - dA.transpose * A‖ +
                    ‖dA.transpose * dA‖ := norm_sub_le _ _
              _ ≤ (‖E - A.transpose * dA‖ + ‖dA.transpose * A‖) +
                    ‖dA.transpose * dA‖ := by gcongr; exact norm_sub_le _ _
              _ ≤ ((‖E‖ + ‖A.transpose * dA‖) +
                    ‖dA.transpose * A‖) + ‖dA.transpose * dA‖ := by
                    gcongr; exact norm_sub_le _ _
              _ = _ := by ring
      _ ≤ ‖E‖ + (a * d) + (d * a) + (d * d) := by
            gcongr
            · calc
                ‖A.transpose * dA‖ ≤ ‖A.transpose‖ * ‖dA‖ :=
                  Matrix.l2_opNorm_mul _ _
                _ = a * d := by
                  rw [show ‖A.transpose‖ = ‖A‖ by
                    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
                      Matrix.l2_opNorm_conjTranspose A]
                  dsimp [a, d, p11RectOpNorm2]
            · calc
                ‖dA.transpose * A‖ ≤ ‖dA.transpose‖ * ‖A‖ :=
                  Matrix.l2_opNorm_mul _ _
                _ = d * a := by
                  rw [show ‖dA.transpose‖ = ‖dA‖ by
                    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
                      Matrix.l2_opNorm_conjTranspose dA]
                  dsimp [a, d, p11RectOpNorm2]
            · calc
                ‖dA.transpose * dA‖ ≤ ‖dA.transpose‖ * ‖dA‖ :=
                  Matrix.l2_opNorm_mul _ _
                _ = d * d := by
                  rw [show ‖dA.transpose‖ = ‖dA‖ by
                    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
                      Matrix.l2_opNorm_conjTranspose dA]
                  dsimp [d, p11RectOpNorm2]
      _ = en + 2 * a * d + d ^ 2 := by
            dsimp [en, a, d, E, p11OpNorm2, p11RectOpNorm2]
            ring

  have hcore : p11OpNorm2 K ≤ c4 * a ^ 2 * e + coreRem * e ^ 2 := by
    have had : 2 * a * d ≤
        2 * c1 * a ^ 2 * e + 2 * a * f * e ^ 2 := by
      calc
        2 * a * d ≤ 2 * a * (c1 * a * e + f * e ^ 2) :=
          mul_le_mul_of_nonneg_left hd (by positivity)
        _ = 2 * c1 * a ^ 2 * e + 2 * a * f * e ^ 2 := by ring
    have hd_sq : d ^ 2 ≤ (c1 * a + f) ^ 2 * e ^ 2 := by
      have hright0 : 0 ≤ (c1 * a + f) * e := by positivity
      calc
        d ^ 2 ≤ ((c1 * a + f) * e) ^ 2 := by
          exact (sq_le_sq₀ hd0 hright0).2 hd_simple
        _ = (c1 * a + f) ^ 2 * e ^ 2 := by ring
    calc
      p11OpNorm2 K ≤ en + 2 * a * d + d ^ 2 := hcore_triangle
      _ ≤ (c2 * a ^ 2 * e + g * e ^ 2) +
          (2 * c1 * a ^ 2 * e + 2 * a * f * e ^ 2) +
          (c1 * a + f) ^ 2 * e ^ 2 := by
            exact add_le_add (add_le_add hE had) hd_sq
      _ = c4 * a ^ 2 * e + coreRem * e ^ 2 := by
            dsimp [c4, p11C4, coreRem]
            ring

  have hcore_R : p11OpNorm2 K ≤
      c4 * r ^ 2 * e + (c4 * asqRem + coreRem) * e ^ 2 := by
    calc
      p11OpNorm2 K ≤ c4 * a ^ 2 * e + coreRem * e ^ 2 := hcore
      _ ≤ c4 * (r ^ 2 + asqRem * e) * e + coreRem * e ^ 2 := by
        gcongr
      _ = c4 * r ^ 2 * e + (c4 * asqRem + coreRem) * e ^ 2 := by ring

  have hdefect_norm : p11OpNorm2 (p11RectOrthogonalityDefect Q) ≤
      ri ^ 2 * p11OpNorm2 K := by
    rw [hdefect]
    change ‖Ri.transpose * K * Ri‖ ≤ ri ^ 2 * p11OpNorm2 K
    calc
      ‖Ri.transpose * K * Ri‖ ≤ ‖Ri.transpose * K‖ * ‖Ri‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ (‖Ri.transpose‖ * ‖K‖) * ‖Ri‖ := by
        gcongr
        exact Matrix.l2_opNorm_mul _ _
      _ = ri ^ 2 * p11OpNorm2 K := by
        rw [show ‖Ri.transpose‖ = ‖Ri‖ by
          simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
            Matrix.l2_opNorm_conjTranspose Ri]
        dsimp [ri, p11OpNorm2]
        ring

  have hextra0 : 0 ≤ c4 * asqRem + coreRem :=
    add_nonneg (mul_nonneg hc4 hasqRem0) hcoreRem0
  have hri_sq : ri ^ 2 ≤ ib ^ 2 := (sq_le_sq₀ hri0 hib0).2 hri
  have hremainder : ri ^ 2 * (c4 * asqRem + coreRem) * e ^ 2 ≤
      ib ^ 2 * (c4 * asqRem + coreRem) * e ^ 2 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hri_sq hextra0) (sq_nonneg e)
  have hfinal : p11OpNorm2 (p11RectOrthogonalityDefect Q) ≤
      c4 * (r * ri) ^ 2 * e +
        ib ^ 2 * (c4 * asqRem + coreRem) * e ^ 2 := by
    calc
      p11OpNorm2 (p11RectOrthogonalityDefect Q)
          ≤ ri ^ 2 * p11OpNorm2 K := hdefect_norm
      _ ≤ ri ^ 2 *
          (c4 * r ^ 2 * e + (c4 * asqRem + coreRem) * e ^ 2) :=
            mul_le_mul_of_nonneg_left hcore_R (sq_nonneg ri)
      _ = c4 * (r * ri) ^ 2 * e +
          ri ^ 2 * (c4 * asqRem + coreRem) * e ^ 2 := by ring
      _ ≤ c4 * (r * ri) ^ 2 * e +
          ib ^ 2 * (c4 * asqRem + coreRem) * e ^ 2 :=
            add_le_add (le_refl _) hremainder

  change p11OpNorm2 (p11RectOrthogonalityDefect Q) ≤
    c4 * p11Kappa2 R Ri ^ 2 * e +
      p11Theorem1OrthogonalityRemainderCoeff family analysis k * e ^ 2
  dsimp [p11Kappa2, p11Theorem1OrthogonalityRemainderCoeff]
  exact hfinal

end HighamBench
