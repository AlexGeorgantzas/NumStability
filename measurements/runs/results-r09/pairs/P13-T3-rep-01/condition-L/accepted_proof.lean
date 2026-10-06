import HighamBench.P13Definitions

namespace HighamBench

open Filter Asymptotics
open scoped BigOperators Topology

private lemma p13_abs_sum_perturbation
    {m : ℕ} (a v : Fin m → ℝ) (g : ℝ)
    (hg : 0 ≤ g) (hv : ∀ i, |v i - 1| ≤ g) :
    |∑ i, a i * v i - ∑ i, a i| ≤ g * ∑ i, |a i| := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i, (a i * v i - a i)| ≤ ∑ i, |a i * v i - a i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |v i - 1| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ ∑ i, |a i| * g := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)
    _ = g * ∑ i, |a i| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

private lemma p13_ratio_perturbation
    (N D Nh Dh a b : ℝ)
    (hN : N ≠ 0) (hD : D ≠ 0)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hNe : |Nh - N| ≤ a * |N|)
    (hDe : |Dh - D| ≤ b * |D|) (hb1 : b < 1) :
    |N / D - Nh / Dh| / |N / D| ≤ (a + b) / (1 - b) := by
  have hNabs : 0 < |N| := abs_pos.mpr hN
  have hDabs : 0 < |D| := abs_pos.mpr hD
  have hDe_lt : |Dh - D| < |D| :=
    lt_of_le_of_lt hDe (by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hb1 hDabs)
  have hDh : Dh ≠ 0 := by
    intro hz
    subst Dh
    have : |D| < |D| := by simpa only [zero_sub, abs_neg] using hDe_lt
    exact (lt_irrefl _ this)
  have hDhabs : 0 < |Dh| := abs_pos.mpr hDh
  have hDh_lower : (1 - b) * |D| ≤ |Dh| := by
    have ht : |D| ≤ |Dh - D| + |Dh| := by
      calc
        |D| = |-(Dh - D) + Dh| := by congr 1 <;> ring
        _ ≤ |-(Dh - D)| + |Dh| := abs_add_le _ _
        _ = |Dh - D| + |Dh| := by rw [abs_neg]
    nlinarith
  have hnum : |N * Dh - Nh * D| ≤ |N| * |D| * (a + b) := by
    calc
      |N * Dh - Nh * D| = |N * (Dh - D) - D * (Nh - N)| := by
        congr 1
        ring
      _ ≤ |N * (Dh - D)| + |D * (Nh - N)| := abs_sub _ _
      _ = |N| * |Dh - D| + |D| * |Nh - N| := by
        rw [abs_mul, abs_mul]
      _ ≤ |N| * (b * |D|) + |D| * (a * |N|) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hDe (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hNe (abs_nonneg _))
      _ = |N| * |D| * (a + b) := by ring
  have hrel :
      |N / D - Nh / Dh| / |N / D| =
        |N * Dh - Nh * D| / (|N| * |Dh|) := by
    have hdiff : N / D - Nh / Dh = (N * Dh - Nh * D) / (D * Dh) := by
      field_simp
      <;> ring
    rw [hdiff]
    simp only [abs_div, abs_mul]
    field_simp [abs_ne_zero.mpr hN, abs_ne_zero.mpr hD,
      abs_ne_zero.mpr hDh]
  rw [hrel]
  apply (div_le_div_iff₀ (mul_pos hNabs hDhabs) (sub_pos.mpr hb1)).2
  calc
    |N * Dh - Nh * D| * (1 - b) ≤
        (|N| * |D| * (a + b)) * (1 - b) :=
      mul_le_mul_of_nonneg_right hnum (sub_nonneg.mpr (le_of_lt hb1))
    _ = (a + b) * (|N| * ((1 - b) * |D|)) := by ring
    _ ≤ (a + b) * (|N| * |Dh|) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hDh_lower (abs_nonneg _)) (add_nonneg ha hb)

private lemma p13_quadratic_rational_isBigO
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (u : ι → ℝ) (hu : Tendsto u l (nhds 0))
    (kn kd cN cD C : ℝ) :
    (fun t => (u t) ^ 2 *
      (((kn ^ 2 * cN) / (1 - kn * u t) +
          (kd ^ 2 * cD) / (1 - kd * u t) +
          (C * kd * cD) / (1 - kd * u t)) /
        (1 - (kd * u t / (1 - kd * u t)) * cD)))
      =O[l] (fun t => (u t) ^ 2) := by
  let K : ℝ → ℝ := fun x =>
    ((kn ^ 2 * cN) / (1 - kn * x) +
        (kd ^ 2 * cD) / (1 - kd * x) +
        (C * kd * cD) / (1 - kd * x)) /
      (1 - (kd * x / (1 - kd * x)) * cD)
  have hK : ContinuousAt K 0 := by
    dsimp only [K]
    have hkn : ContinuousAt (fun x : ℝ => 1 - kn * x) 0 := by fun_prop
    have hkd : ContinuousAt (fun x : ℝ => 1 - kd * x) 0 := by fun_prop
    have htN : ContinuousAt (fun x : ℝ => kn ^ 2 * cN / (1 - kn * x)) 0 :=
      continuousAt_const.div hkn (by norm_num)
    have htD : ContinuousAt (fun x : ℝ => kd ^ 2 * cD / (1 - kd * x)) 0 :=
      continuousAt_const.div hkd (by norm_num)
    have htC : ContinuousAt (fun x : ℝ => C * kd * cD / (1 - kd * x)) 0 :=
      continuousAt_const.div hkd (by norm_num)
    have hratio : ContinuousAt (fun x : ℝ => kd * x / (1 - kd * x)) 0 :=
      (continuousAt_const.mul continuousAt_id).div hkd (by norm_num)
    have hout :
        ContinuousAt (fun x : ℝ => 1 - (kd * x / (1 - kd * x)) * cD) 0 :=
      continuousAt_const.sub (hratio.mul continuousAt_const)
    exact ((htN.add htD).add htC).div hout (by norm_num)
  have hKO : (fun t => K (u t)) =O[l] (fun _ : ι => (1 : ℝ)) :=
    (hK.tendsto.comp hu).isBigO_one ℝ
  have hsq : (fun t => (u t) ^ 2) =O[l] (fun t => (u t) ^ 2) :=
    isBigO_refl _ _
  simpa only [K, mul_one] using hsq.mul hKO

private lemma p13_gamma_sub_linear_isBigO
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (u : ι → ℝ) (hu : Tendsto u l (nhds 0)) (k : ℕ)
    (hvalid : ∀ t, GammaValid (u t) k) :
    (fun t => gamma (u t) k - (k : ℝ) * u t)
      =O[l] (fun t => (u t) ^ 2) := by
  let Q : ℝ → ℝ := fun x => (k : ℝ) ^ 2 / (1 - (k : ℝ) * x)
  have hQcont : ContinuousAt Q 0 := by
    dsimp only [Q]
    exact continuousAt_const.div
      (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)) (by norm_num)
  have hQO : (fun t => Q (u t)) =O[l] (fun _ : ι => (1 : ℝ)) :=
    (hQcont.tendsto.comp hu).isBigO_one ℝ
  have heq :
      (fun t => gamma (u t) k - (k : ℝ) * u t) =
        (fun t => (u t) ^ 2 * Q (u t)) := by
    funext t
    have hden : 1 - (k : ℝ) * u t ≠ 0 :=
      ne_of_gt (sub_pos.mpr (hvalid t))
    dsimp only [gamma, Q]
    field_simp [hden]
    ring
  rw [heq]
  have hsq : (fun t => (u t) ^ 2) =O[l] (fun t => (u t) ^ 2) :=
    isBigO_refl _ _
  simpa only [mul_one] using hsq.mul hQO

theorem p13_t3_barycentric_forward_bound
    {n : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    (problem : P13SecondBarycentricProblem n)
    (u : ι → ℝ)
    (run : ∀ t, P13SecondBarycentricExecution problem (u t))
    (hu : Filter.Tendsto u l (nhds 0))
    (hnumerator : p13SecondBarycentricNumerator problem ≠ 0)
    (hdenominator : p13SecondBarycentricDenominator problem ≠ 0) :
    let conditionData := p13SecondBarycentricDataCondition problem
    let conditionOne := p13SecondBarycentricOneCondition problem
    ∃ remainder : ι → ℝ,
      remainder =O[l] (fun t => (u t) ^ 2) ∧
      ∀ᶠ t in l,
        p13SecondBarycentricRelativeError (run t) ≤
          u t * p13SecondBarycentricFirstOrderCoefficient n
            conditionData conditionOne +
          |remainder t| := by
  -- PROOF_START P13-T3-H001
  dsimp only
  let ell : Fin (n + 1) → ℝ :=
    p13DirectBarycentricCoefficient problem.nodes problem.x
  let a : Fin (n + 1) → ℝ := fun j => ell j * problem.data j
  let b : Fin (n + 1) → ℝ := fun j => ell j
  let N : ℝ := ∑ j, a j
  let D : ℝ := ∑ j, b j
  let Nh : ι → ℝ := fun t =>
    ∑ j, a j * ((run t).numeratorCounter j).value
  let Dh : ι → ℝ := fun t =>
    ∑ j, b j * ((run t).denominatorCounter j).value
  let kN : ℕ := p13NumeratorCounterLength n
  let kD : ℕ := p13DenominatorCounterLength n
  let kn : ℝ := (kN : ℝ)
  let kd : ℝ := (kD : ℝ)
  let cN : ℝ := p13SecondBarycentricDataCondition problem
  let cD : ℝ := p13SecondBarycentricOneCondition problem
  let C : ℝ := kn * cN + kd * cD
  let remainder : ι → ℝ := fun t =>
    (gamma (u t) kN * cN + gamma (u t) kD * cD) /
        (1 - gamma (u t) kD * cD) -
      u t * C
  have hN : N ≠ 0 := by
    simpa only [N, a, ell, p13SecondBarycentricNumerator,
      p13InterpolationValue] using hnumerator
  have hD : D ≠ 0 := by
    simpa only [D, b, ell, p13SecondBarycentricDenominator,
      p13InterpolationValue, mul_one] using hdenominator
  have hcN : cN = (∑ j, |a j|) / |N| := by
    simp only [cN, p13SecondBarycentricDataCondition, p13Condition,
      p13InterpolationValue, a, ell, N]
  have hcD : cD = (∑ j, |b j|) / |D| := by
    simp only [cD, p13SecondBarycentricOneCondition, p13Condition,
      p13InterpolationValue, b, ell, D, mul_one]
  have hcN_nonneg : 0 ≤ cN := by
    rw [hcN]
    positivity
  have hcD_nonneg : 0 ≤ cD := by
    rw [hcD]
    positivity
  have hcomputed : ∀ t, p13SecondBarycentricComputed (run t) = Nh t / Dh t := by
    intro t
    have hNh :
        Nh t =
          (∑ j,
            ell j * ((run t).weightCounter j).value * problem.data j *
              ((run t).numeratorEvaluationCounter j).value) *
            (run t).quotientCounter.value := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [(run t).numeratorCounter_eq j]
      simp only [Nh, a]
      ring
    have hDh :
        Dh t =
          ∑ j,
            ell j * ((run t).weightCounter j).value *
              ((run t).denominatorEvaluationCounter j).value := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [(run t).denominatorCounter_eq j]
      simp only [Dh, b]
      ring
    rw [hNh, hDh]
    simp only [p13SecondBarycentricComputed, ell]
    ring
  have hexact : p13SecondBarycentricExact problem = N / D := by
    simp only [p13SecondBarycentricExact, p13SecondBarycentricNumerator,
      p13SecondBarycentricDenominator, p13InterpolationValue, N, D, a, b,
      ell, mul_one]
  have hgammaD : Tendsto (fun t => gamma (u t) kD) l (nhds 0) := by
    have hcont : ContinuousAt (fun x : ℝ => gamma x kD) 0 := by
      unfold gamma
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · norm_num
    simpa only [gamma, mul_zero, Nat.cast_eq_zero, zero_div] using
      hcont.tendsto.comp hu
  have hq : Tendsto (fun t => gamma (u t) kD * cD) l (nhds 0) := by
    simpa only [zero_mul] using hgammaD.mul_const cD
  have hq_lt : ∀ᶠ t in l, gamma (u t) kD * cD < 1 :=
    (tendsto_order.1 hq).2 1 (by norm_num)
  refine ⟨remainder, ?_, ?_⟩
  · have hremN := p13_gamma_sub_linear_isBigO u hu kN
      (fun t => (run t).numeratorGammaValid)
    have hremD := p13_gamma_sub_linear_isBigO u hu kD
      (fun t => (run t).denominatorGammaValid)
    have huO1 : u =O[l] (fun _ : ι => (1 : ℝ)) := hu.isBigO_one ℝ
    have hsqOu : (fun t => (u t) ^ 2) =O[l] u := by
      simpa only [pow_two, mul_one] using (isBigO_refl u l).mul huO1
    have hlinearD : (fun t => kd * u t) =O[l] u := by
      exact (isBigO_refl u l).const_mul_left kd
    have hgammaDO : (fun t => gamma (u t) kD) =O[l] u := by
      have h := (hremD.trans hsqOu).add hlinearD
      simpa only [kd, kD, sub_add_cancel] using h
    have hpartN :
        (fun t => cN * (gamma (u t) kN - kn * u t))
          =O[l] (fun t => (u t) ^ 2) := by
      simpa only [kn, kN] using hremN.const_mul_left cN
    have hpartD :
        (fun t => cD * (gamma (u t) kD - kd * u t))
          =O[l] (fun t => (u t) ^ 2) := by
      simpa only [kd, kD] using hremD.const_mul_left cD
    have hArem :
        (fun t =>
          (gamma (u t) kN * cN + gamma (u t) kD * cD) - u t * C)
          =O[l] (fun t => (u t) ^ 2) := by
      have h := hpartN.add hpartD
      convert h using 1
      funext t
      dsimp only [C]
      ring
    have hqO : (fun t => gamma (u t) kD * cD) =O[l] u := by
      simpa only [mul_comm] using hgammaDO.const_mul_left cD
    have huC : (fun t => u t * C) =O[l] u := by
      simpa only [mul_comm] using (isBigO_refl u l).const_mul_left C
    have hcross :
        (fun t => (u t * C) * (gamma (u t) kD * cD))
          =O[l] (fun t => (u t) ^ 2) := by
      simpa only [pow_two] using huC.mul hqO
    have hnum :
        (fun t =>
          ((gamma (u t) kN * cN + gamma (u t) kD * cD) - u t * C) +
            (u t * C) * (gamma (u t) kD * cD))
          =O[l] (fun t => (u t) ^ 2) := hArem.add hcross
    have hdenT :
        Tendsto (fun t => 1 - gamma (u t) kD * cD) l (nhds 1) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub hq
    have hinvT :
        Tendsto (fun t => (1 - gamma (u t) kD * cD)⁻¹) l (nhds 1) := by
      simpa only [inv_one] using hdenT.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hinvO :
        (fun t => (1 - gamma (u t) kD * cD)⁻¹)
          =O[l] (fun _ : ι => (1 : ℝ)) := hinvT.isBigO_one ℝ
    have hproduct :
        (fun t =>
          (((gamma (u t) kN * cN + gamma (u t) kD * cD) - u t * C) +
              (u t * C) * (gamma (u t) kD * cD)) *
            (1 - gamma (u t) kD * cD)⁻¹)
          =O[l] (fun t => (u t) ^ 2) := by
      simpa only [mul_one] using hnum.mul hinvO
    apply hproduct.congr' ?_ EventuallyEq.rfl
    filter_upwards [hq_lt] with t hqt
    have hne : 1 - gamma (u t) kD * cD ≠ 0 :=
      ne_of_gt (sub_pos.mpr hqt)
    dsimp only [remainder]
    field_simp [hne]
    ring
  · filter_upwards [hq_lt] with t hqt
    have hgammaN_nonneg : 0 ≤ gamma (u t) kN := by
      unfold gamma
      exact div_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (run t).u_nonneg)
        (le_of_lt (sub_pos.mpr (run t).numeratorGammaValid))
    have hgammaD_nonneg : 0 ≤ gamma (u t) kD := by
      unfold gamma
      exact div_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (run t).u_nonneg)
        (le_of_lt (sub_pos.mpr (run t).denominatorGammaValid))
    have hNsum :
        |Nh t - N| ≤ gamma (u t) kN * ∑ j, |a j| := by
      apply p13_abs_sum_perturbation
      · exact hgammaN_nonneg
      · intro j
        exact ((run t).numeratorCounter j).gamma_le
          (run t).numeratorGammaValid
    have hDsum :
        |Dh t - D| ≤ gamma (u t) kD * ∑ j, |b j| := by
      apply p13_abs_sum_perturbation
      · exact hgammaD_nonneg
      · intro j
        exact ((run t).denominatorCounter j).gamma_le
          (run t).denominatorGammaValid
    have hNerr :
        |Nh t - N| ≤ (gamma (u t) kN * cN) * |N| := by
      calc
        |Nh t - N| ≤ gamma (u t) kN * ∑ j, |a j| := hNsum
        _ = (gamma (u t) kN * cN) * |N| := by
          rw [hcN]
          field_simp [abs_ne_zero.mpr hN]
    have hDerr :
        |Dh t - D| ≤ (gamma (u t) kD * cD) * |D| := by
      calc
        |Dh t - D| ≤ gamma (u t) kD * ∑ j, |b j| := hDsum
        _ = (gamma (u t) kD * cD) * |D| := by
          rw [hcD]
          field_simp [abs_ne_zero.mpr hD]
    have hratio := p13_ratio_perturbation N D (Nh t) (Dh t)
      (gamma (u t) kN * cN) (gamma (u t) kD * cD)
      hN hD (mul_nonneg hgammaN_nonneg hcN_nonneg)
      (mul_nonneg hgammaD_nonneg hcD_nonneg) hNerr hDerr hqt
    have hexpansion :
        (gamma (u t) kN * cN + gamma (u t) kD * cD) /
            (1 - gamma (u t) kD * cD) =
          u t * C + remainder t := by
      dsimp only [remainder]
      ring
    rw [p13SecondBarycentricRelativeError, hexact, hcomputed]
    calc
      |N / D - Nh t / Dh t| / |N / D| ≤
          (gamma (u t) kN * cN + gamma (u t) kD * cD) /
            (1 - gamma (u t) kD * cD) := hratio
      _ = u t * C + remainder t := hexpansion
      _ ≤ u t * C + |remainder t| :=
        add_le_add (le_refl (u t * C)) (le_abs_self (remainder t))
      _ = u t * p13SecondBarycentricFirstOrderCoefficient n cN cD +
          |remainder t| := by
        simp only [C, kn, kd, kN, kD,
          p13SecondBarycentricFirstOrderCoefficient]

end HighamBench
