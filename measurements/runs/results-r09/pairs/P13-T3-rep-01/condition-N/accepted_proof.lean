import HighamBench.P13Definitions

namespace HighamBench

lemma p13_sum_perturbation_bound {m : ℕ} (a e : Fin m → ℝ) (g : ℝ)
    (he : ∀ i, |e i - 1| ≤ g) :
    |(∑ i, a i * e i) - ∑ i, a i| ≤ g * ∑ i, |a i| := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i, (a i * e i - a i)| ≤ ∑ i, |a i * e i - a i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, g * |a i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [show a i * e i - a i = a i * (e i - 1) by ring, abs_mul]
      calc
        |a i| * |e i - 1| ≤ |a i| * g :=
          mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)
        _ = g * |a i| := by ring
    _ = g * ∑ i, |a i| := by rw [Finset.mul_sum]

lemma p13_quotient_relative_error_bound
    (a b ah bh A B : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : |(ah - a) / a| ≤ A) (hB : |(bh - b) / b| ≤ B)
    (hA0 : 0 ≤ A) (hBlt : B < 1) :
    |a / b - ah / bh| / |a / b| ≤ (A + B) / (1 - B) := by
  have hylt : |(bh - b) / b| < 1 := lt_of_le_of_lt hB hBlt
  have hbh : bh ≠ 0 := by
    intro h
    simp [h, hb] at hylt
  have hab : a / b ≠ 0 := div_ne_zero ha hb
  have hid :
      a / b - ah / bh =
        (a / b) * (((bh - b) / b - (ah - a) / a) /
          (1 + (bh - b) / b)) := by
    field_simp [ha, hb, hbh]
    ring
  rw [hid, abs_mul, mul_div_cancel_left₀ _ (abs_ne_zero.mpr hab), abs_div]
  have hnum :
      |(bh - b) / b - (ah - a) / a| ≤ A + B := by
    calc
      |(bh - b) / b - (ah - a) / a| ≤
          |(bh - b) / b| + |(ah - a) / a| := abs_sub _ _
      _ ≤ B + A := add_le_add hB hA
      _ = A + B := by ring
  have hden : 1 - B ≤ |1 + (bh - b) / b| := by
    have htri :
        (1 : ℝ) ≤ |1 + (bh - b) / b| + |(bh - b) / b| := by
      calc
        (1 : ℝ) = |(1 + (bh - b) / b) - (bh - b) / b| := by
          ring_nf
          norm_num
        _ ≤ |1 + (bh - b) / b| + |(bh - b) / b| := abs_sub _ _
    linarith
  apply div_le_div₀
  · exact add_nonneg hA0 (le_trans (abs_nonneg _) hB)
  · exact hnum
  · linarith
  · exact hden

lemma p13_rational_remainder_tendsto {ι : Type*} {l : Filter ι}
    (u : ι → ℝ) (hu : Filter.Tendsto u l (nhds 0))
    (a b c d e : ℝ) :
    Filter.Tendsto
      (fun t =>
        (c * (a + b * (1 + d)) - a * b * e - a * b * u t * c * (1 + d)) /
          ((1 - a * u t) * (1 - b * u t * (1 + d))))
      l (nhds (c * (a + b * (1 + d)) - a * b * e)) := by
  have ha : Filter.Tendsto (fun t => a * u t) l (nhds 0) := by
    simpa using hu.const_mul a
  have hb : Filter.Tendsto (fun t => b * u t * (1 + d)) l (nhds 0) := by
    simpa using (hu.const_mul b).mul_const (1 + d)
  have hlast :
      Filter.Tendsto (fun t => a * b * u t * c * (1 + d)) l (nhds 0) := by
    convert (hu.const_mul (a * b)).mul_const (c * (1 + d)) using 1
    · funext t
      ring
    · norm_num
  have hnum : Filter.Tendsto
      (fun t => c * (a + b * (1 + d)) - a * b * e -
        a * b * u t * c * (1 + d)) l
      (nhds (c * (a + b * (1 + d)) - a * b * e)) := by
    simpa using tendsto_const_nhds.sub hlast
  have hleft : Filter.Tendsto (fun t => 1 - a * u t) l (nhds 1) := by
    simpa using tendsto_const_nhds.sub ha
  have hright : Filter.Tendsto
      (fun t => 1 - b * u t * (1 + d)) l (nhds 1) := by
    simpa using tendsto_const_nhds.sub hb
  simpa using hnum.div (hleft.mul hright) (by norm_num)

lemma p13_gamma_nonneg (z : ℝ) (k : ℕ) (hz : 0 ≤ z)
    (hk : GammaValid z k) : 0 ≤ gamma z k := by
  rw [gamma]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hz)
    (le_of_lt (sub_pos.mpr hk))

lemma p13_gamma_tendsto_zero {ι : Type*} {l : Filter ι} (u : ι → ℝ)
    (hu : Filter.Tendsto u l (nhds 0)) (k : ℕ) :
    Filter.Tendsto (fun t => gamma (u t) k) l (nhds 0) := by
  have hku : Filter.Tendsto (fun t => (k : ℝ) * u t) l (nhds 0) := by
    simpa using hu.const_mul (k : ℝ)
  have hden : Filter.Tendsto (fun t => 1 - (k : ℝ) * u t) l (nhds 1) := by
    simpa using tendsto_const_nhds.sub hku
  simpa [gamma] using hku.div hden (by norm_num)

lemma p13_gamma_remainder_identity (z a b c d : ℝ)
    (ha : 1 - a * z ≠ 0) (hb : 1 - b * z ≠ 0)
    (hout : 1 - (b * z / (1 - b * z)) * d ≠ 0) :
    ((a * z / (1 - a * z)) * c + (b * z / (1 - b * z)) * d) /
        (1 - (b * z / (1 - b * z)) * d) =
      z * (a * c + b * d) + z ^ 2 *
        ((a ^ 2 * c / (1 - a * z) + b ^ 2 * d / (1 - b * z) +
            (a * c + b * d) * b * d / (1 - b * z)) /
          (1 - (b * z / (1 - b * z)) * d)) := by
  let den := 1 - (b * z / (1 - b * z)) * d
  let E := a ^ 2 * c / (1 - a * z) + b ^ 2 * d / (1 - b * z) +
    (a * c + b * d) * b * d / (1 - b * z)
  change ((a * z / (1 - a * z)) * c + (b * z / (1 - b * z)) * d) / den =
    z * (a * c + b * d) + z ^ 2 * (E / den)
  apply (div_eq_iff hout).2
  have hcancel : z ^ 2 * (E / den) * den = z ^ 2 * E := by
    rw [mul_assoc, div_mul_cancel₀ E hout]
  rw [add_mul, hcancel]
  dsimp [E, den]
  have hb' : 1 - z * b ≠ 0 := by simpa [mul_comm] using hb
  field_simp [ha, hb, hout]
  field_simp [hb']
  ring

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
  let a : ℝ := p13NumeratorCounterLength n
  let b : ℝ := p13DenominatorCounterLength n
  let c : ℝ := p13SecondBarycentricDataCondition problem
  let d : ℝ := p13SecondBarycentricOneCondition problem
  let C : ℝ := a * c + b * d
  let q : ι → ℝ := fun t =>
    (a ^ 2 * c / (1 - a * u t) + b ^ 2 * d / (1 - b * u t) +
        C * b * d / (1 - b * u t)) /
      (1 - gamma (u t) (p13DenominatorCounterLength n) * d)
  let remainder : ι → ℝ := fun t => (u t) ^ 2 * q t
  have ha_lim : Filter.Tendsto (fun t => a * u t) l (nhds 0) := by
    simpa using hu.const_mul a
  have hb_lim : Filter.Tendsto (fun t => b * u t) l (nhds 0) := by
    simpa using hu.const_mul b
  have hda : Filter.Tendsto (fun t => 1 - a * u t) l (nhds 1) := by
    simpa using tendsto_const_nhds.sub ha_lim
  have hdb : Filter.Tendsto (fun t => 1 - b * u t) l (nhds 1) := by
    simpa using tendsto_const_nhds.sub hb_lim
  have hga : Filter.Tendsto
      (fun t => gamma (u t) (p13DenominatorCounterLength n)) l (nhds 0) :=
    p13_gamma_tendsto_zero u hu _
  have hgd : Filter.Tendsto
      (fun t => gamma (u t) (p13DenominatorCounterLength n) * d) l
      (nhds 0) := by
    simpa using hga.mul_const d
  have hgden : Filter.Tendsto
      (fun t => 1 - gamma (u t) (p13DenominatorCounterLength n) * d) l
      (nhds 1) := by
    simpa using tendsto_const_nhds.sub hgd
  have ht1 : Filter.Tendsto
      (fun t => a ^ 2 * c / (1 - a * u t)) l (nhds (a ^ 2 * c)) := by
    simpa using (tendsto_const_nhds.div hda (by norm_num) :
      Filter.Tendsto (fun t => (a ^ 2 * c) / (1 - a * u t)) l
        (nhds ((a ^ 2 * c) / 1)))
  have ht2 : Filter.Tendsto
      (fun t => b ^ 2 * d / (1 - b * u t)) l (nhds (b ^ 2 * d)) := by
    simpa using (tendsto_const_nhds.div hdb (by norm_num) :
      Filter.Tendsto (fun t => (b ^ 2 * d) / (1 - b * u t)) l
        (nhds ((b ^ 2 * d) / 1)))
  have ht3 : Filter.Tendsto
      (fun t => C * b * d / (1 - b * u t)) l (nhds (C * b * d)) := by
    simpa using (tendsto_const_nhds.div hdb (by norm_num) :
      Filter.Tendsto (fun t => (C * b * d) / (1 - b * u t)) l
        (nhds ((C * b * d) / 1)))
  have hq : Filter.Tendsto q l
      (nhds (a ^ 2 * c + b ^ 2 * d + C * b * d)) := by
    dsimp [q]
    simpa using (ht1.add ht2 |>.add ht3).div hgden (by norm_num)
  have hremainder : remainder =O[l] (fun t => (u t) ^ 2) := by
    have hpow := Asymptotics.isBigO_refl (fun t => (u t) ^ 2) l
    have hqO := hq.isBigO_one ℝ
    simpa [remainder] using hpow.mul hqO
  refine ⟨remainder, hremainder, ?_⟩
  have hsmall : ∀ᶠ t in l,
      gamma (u t) (p13DenominatorCounterLength n) * d < 1 :=
    (tendsto_order.1 hgd).2 1 (by norm_num)
  filter_upwards [hsmall] with t hsmall_t
  let coeff : Fin (n + 1) → ℝ :=
    p13DirectBarycentricCoefficient problem.nodes problem.x
  let dataTerm : Fin (n + 1) → ℝ := fun j => coeff j * problem.data j
  let oneTerm : Fin (n + 1) → ℝ := fun j => coeff j * 1
  let N : ℝ := ∑ j, dataTerm j
  let D : ℝ := ∑ j, oneTerm j
  let Nh : ℝ := ∑ j, dataTerm j * ((run t).numeratorCounter j).value
  let Dh : ℝ := ∑ j, oneTerm j * ((run t).denominatorCounter j).value
  have hN_orig : N = p13SecondBarycentricNumerator problem := by rfl
  have hD_orig : D = p13SecondBarycentricDenominator problem := by rfl
  have hN0 : N ≠ 0 := by simpa [hN_orig] using hnumerator
  have hD0 : D ≠ 0 := by simpa [hD_orig] using hdenominator
  have hc_eq : c = (∑ j, |dataTerm j|) / |N| := by rfl
  have hd_eq : d = (∑ j, |oneTerm j|) / |D| := by rfl
  have hc0 : 0 ≤ c := by
    rw [hc_eq]
    positivity
  have hd0 : 0 ≤ d := by
    rw [hd_eq]
    positivity
  let ga : ℝ := gamma (u t) (p13NumeratorCounterLength n)
  let gb : ℝ := gamma (u t) (p13DenominatorCounterLength n)
  have hga0 : 0 ≤ ga :=
    p13_gamma_nonneg (u t) _ (run t).u_nonneg (run t).numeratorGammaValid
  have hgb0 : 0 ≤ gb :=
    p13_gamma_nonneg (u t) _ (run t).u_nonneg (run t).denominatorGammaValid
  have hDN : |Nh - N| ≤ ga * ∑ j, |dataTerm j| := by
    simpa [Nh, N, ga] using
      p13_sum_perturbation_bound dataTerm
        (fun j => ((run t).numeratorCounter j).value)
        (gamma (u t) (p13NumeratorCounterLength n))
        (fun j => ((run t).numeratorCounter j).gamma_le
          (run t).numeratorGammaValid)
  have hDD : |Dh - D| ≤ gb * ∑ j, |oneTerm j| := by
    simpa [Dh, D, gb] using
      p13_sum_perturbation_bound oneTerm
        (fun j => ((run t).denominatorCounter j).value)
        (gamma (u t) (p13DenominatorCounterLength n))
        (fun j => ((run t).denominatorCounter j).gamma_le
          (run t).denominatorGammaValid)
  have hNabs : 0 < |N| := abs_pos.mpr hN0
  have hDabs : 0 < |D| := abs_pos.mpr hD0
  have hAN : |(Nh - N) / N| ≤ ga * c := by
    rw [abs_div]
    calc
      |Nh - N| / |N| ≤ (ga * ∑ j, |dataTerm j|) / |N| :=
        (div_le_div_iff_of_pos_right hNabs).2 hDN
      _ = ga * c := by rw [hc_eq]; ring
  have hBD : |(Dh - D) / D| ≤ gb * d := by
    rw [abs_div]
    calc
      |Dh - D| / |D| ≤ (gb * ∑ j, |oneTerm j|) / |D| :=
        (div_le_div_iff_of_pos_right hDabs).2 hDD
      _ = gb * d := by rw [hd_eq]; ring
  have hNh_eq : Nh =
      (∑ j, coeff j * ((run t).weightCounter j).value * problem.data j *
        ((run t).numeratorEvaluationCounter j).value) *
          (run t).quotientCounter.value := by
    dsimp [Nh, dataTerm]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(run t).numeratorCounter_eq j]
    ring
  have hDh_eq : Dh =
      ∑ j, coeff j * ((run t).weightCounter j).value *
        ((run t).denominatorEvaluationCounter j).value := by
    dsimp [Dh, oneTerm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(run t).denominatorCounter_eq j]
    ring
  have hcomputed : p13SecondBarycentricComputed (run t) = Nh / Dh := by
    rw [p13SecondBarycentricComputed]
    change
      ((∑ j, coeff j * ((run t).weightCounter j).value * problem.data j *
          ((run t).numeratorEvaluationCounter j).value) /
        (∑ j, coeff j * ((run t).weightCounter j).value *
          ((run t).denominatorEvaluationCounter j).value)) *
          (run t).quotientCounter.value = Nh / Dh
    rw [← hDh_eq, hNh_eq]
    field_simp
  have hrelative : p13SecondBarycentricRelativeError (run t) =
      |N / D - Nh / Dh| / |N / D| := by
    rw [p13SecondBarycentricRelativeError, p13SecondBarycentricExact,
      hcomputed, ← hN_orig, ← hD_orig]
  have hsmall_gb : gb * d < 1 := by simpa [gb] using hsmall_t
  have hquotient :
      |N / D - Nh / Dh| / |N / D| ≤
        (ga * c + gb * d) / (1 - gb * d) :=
    p13_quotient_relative_error_bound N D Nh Dh (ga * c) (gb * d)
      hN0 hD0 hAN hBD (mul_nonneg hga0 hc0) hsmall_gb
  have ha_den : 1 - a * u t ≠ 0 := by
    apply ne_of_gt
    apply sub_pos.mpr
    simpa [a, GammaValid] using (run t).numeratorGammaValid
  have hb_den : 1 - b * u t ≠ 0 := by
    apply ne_of_gt
    apply sub_pos.mpr
    simpa [b, GammaValid] using (run t).denominatorGammaValid
  have hout : 1 - (b * u t / (1 - b * u t)) * d ≠ 0 := by
    apply ne_of_gt
    apply sub_pos.mpr
    simpa [gb, gamma, b] using hsmall_gb
  have hidentity :
      (ga * c + gb * d) / (1 - gb * d) =
        u t * C + (u t) ^ 2 * q t := by
    simpa [ga, gb, q, C, gamma, a, b] using
      p13_gamma_remainder_identity (u t) a b c d ha_den hb_den hout
  calc
    p13SecondBarycentricRelativeError (run t) ≤
        (ga * c + gb * d) / (1 - gb * d) := by
      rw [hrelative]
      exact hquotient
    _ = u t * C + remainder t := by rw [hidentity]
    _ ≤ u t * C + |remainder t| :=
      add_le_add (le_refl _) (le_abs_self (remainder t))
    _ = u t * p13SecondBarycentricFirstOrderCoefficient n
          (p13SecondBarycentricDataCondition problem)
          (p13SecondBarycentricOneCondition problem) + |remainder t| := by
      simp [C, a, b, c, d, p13SecondBarycentricFirstOrderCoefficient]

end HighamBench
