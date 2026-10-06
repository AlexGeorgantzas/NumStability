import HighamBench.P13Definitions

namespace HighamBench

open scoped BigOperators

private lemma p13_abs_weighted_perturbation
    {m : ℕ} (a e : Fin m → ℝ) (g : ℝ)
    (he : ∀ i, |e i - 1| ≤ g) :
    |∑ i, a i * e i - ∑ i, a i| ≤ g * ∑ i, |a i| := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i, (a i * e i - a i)| ≤ ∑ i, |a i * e i - a i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |e i - 1| := by
      apply Finset.sum_congr rfl
      intro i _
      have : a i * e i - a i = a i * (e i - 1) := by ring
      rw [this, abs_mul]
    _ ≤ ∑ i, |a i| * g := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)
    _ = g * ∑ i, |a i| := by
      rw [← Finset.sum_mul]
      ring

private lemma p13_relative_quotient_perturbation
    {N D a b : ℝ} (hN : N ≠ 0) (hD : D ≠ 0) (hb : |b| < 1) :
    |N / D - (N * (1 + a)) / (D * (1 + b))| / |N / D| ≤
      (|a| + |b|) / (1 - |b|) := by
  have h_one_b : 1 + b ≠ 0 := by
    intro h
    have : b = -1 := by linarith
    rw [this, abs_neg, abs_one] at hb
    linarith
  have hND : N / D ≠ 0 := div_ne_zero hN hD
  have hdiff :
      N / D - (N * (1 + a)) / (D * (1 + b)) =
        (N / D) * ((b - a) / (1 + b)) := by
    field_simp
    ring
  rw [hdiff, abs_mul]
  have h_abs_ND : |N / D| ≠ 0 := abs_ne_zero.mpr hND
  rw [mul_div_cancel_left₀ _ h_abs_ND]
  rw [abs_div]
  have hnum : |b - a| ≤ |a| + |b| := by
    calc
      |b - a| ≤ |b| + |a| := abs_sub _ _
      _ = |a| + |b| := by ring
  have hden : 1 - |b| ≤ |1 + b| := by
    have htri := abs_add_le (1 + b) (-b)
    simp only [add_neg_cancel_right, abs_one, abs_neg] at htri
    linarith
  have hpos : 0 < 1 - |b| := sub_pos.mpr hb
  exact div_le_div₀ (by positivity) hnum hpos hden

private lemma p13_gamma_estimates (v : ℝ) (k : ℕ)
    (hv : 0 ≤ v) (hhalf : (k : ℝ) * v ≤ 1 / 2) :
    0 ≤ gamma v k ∧
      gamma v k ≤ (k : ℝ) * v + 2 * (k : ℝ) ^ 2 * v ^ 2 ∧
      gamma v k ≤ 2 * (k : ℝ) * v := by
  let z : ℝ := (k : ℝ) * v
  have hz0 : 0 ≤ z := mul_nonneg (Nat.cast_nonneg _) hv
  have hzhalf : z ≤ 1 / 2 := hhalf
  have hden : 0 < 1 - z := by linarith
  have hsq : 0 ≤ z ^ 2 * (1 - 2 * z) :=
    mul_nonneg (sq_nonneg z) (by linarith)
  have hlin : 0 ≤ z * (1 - 2 * z) :=
    mul_nonneg hz0 (by linarith)
  dsimp [gamma, z] at *
  refine ⟨div_nonneg hz0 hden.le, ?_, ?_⟩
  · apply (div_le_iff₀ hden).2
    nlinarith
  · apply (div_le_iff₀ hden).2
    nlinarith

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
  let A : ℝ := p13SecondBarycentricDataCondition problem
  let B : ℝ := p13SecondBarycentricOneCondition problem
  let a : ℝ := p13NumeratorCounterLength n
  let b : ℝ := p13DenominatorCounterLength n
  let C : ℝ := a * A + b * B
  let Q : ℝ := a ^ 2 * A + b ^ 2 * B
  let K : ℝ := 2 * Q + 8 * C * b * B
  have hA : 0 ≤ A := by
    dsimp [A, p13SecondBarycentricDataCondition, p13Condition]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B, p13SecondBarycentricOneCondition, p13Condition]
    positivity
  have ha : 0 < a := by
    dsimp [a, p13NumeratorCounterLength]
    positivity
  have hb : 0 < b := by
    dsimp [b, p13DenominatorCounterLength]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨(fun t => K * (u t) ^ 2), ?_, ?_⟩
  · exact Asymptotics.isBigO_const_mul_self K (fun t => (u t) ^ 2) l
  · have hua : ∀ᶠ t in l, u t < 1 / (2 * a) :=
      (tendsto_order.1 hu).2 _ (by positivity)
    have hub : ∀ᶠ t in l, u t < 1 / (2 * b) :=
      (tendsto_order.1 hu).2 _ (by positivity)
    have huB : ∀ᶠ t in l, u t < 1 / (4 * b * (B + 1)) :=
      (tendsto_order.1 hu).2 _ (by positivity)
    filter_upwards [hua, hub, huB] with t hut_a hut_b hut_B
    let v : ℝ := u t
    let coeff : Fin (n + 1) → ℝ :=
      p13DirectBarycentricCoefficient problem.nodes problem.x
    let N : ℝ := ∑ j, coeff j * problem.data j
    let D : ℝ := ∑ j, coeff j
    let N' : ℝ :=
      ∑ j, coeff j * problem.data j * ((run t).numeratorCounter j).value
    let D' : ℝ :=
      ∑ j, coeff j * ((run t).denominatorCounter j).value
    let εN : ℝ := (N' - N) / N
    let εD : ℝ := (D' - D) / D
    let gN : ℝ := gamma v (p13NumeratorCounterLength n)
    let gD : ℝ := gamma v (p13DenominatorCounterLength n)
    have hv : 0 ≤ v := (run t).u_nonneg
    have hva : a * v ≤ 1 / 2 := by
      have h := mul_lt_mul_of_pos_left hut_a ha
      have heq : a * (1 / (2 * a)) = 1 / 2 := by field_simp
      rw [heq] at h
      exact h.le
    have hvb : b * v ≤ 1 / 2 := by
      have h := mul_lt_mul_of_pos_left hut_b hb
      have heq : b * (1 / (2 * b)) = 1 / 2 := by field_simp
      rw [heq] at h
      exact h.le
    have hgN := p13_gamma_estimates v (p13NumeratorCounterLength n) hv (by
      simpa [a] using hva)
    have hgD := p13_gamma_estimates v (p13DenominatorCounterLength n) hv (by
      simpa [b] using hvb)
    have hcounterN : ∀ j, |((run t).numeratorCounter j).value - 1| ≤ gN := by
      intro j
      exact (run t).numeratorCounter j |>.gamma_le (run t).numeratorGammaValid
    have hcounterD : ∀ j, |((run t).denominatorCounter j).value - 1| ≤ gD := by
      intro j
      exact (run t).denominatorCounter j |>.gamma_le (run t).denominatorGammaValid
    have hNpert :
        |N' - N| ≤ gN * ∑ j, |coeff j * problem.data j| := by
      exact p13_abs_weighted_perturbation
        (fun j => coeff j * problem.data j)
        (fun j => ((run t).numeratorCounter j).value) gN hcounterN
    have hDpert : |D' - D| ≤ gD * ∑ j, |coeff j| := by
      exact p13_abs_weighted_perturbation coeff
        (fun j => ((run t).denominatorCounter j).value) gD hcounterD
    have hN : N ≠ 0 := by
      simpa [N, coeff, p13SecondBarycentricNumerator,
        p13InterpolationValue] using hnumerator
    have hD : D ≠ 0 := by
      simpa [D, coeff, p13SecondBarycentricDenominator,
        p13InterpolationValue] using hdenominator
    have hεN : |εN| ≤ gN * A := by
      rw [show |εN| = |N' - N| / |N| by simp [εN, abs_div]]
      calc
        |N' - N| / |N| ≤
            (gN * ∑ j, |coeff j * problem.data j|) / |N| :=
          div_le_div_of_nonneg_right hNpert (abs_nonneg _)
        _ = gN * A := by
          dsimp [A, p13SecondBarycentricDataCondition, p13Condition,
            p13InterpolationValue, N, coeff]
          ring
    have hεD : |εD| ≤ gD * B := by
      rw [show |εD| = |D' - D| / |D| by simp [εD, abs_div]]
      calc
        |D' - D| / |D| ≤ (gD * ∑ j, |coeff j|) / |D| :=
          div_le_div_of_nonneg_right hDpert (abs_nonneg _)
        _ = gD * B := by
          dsimp [B, p13SecondBarycentricOneCondition, p13Condition,
            p13InterpolationValue, D, coeff]
          simp only [mul_one]
          ring
    have hvB : 2 * b * B * v < 1 / 2 := by
      have hdenB : 0 < 4 * b * (B + 1) := by positivity
      have hfull : 4 * b * (B + 1) * v < 1 := by
        have h := (lt_div_iff₀ hdenB).mp hut_B
        nlinarith
      have hcomp : 4 * b * B * v ≤ 4 * b * (B + 1) * v := by
        gcongr
        linarith
      nlinarith
    have hgDB : gD * B ≤ 2 * b * B * v := by
      have h := mul_le_mul_of_nonneg_right hgD.2.2 hB
      dsimp [gD, b] at h ⊢
      convert h using 1 <;> ring
    have hεDhalf : |εD| < 1 / 2 :=
      lt_of_le_of_lt hεD (lt_of_le_of_lt hgDB hvB)
    have hsmallD : |εD| < 1 := by linarith
    have hN'id : N' = N * (1 + εN) := by
      dsimp [εN]
      field_simp
      ring
    have hD'id : D' = D * (1 + εD) := by
      dsimp [εD]
      field_simp
      ring
    have hcomputed : p13SecondBarycentricComputed (run t) = N' / D' := by
      have hnum :
          (∑ j, coeff j * ((run t).weightCounter j).value * problem.data j *
              ((run t).numeratorEvaluationCounter j).value) *
              (run t).quotientCounter.value = N' := by
        rw [Finset.sum_mul]
        dsimp [N']
        apply Finset.sum_congr rfl
        intro j _
        rw [(run t).numeratorCounter_eq]
        ring
      have hden :
          (∑ j, coeff j * ((run t).weightCounter j).value *
              ((run t).denominatorEvaluationCounter j).value) = D' := by
        dsimp [D']
        apply Finset.sum_congr rfl
        intro j _
        rw [(run t).denominatorCounter_eq]
        ring
      rw [p13SecondBarycentricComputed, div_mul_eq_mul_div, hnum, hden]
    have hexact : p13SecondBarycentricExact problem = N / D := by
      dsimp [p13SecondBarycentricExact, p13SecondBarycentricNumerator,
        p13SecondBarycentricDenominator, p13InterpolationValue, N, D, coeff]
      simp
    have hrelative :
        p13SecondBarycentricRelativeError (run t) ≤
          (|εN| + |εD|) / (1 - |εD|) := by
      rw [p13SecondBarycentricRelativeError, hexact, hcomputed, hN'id, hD'id]
      exact p13_relative_quotient_perturbation hN hD hsmallD
    have hgNquad : gN ≤ a * v + 2 * a ^ 2 * v ^ 2 := by
      simpa [gN, a] using hgN.2.1
    have hgDquad : gD ≤ b * v + 2 * b ^ 2 * v ^ 2 := by
      simpa [gD, b] using hgD.2.1
    have hgNlin : gN ≤ 2 * a * v := by
      simpa [gN, a] using hgN.2.2
    have hxquad :
        |εN| + |εD| ≤ v * C + 2 * Q * v ^ 2 := by
      calc
        |εN| + |εD| ≤ gN * A + gD * B := add_le_add hεN hεD
        _ ≤ (a * v + 2 * a ^ 2 * v ^ 2) * A +
              (b * v + 2 * b ^ 2 * v ^ 2) * B :=
          add_le_add (mul_le_mul_of_nonneg_right hgNquad hA)
            (mul_le_mul_of_nonneg_right hgDquad hB)
        _ = v * C + 2 * Q * v ^ 2 := by
          dsimp [C, Q]
          ring
    have hxlin : |εN| + |εD| ≤ 2 * C * v := by
      calc
        |εN| + |εD| ≤ gN * A + gD * B := add_le_add hεN hεD
        _ ≤ (2 * a * v) * A + (2 * b * v) * B :=
          add_le_add (mul_le_mul_of_nonneg_right hgNlin hA)
            (mul_le_mul_of_nonneg_right hgD.2.2 hB)
        _ = 2 * C * v := by
          dsimp [C]
          ring
    have hcross :
        (|εN| + |εD|) * |εD| / (1 - |εD|) ≤
          8 * C * b * B * v ^ 2 := by
      have hxy0 : 0 ≤ (|εN| + |εD|) * |εD| := by positivity
      have hdenhalf : 1 / 2 ≤ 1 - |εD| := by linarith
      calc
        (|εN| + |εD|) * |εD| / (1 - |εD|) ≤
            (|εN| + |εD|) * |εD| / (1 / 2) :=
          div_le_div_of_nonneg_left hxy0 (by norm_num) hdenhalf
        _ = 2 * ((|εN| + |εD|) * |εD|) := by ring
        _ ≤ 2 * ((2 * C * v) * (2 * b * B * v)) := by
          gcongr
          exact le_trans hεD hgDB
        _ = 8 * C * b * B * v ^ 2 := by ring
    have hquotient :
        (|εN| + |εD|) / (1 - |εD|) ≤ v * C + K * v ^ 2 := by
      have hden_ne : 1 - |εD| ≠ 0 := by linarith
      have hid :
          (|εN| + |εD|) / (1 - |εD|) =
            (|εN| + |εD|) +
              (|εN| + |εD|) * |εD| / (1 - |εD|) := by
        field_simp
        ring
      rw [hid]
      calc
        (|εN| + |εD|) +
              (|εN| + |εD|) * |εD| / (1 - |εD|) ≤
            (v * C + 2 * Q * v ^ 2) + 8 * C * b * B * v ^ 2 :=
          add_le_add hxquad hcross
        _ = v * C + K * v ^ 2 := by
          dsimp [K]
          ring
    calc
      p13SecondBarycentricRelativeError (run t) ≤
          (|εN| + |εD|) / (1 - |εD|) := hrelative
      _ ≤ v * C + K * v ^ 2 := hquotient
      _ = u t * p13SecondBarycentricFirstOrderCoefficient n A B +
            |K * (u t) ^ 2| := by
        rw [abs_of_nonneg (mul_nonneg hK (sq_nonneg _))]
        dsimp [v, C, a, b, p13SecondBarycentricFirstOrderCoefficient]

end HighamBench
