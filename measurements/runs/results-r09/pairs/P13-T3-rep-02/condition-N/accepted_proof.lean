import HighamBench.P13Definitions

namespace HighamBench

open scoped BigOperators

lemma gamma_le_linear_quadratic {u : ℝ} {k : ℕ}
    (hu : 0 ≤ u) (hku : (k : ℝ) * u ≤ 1 / 2) :
    gamma u k ≤ (k : ℝ) * u + 2 * (k : ℝ) ^ 2 * u ^ 2 := by
  rw [gamma]
  have hd : 0 < 1 - (k : ℝ) * u := by nlinarith
  rw [div_le_iff₀ hd]
  nlinarith [sq_nonneg ((k : ℝ) * u)]

lemma abs_sum_mul_sub_sum_le {m : ℕ} (a v : Fin m → ℝ) (g : ℝ)
    (hv : ∀ j, |v j - 1| ≤ g) :
    |(∑ j, a j * v j) - ∑ j, a j| ≤ g * ∑ j, |a j| := by
  calc
    |(∑ j, a j * v j) - ∑ j, a j| = |∑ j, (a j * v j - a j)| := by
      congr 1
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ j, |a j * v j - a j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, g * |a j| := by
      apply Finset.sum_le_sum
      intro j hj
      rw [show a j * v j - a j = a j * (v j - 1) by ring, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hv j) (abs_nonneg (a j))]
    _ = g * ∑ j, |a j| := by rw [Finset.mul_sum]

lemma relative_quotient_le (N D N' D' : ℝ)
    (hN : N ≠ 0) (hD : D ≠ 0)
    (hsmall : |D' - D| / |D| < 1) :
    |N / D - N' / D'| / |N / D| ≤
      (|N' - N| / |N| + |D' - D| / |D|) /
        (1 - |D' - D| / |D|) := by
  have hNp : 0 < |N| := abs_pos.mpr hN
  have hDp : 0 < |D| := abs_pos.mpr hD
  have hdiff : |D' - D| < |D| := (div_lt_one hDp).mp hsmall
  have hD' : D' ≠ 0 := by
    intro hz
    subst D'
    simp only [zero_sub, abs_neg] at hdiff
    exact (lt_irrefl _ hdiff)
  have hD'p : 0 < |D'| := abs_pos.mpr hD'
  have hlower : |D| - |D' - D| ≤ |D'| := by
    have htri : |D| ≤ |D' - D| + |D'| := by
      calc
        |D| = |(D' - D) - D'| := by ring_nf; rw [abs_neg]
        _ ≤ |D' - D| + |D'| := abs_sub _ _
    linarith
  have hlowerp : 0 < |D| - |D' - D| := by linarith
  have hnum : |N * D' - N' * D| ≤
      |N| * |D' - D| + |D| * |N' - N| := by
    calc
      |N * D' - N' * D| = |N * (D' - D) - D * (N' - N)| := by ring_nf
      _ ≤ |N * (D' - D)| + |D * (N' - N)| := abs_sub _ _
      _ = |N| * |D' - D| + |D| * |N' - N| := by rw [abs_mul, abs_mul]
  have hlhs :
      |N / D - N' / D'| / |N / D| =
        |N * D' - N' * D| / (|N| * |D'|) := by
    rw [div_sub_div, abs_div, abs_div, abs_mul, div_div]
    field_simp
    ring_nf
    all_goals assumption
  rw [hlhs]
  have hbase :
      |N * D' - N' * D| / (|N| * |D'|) ≤
        (|N| * |D' - D| + |D| * |N' - N|) /
          (|N| * (|D| - |D' - D|)) := by
    calc
      _ ≤ (|N| * |D' - D| + |D| * |N' - N|) / (|N| * |D'|) := by
        exact (div_le_div_iff_of_pos_right (mul_pos hNp hD'p)).mpr hnum
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact mul_pos hNp hlowerp
        · exact mul_le_mul_of_nonneg_left hlower (le_of_lt hNp)
  calc
    _ ≤ (|N| * |D' - D| + |D| * |N' - N|) /
          (|N| * (|D| - |D' - D|)) := hbase
    _ = (|N' - N| / |N| + |D' - D| / |D|) /
          (1 - |D' - D| / |D|) := by field_simp; ring

lemma p13_computed_eq_counter_quotient {n : ℕ}
    {problem : P13SecondBarycentricProblem n} {u : ℝ}
    (run : P13SecondBarycentricExecution problem u) :
    p13SecondBarycentricComputed run =
      (∑ j, (p13DirectBarycentricCoefficient problem.nodes problem.x j *
          problem.data j) * (run.numeratorCounter j).value) /
      (∑ j, p13DirectBarycentricCoefficient problem.nodes problem.x j *
          (run.denominatorCounter j).value) := by
  let c := p13DirectBarycentricCoefficient problem.nodes problem.x
  have hn :
      (∑ j, (c j * problem.data j) * (run.numeratorCounter j).value) =
        (∑ j, c j * (run.weightCounter j).value * problem.data j *
          (run.numeratorEvaluationCounter j).value) * run.quotientCounter.value := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [run.numeratorCounter_eq]
    ring
  have hd :
      (∑ j, c j * (run.denominatorCounter j).value) =
        ∑ j, c j * (run.weightCounter j).value *
          (run.denominatorEvaluationCounter j).value := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [run.denominatorCounter_eq]
    ring
  rw [p13SecondBarycentricComputed, hn, hd]
  ring

set_option maxHeartbeats 1000000 in
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
  let A : ℝ := p13NumeratorCounterLength n
  let B : ℝ := p13DenominatorCounterLength n
  let cN := p13SecondBarycentricDataCondition problem
  let cD := p13SecondBarycentricOneCondition problem
  let C := A * cN + B * cD
  let Q := 2 * A ^ 2 * cN + 2 * B ^ 2 * cD
  let K := Q + 8 * C * B * cD
  have hcN : 0 ≤ cN := by
    dsimp [cN, p13SecondBarycentricDataCondition, p13Condition]
    positivity
  have hcD : 0 ≤ cD := by
    dsimp [cD, p13SecondBarycentricOneCondition, p13Condition]
    positivity
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hK : 0 ≤ K := by dsimp [K, Q]; positivity
  have hAu_tendsto : Filter.Tendsto (fun t => A * u t) l (nhds 0) := by
    simpa using hu.const_mul A
  have hBu_tendsto : Filter.Tendsto (fun t => B * u t) l (nhds 0) := by
    simpa using hu.const_mul B
  have hEu_tendsto : Filter.Tendsto (fun t => (2 * B * cD) * u t) l (nhds 0) := by
    simpa using hu.const_mul (2 * B * cD)
  have hAu : ∀ᶠ t in l, A * u t < 1 / 2 :=
    (tendsto_order.mp hAu_tendsto).2 (1 / 2) (by norm_num)
  have hBu : ∀ᶠ t in l, B * u t < 1 / 2 :=
    (tendsto_order.mp hBu_tendsto).2 (1 / 2) (by norm_num)
  have hEu : ∀ᶠ t in l, (2 * B * cD) * u t < 1 / 2 :=
    (tendsto_order.mp hEu_tendsto).2 (1 / 2) (by norm_num)
  refine ⟨fun t => K * (u t) ^ 2, ?_, ?_⟩
  · exact (Asymptotics.isBigO_refl (fun t => (u t) ^ 2) l).const_mul_left K
  filter_upwards [hAu, hBu, hEu] with t htA htB htE
  let a : Fin (n + 1) → ℝ := fun j =>
    p13DirectBarycentricCoefficient problem.nodes problem.x j * problem.data j
  let b : Fin (n + 1) → ℝ := fun j =>
    p13DirectBarycentricCoefficient problem.nodes problem.x j
  let N := p13SecondBarycentricNumerator problem
  let D := p13SecondBarycentricDenominator problem
  let N' := ∑ j, a j * ((run t).numeratorCounter j).value
  let D' := ∑ j, b j * ((run t).denominatorCounter j).value
  let gN := gamma (u t) (p13NumeratorCounterLength n)
  let gD := gamma (u t) (p13DenominatorCounterLength n)
  let eN := gN * cN
  let eD := gD * cD
  have hut : 0 ≤ u t := (run t).u_nonneg
  have hN : N ≠ 0 := by simpa [N] using hnumerator
  have hD : D ≠ 0 := by simpa [D] using hdenominator
  have hNsum : N = ∑ j, a j := by
    rfl
  have hDsum : D = ∑ j, b j := by
    simp [D, b, p13SecondBarycentricDenominator, p13InterpolationValue]
  have hcN_eq : cN = (∑ j, |a j|) / |N| := by
    rfl
  have hcD_eq : cD = (∑ j, |b j|) / |D| := by
    simp [cD, b, D, p13SecondBarycentricOneCondition, p13Condition,
      p13SecondBarycentricDenominator, p13InterpolationValue]
  have hcomp : p13SecondBarycentricComputed (run t) = N' / D' := by
    simpa [N', D', a, b] using p13_computed_eq_counter_quotient (run t)
  have hexact : p13SecondBarycentricExact problem = N / D := by rfl
  have hgNlin : gN ≤ A * u t + 2 * A ^ 2 * (u t) ^ 2 := by
    simpa [gN, A] using gamma_le_linear_quadratic hut (le_of_lt htA)
  have hgDlin : gD ≤ B * u t + 2 * B ^ 2 * (u t) ^ 2 := by
    simpa [gD, B] using gamma_le_linear_quadratic hut (le_of_lt htB)
  have hgNtwo : gN ≤ 2 * A * u t := by
    have hs : 2 * (A * u t) ^ 2 ≤ A * u t := by nlinarith [mul_nonneg hA hut]
    nlinarith [hgNlin]
  have hgDtwo : gD ≤ 2 * B * u t := by
    have hs : 2 * (B * u t) ^ 2 ≤ B * u t := by nlinarith [mul_nonneg hB hut]
    nlinarith [hgDlin]
  have hgN0 : 0 ≤ gN := by
    dsimp [gN, gamma]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hut) (by nlinarith)
  have hgD0 : 0 ≤ gD := by
    dsimp [gD, gamma]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hut) (by nlinarith)
  have heN0 : 0 ≤ eN := mul_nonneg hgN0 hcN
  have heD0 : 0 ≤ eD := mul_nonneg hgD0 hcD
  have heDhalf : eD < 1 / 2 := by
    have hm := mul_le_mul_of_nonneg_right hgDtwo hcD
    dsimp [eD]
    nlinarith
  have hNerr0 :
      |N' - N| ≤ gN * ∑ j, |a j| := by
    rw [hNsum]
    exact abs_sum_mul_sub_sum_le a (fun j => ((run t).numeratorCounter j).value) gN
      (fun j => ((run t).numeratorCounter j).gamma_le (run t).numeratorGammaValid)
  have hDerr0 :
      |D' - D| ≤ gD * ∑ j, |b j| := by
    rw [hDsum]
    exact abs_sum_mul_sub_sum_le b (fun j => ((run t).denominatorCounter j).value) gD
      (fun j => ((run t).denominatorCounter j).gamma_le (run t).denominatorGammaValid)
  have hNerr : |N' - N| / |N| ≤ eN := by
    apply (div_le_iff₀ (abs_pos.mpr hN)).2
    calc
      |N' - N| ≤ gN * ∑ j, |a j| := hNerr0
      _ = eN * |N| := by
        dsimp [eN]
        rw [hcN_eq]
        field_simp [hN]
  have hDerr : |D' - D| / |D| ≤ eD := by
    apply (div_le_iff₀ (abs_pos.mpr hD)).2
    calc
      |D' - D| ≤ gD * ∑ j, |b j| := hDerr0
      _ = eD * |D| := by
        dsimp [eD]
        rw [hcD_eq]
        field_simp [hD]
  have hsmall : |D' - D| / |D| < 1 := lt_of_le_of_lt hDerr (by linarith)
  have hx0 : 0 ≤ |N' - N| / |N| := div_nonneg (abs_nonneg _) (abs_nonneg _)
  have hy0 : 0 ≤ |D' - D| / |D| := div_nonneg (abs_nonneg _) (abs_nonneg _)
  have hmonotone :
      (|N' - N| / |N| + |D' - D| / |D|) /
          (1 - |D' - D| / |D|) ≤
        (eN + eD) / (1 - eD) := by
    have hyd : 0 < 1 - |D' - D| / |D| := by linarith [hsmall]
    have hed : 0 < 1 - eD := by linarith [heDhalf]
    rw [div_le_div_iff₀ hyd hed]
    have hp : 0 ≤
        (eN - |N' - N| / |N|) * (1 - |D' - D| / |D|) :=
      mul_nonneg (sub_nonneg.mpr hNerr) (le_of_lt hyd)
    have hq : 0 ≤
        (eD - |D' - D| / |D|) * (1 + |N' - N| / |N|) :=
      mul_nonneg (sub_nonneg.mpr hDerr) (by linarith)
    nlinarith
  have hlinear : eN + eD ≤ u t * C + Q * (u t) ^ 2 := by
    have hn := mul_le_mul_of_nonneg_right hgNlin hcN
    have hd := mul_le_mul_of_nonneg_right hgDlin hcD
    calc
      eN + eD = gN * cN + gD * cD := rfl
      _ ≤ (A * u t + 2 * A ^ 2 * (u t) ^ 2) * cN +
          (B * u t + 2 * B ^ 2 * (u t) ^ 2) * cD := add_le_add hn hd
      _ = u t * C + Q * (u t) ^ 2 := by dsimp [C, Q]; ring
  have heNtwo : eN ≤ 2 * A * cN * u t := by
    have hm := mul_le_mul_of_nonneg_right hgNtwo hcN
    calc
      eN = gN * cN := rfl
      _ ≤ (2 * A * u t) * cN := hm
      _ = 2 * A * cN * u t := by ring
  have heDtwo : eD ≤ 2 * B * cD * u t := by
    have hm := mul_le_mul_of_nonneg_right hgDtwo hcD
    calc
      eD = gD * cD := rfl
      _ ≤ (2 * B * u t) * cD := hm
      _ = 2 * B * cD * u t := by ring
  have hesumtwo : eN + eD ≤ 2 * C * u t := by
    calc
      eN + eD ≤ 2 * A * cN * u t + 2 * B * cD * u t :=
        add_le_add heNtwo heDtwo
      _ = 2 * C * u t := by dsimp [C]; ring
  have hcorr :
      (eN + eD) * eD / (1 - eD) ≤ 8 * C * B * cD * (u t) ^ 2 := by
    have hden : 1 / 2 ≤ 1 - eD := by linarith [heDhalf]
    have hprod : (eN + eD) * eD ≤
        (2 * C * u t) * (2 * B * cD * u t) :=
      mul_le_mul hesumtwo heDtwo heD0 (by positivity)
    rw [div_le_iff₀ (by linarith [heDhalf])]
    calc
      (eN + eD) * eD ≤ (2 * C * u t) * (2 * B * cD * u t) := hprod
      _ = 4 * C * B * cD * (u t) ^ 2 := by ring
      _ ≤ 8 * C * B * cD * (u t) ^ 2 * (1 - eD) := by
        have hm := mul_le_mul_of_nonneg_left hden
          (by positivity : 0 ≤ 8 * C * B * cD * (u t) ^ 2)
        nlinarith
  have hformula :
      (eN + eD) / (1 - eD) =
        (eN + eD) + (eN + eD) * eD / (1 - eD) := by
    have hne : 1 - eD ≠ 0 := ne_of_gt (by linarith [heDhalf])
    field_simp [hne]
    ring
  rw [p13SecondBarycentricRelativeError, hexact, hcomp]
  calc
    |N / D - N' / D'| / |N / D| ≤
        (|N' - N| / |N| + |D' - D| / |D|) /
          (1 - |D' - D| / |D|) := relative_quotient_le N D N' D' hN hD hsmall
    _ ≤ (eN + eD) / (1 - eD) := hmonotone
    _ = (eN + eD) + (eN + eD) * eD / (1 - eD) := hformula
    _ ≤ u t * C + K * (u t) ^ 2 := by
      calc
        (eN + eD) + (eN + eD) * eD / (1 - eD) ≤
            (u t * C + Q * (u t) ^ 2) +
              8 * C * B * cD * (u t) ^ 2 := add_le_add hlinear hcorr
        _ = u t * C + K * (u t) ^ 2 := by dsimp [K]; ring
    _ = u t * p13SecondBarycentricFirstOrderCoefficient n cN cD +
          |K * (u t) ^ 2| := by
      rw [abs_of_nonneg (mul_nonneg hK (sq_nonneg (u t)))]
      simp only [p13SecondBarycentricFirstOrderCoefficient]
      dsimp [C, A, B]

end HighamBench
