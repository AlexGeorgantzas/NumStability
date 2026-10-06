import HighamBench.P13Definitions

namespace HighamBench

open scoped BigOperators

private lemma p13_gamma_nonneg {v : ℝ} {k : ℕ}
    (hv : 0 ≤ v) (hvalid : GammaValid v k) : 0 ≤ gamma v k := by
  rw [gamma]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hv)
    (le_of_lt (sub_pos.mpr hvalid))

private lemma p13_abs_sum_mul_sub_one_le {m : ℕ}
    (a e : Fin m → ℝ) {g : ℝ} (hg : 0 ≤ g)
    (he : ∀ j, |e j - 1| ≤ g) :
    |(∑ j, a j * e j) - ∑ j, a j| ≤ g * ∑ j, |a j| := by
  calc
    |(∑ j, a j * e j) - ∑ j, a j| = |∑ j, a j * (e j - 1)| := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ j, |a j * (e j - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |a j| * |e j - 1| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul]
    _ ≤ ∑ j, |a j| * g := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (he j) (abs_nonneg _)
    _ = g * ∑ j, |a j| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

private lemma p13_relative_div_error_le
    {N D N' D' a b : ℝ}
    (hN : N ≠ 0) (hD : D ≠ 0) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hN' : |N' - N| ≤ a * |N|)
    (hD' : |D' - D| ≤ b * |D|) (hb1 : b < 1) :
    |N / D - N' / D'| / |N / D| ≤ (a + b) / (1 - b) := by
  have habsN : 0 < |N| := abs_pos.mpr hN
  have habsD : 0 < |D| := abs_pos.mpr hD
  have hD'0 : D' ≠ 0 := by
    intro hzero
    have hEq : |D' - D| = |D| := by
      rw [hzero, zero_sub]
      exact abs_neg D
    rw [hEq] at hD'
    nlinarith
  have habsD' : 0 < |D'| := abs_pos.mpr hD'0
  have hDlower : (1 - b) * |D| ≤ |D'| := by
    have htri : |D| ≤ |D' - D| + |D'| := by
      calc
        |D| = |(D' - D) - D'| := by
          rw [show (D' - D) - D' = -D by ring, abs_neg]
        _ ≤ |D' - D| + |D'| := abs_sub _ _
    nlinarith
  have hnum : |N * D' - N' * D| ≤ (a + b) * |N| * |D| := by
    have hid : N * D' - N' * D = N * (D' - D) - (N' - N) * D := by ring
    rw [hid]
    calc
      |N * (D' - D) - (N' - N) * D| ≤
          |N * (D' - D)| + |(N' - N) * D| := abs_sub _ _
      _ = |N| * |D' - D| + |N' - N| * |D| := by rw [abs_mul, abs_mul]
      _ ≤ |N| * (b * |D|) + (a * |N|) * |D| := by
        gcongr
      _ = (a + b) * |N| * |D| := by ring
  have hdenpos : 0 < 1 - b := sub_pos.mpr hb1
  have herrEq : |N / D - N' / D'| / |N / D| =
      |N * D' - N' * D| / (|N| * |D'|) := by
    rw [div_sub_div N N' hD hD'0]
    simp only [abs_div, abs_mul]
    field_simp [hD, hD'0] <;> assumption
  rw [herrEq]
  apply (div_le_div_iff₀ (mul_pos habsN habsD') hdenpos).2
  calc
    |N * D' - N' * D| * (1 - b) ≤
        ((a + b) * |N| * |D|) * (1 - b) := by
      exact mul_le_mul_of_nonneg_right hnum hdenpos.le
    _ ≤ (a + b) * (|N| * |D'|) := by
      have hab : 0 ≤ a + b := add_nonneg ha hb
      calc
        ((a + b) * |N| * |D|) * (1 - b) =
            ((a + b) * |N|) * ((1 - b) * |D|) := by ring
        _ ≤ ((a + b) * |N|) * |D'| :=
          mul_le_mul_of_nonneg_left hDlower (mul_nonneg hab habsN.le)
        _ = (a + b) * (|N| * |D'|) := by ring

private lemma p13_gamma_quotient_expansion
    {v K L C E A : ℝ}
    (hA : A = K * C + L * E)
    (hK : 1 - K * v ≠ 0) (hL : 1 - L * v ≠ 0)
    (houter : 1 - (L * v / (1 - L * v)) * E ≠ 0)
    (hlast : 1 - L * (1 + E) * v ≠ 0) :
    (K * v / (1 - K * v) * C + L * v / (1 - L * v) * E) /
        (1 - (L * v / (1 - L * v)) * E) =
      v * A + v ^ 2 *
        ((A * (K + L * (1 + E)) - K * L * (C + E) -
            A * K * L * (1 + E) * v) /
          ((1 - K * v) * (1 - L * (1 + E) * v))) := by
  have hK' : 1 - v * K ≠ 0 := by
    convert hK using 1 <;> ring
  have hL' : 1 - v * L ≠ 0 := by
    convert hL using 1 <;> ring
  have houter' : 1 - v * L * E * (1 - v * L)⁻¹ ≠ 0 := by
    rw [show 1 - v * L * E * (1 - v * L)⁻¹ =
        1 - (L * v / (1 - L * v)) * E by
      field_simp [hL, hL']]
    exact houter
  rw [hA]
  field_simp [hK, hL, hK', hL', houter, houter']
  have hd₁ : 1 - v * L - v * L * E ≠ 0 := by
    convert hlast using 1 <;> ring
  have hd₂ : 1 - v * L * (1 + E) ≠ 0 := by
    convert hlast using 1 <;> ring
  field_simp [hd₁, hd₂]
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
  classical
  let c : Fin (n + 1) → ℝ :=
    p13DirectBarycentricCoefficient problem.nodes problem.x
  let N : ℝ := p13SecondBarycentricNumerator problem
  let D : ℝ := p13SecondBarycentricDenominator problem
  let C : ℝ := p13SecondBarycentricDataCondition problem
  let E : ℝ := p13SecondBarycentricOneCondition problem
  let K : ℝ := p13NumeratorCounterLength n
  let L : ℝ := p13DenominatorCounterLength n
  let A : ℝ := K * C + L * E
  let N' : ι → ℝ := fun t =>
    ∑ j, (c j * problem.data j) * ((run t).numeratorCounter j).value
  let D' : ι → ℝ := fun t =>
    ∑ j, c j * ((run t).denominatorCounter j).value
  let q : ι → ℝ := fun t =>
    (A * (K + L * (1 + E)) - K * L * (C + E) -
        A * K * L * (1 + E) * u t) /
      ((1 - K * u t) * (1 - L * (1 + E) * u t))
  let remainder : ι → ℝ := fun t => (u t) ^ 2 * q t

  have hN : N ≠ 0 := by
    simpa [N] using hnumerator
  have hD : D ≠ 0 := by
    simpa [D] using hdenominator
  have hC : 0 ≤ C := by
    dsimp [C, p13SecondBarycentricDataCondition, p13Condition]
    positivity
  have hE : 0 ≤ E := by
    dsimp [E, p13SecondBarycentricOneCondition, p13Condition]
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity

  have hq : Filter.Tendsto q l
      (nhds (A * (K + L * (1 + E)) - K * L * (C + E))) := by
    have hnq : Filter.Tendsto
        (fun t => A * (K + L * (1 + E)) - K * L * (C + E) -
          A * K * L * (1 + E) * u t) l
        (nhds (A * (K + L * (1 + E)) - K * L * (C + E))) := by
      convert tendsto_const_nhds.sub (tendsto_const_nhds.mul hu) using 1 <;> ring
    have hdq₁ : Filter.Tendsto (fun t => 1 - K * u t) l (nhds 1) := by
      convert tendsto_const_nhds.sub (tendsto_const_nhds.mul hu) using 1 <;> ring
    have hdq₂ : Filter.Tendsto (fun t => 1 - L * (1 + E) * u t) l (nhds 1) := by
      convert tendsto_const_nhds.sub (tendsto_const_nhds.mul hu) using 1 <;> ring
    dsimp [q]
    simpa only [one_mul, div_one] using
      hnq.div (hdq₁.mul hdq₂) (mul_ne_zero one_ne_zero one_ne_zero)
  have hremainder : remainder =O[l] (fun t => (u t) ^ 2) := by
    have hqO : q =O[l] (fun _ : ι => (1 : ℝ)) := hq.isBigO_one ℝ
    have hp := (Asymptotics.isBigO_refl (fun t => (u t) ^ 2) l).mul hqO
    simpa [remainder] using hp

  have hCmul : C * |N| = ∑ j, |c j * problem.data j| := by
    have habsN : |N| ≠ 0 := abs_ne_zero.mpr hN
    change ((∑ j, |c j * problem.data j|) / |N|) * |N| = _
    exact div_mul_cancel₀ _ habsN
  have hEmul : E * |D| = ∑ j, |c j| := by
    have habsD : |D| ≠ 0 := abs_ne_zero.mpr hD
    change ((∑ j, |c j * 1|) / |D|) * |D| = _
    simpa using div_mul_cancel₀ (∑ j, |c j|) habsD

  have hcomputed : ∀ t, p13SecondBarycentricComputed (run t) = N' t / D' t := by
    intro t
    have hnum : N' t =
        (∑ j, c j * ((run t).weightCounter j).value * problem.data j *
          ((run t).numeratorEvaluationCounter j).value) *
            (run t).quotientCounter.value := by
      dsimp [N']
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [(run t).numeratorCounter_eq j]
      ring
    have hden : D' t =
        ∑ j, c j * ((run t).weightCounter j).value *
          ((run t).denominatorEvaluationCounter j).value := by
      dsimp [D']
      apply Finset.sum_congr rfl
      intro j _
      rw [(run t).denominatorCounter_eq j]
      ring
    rw [p13SecondBarycentricComputed]
    change
      ((∑ j, c j * ((run t).weightCounter j).value * problem.data j *
          ((run t).numeratorEvaluationCounter j).value) /
        (∑ j, c j * ((run t).weightCounter j).value *
          ((run t).denominatorEvaluationCounter j).value)) *
          (run t).quotientCounter.value = N' t / D' t
    rw [hnum, hden]
    ring

  have hgamma : Filter.Tendsto
      (fun t => gamma (u t) (p13DenominatorCounterLength n) * E) l (nhds 0) := by
    have hnumg : Filter.Tendsto
        (fun t => (p13DenominatorCounterLength n : ℝ) * u t) l (nhds 0) := by
      convert tendsto_const_nhds.mul hu using 1 <;> ring
    have hdeng : Filter.Tendsto
        (fun t => 1 - (p13DenominatorCounterLength n : ℝ) * u t) l (nhds 1) := by
      convert tendsto_const_nhds.sub hnumg using 1 <;> ring
    have hg0 : Filter.Tendsto
        (fun t => gamma (u t) (p13DenominatorCounterLength n)) l (nhds 0) := by
      dsimp [gamma]
      convert hnumg.div hdeng one_ne_zero using 1 <;> ring
    convert hg0.mul tendsto_const_nhds using 1 <;> ring
  have hb_event : ∀ᶠ t in l,
      gamma (u t) (p13DenominatorCounterLength n) * E < 1 :=
    (tendsto_order.1 hgamma).2 1 zero_lt_one

  refine ⟨remainder, hremainder, ?_⟩
  filter_upwards [hb_event] with t hb1
  have hu0 : 0 ≤ u t := (run t).u_nonneg
  have hgN0 : 0 ≤ gamma (u t) (p13NumeratorCounterLength n) :=
    p13_gamma_nonneg hu0 (run t).numeratorGammaValid
  have hgD0 : 0 ≤ gamma (u t) (p13DenominatorCounterLength n) :=
    p13_gamma_nonneg hu0 (run t).denominatorGammaValid
  have ha0 : 0 ≤ gamma (u t) (p13NumeratorCounterLength n) * C :=
    mul_nonneg hgN0 hC
  have hb0 : 0 ≤ gamma (u t) (p13DenominatorCounterLength n) * E :=
    mul_nonneg hgD0 hE
  have hNpert : |N' t - N| ≤
      (gamma (u t) (p13NumeratorCounterLength n) * C) * |N| := by
    have hraw := p13_abs_sum_mul_sub_one_le
      (fun j => c j * problem.data j)
      (fun j => ((run t).numeratorCounter j).value) hgN0
      (fun j => ((run t).numeratorCounter j).gamma_le
        (run t).numeratorGammaValid)
    change |N' t - N| ≤ _
    calc
      |N' t - N| ≤ gamma (u t) (p13NumeratorCounterLength n) *
          ∑ j, |c j * problem.data j| := by
        simpa [N', N, p13SecondBarycentricNumerator,
          p13InterpolationValue, c] using hraw
      _ = (gamma (u t) (p13NumeratorCounterLength n) * C) * |N| := by
        rw [← hCmul]
        ring
  have hDpert : |D' t - D| ≤
      (gamma (u t) (p13DenominatorCounterLength n) * E) * |D| := by
    have hraw := p13_abs_sum_mul_sub_one_le c
      (fun j => ((run t).denominatorCounter j).value) hgD0
      (fun j => ((run t).denominatorCounter j).gamma_le
        (run t).denominatorGammaValid)
    change |D' t - D| ≤ _
    calc
      |D' t - D| ≤ gamma (u t) (p13DenominatorCounterLength n) *
          ∑ j, |c j| := by
        simpa [D', D, p13SecondBarycentricDenominator,
          p13InterpolationValue, c] using hraw
      _ = (gamma (u t) (p13DenominatorCounterLength n) * E) * |D| := by
        rw [← hEmul]
        ring
  have hratio := p13_relative_div_error_le hN hD ha0 hb0 hNpert hDpert hb1
  rw [p13SecondBarycentricRelativeError, hcomputed t]
  change |N / D - N' t / D' t| / |N / D| ≤ _
  calc
    |N / D - N' t / D' t| / |N / D| ≤
        (gamma (u t) (p13NumeratorCounterLength n) * C +
          gamma (u t) (p13DenominatorCounterLength n) * E) /
          (1 - gamma (u t) (p13DenominatorCounterLength n) * E) := hratio
    _ = u t * A + remainder t := by
      have hkpos : 0 < 1 - (p13NumeratorCounterLength n : ℝ) * u t :=
        sub_pos.mpr (run t).numeratorGammaValid
      have hlpos : 0 < 1 - (p13DenominatorCounterLength n : ℝ) * u t :=
        sub_pos.mpr (run t).denominatorGammaValid
      have hlast : 0 <
          1 - (p13DenominatorCounterLength n : ℝ) * (1 + E) * u t := by
        dsimp [gamma] at hb1
        have hx :
            ((p13DenominatorCounterLength n : ℝ) * u t * E) /
                (1 - (p13DenominatorCounterLength n : ℝ) * u t) < 1 := by
          convert hb1 using 1 <;> ring
        have hx' := (div_lt_one hlpos).mp hx
        calc
          0 < (1 - (p13DenominatorCounterLength n : ℝ) * u t) -
              (p13DenominatorCounterLength n : ℝ) * u t * E := sub_pos.mpr hx'
          _ = 1 - (p13DenominatorCounterLength n : ℝ) * (1 + E) * u t := by ring
      have houter : 0 <
          1 - ((p13DenominatorCounterLength n : ℝ) * u t /
            (1 - (p13DenominatorCounterLength n : ℝ) * u t)) * E := by
        simpa only [gamma] using sub_pos.mpr hb1
      change
        (K * u t / (1 - K * u t) * C +
            L * u t / (1 - L * u t) * E) /
            (1 - (L * u t / (1 - L * u t)) * E) =
          u t * A + (u t) ^ 2 *
            ((A * (K + L * (1 + E)) - K * L * (C + E) -
                A * K * L * (1 + E) * u t) /
              ((1 - K * u t) * (1 - L * (1 + E) * u t)))
      exact p13_gamma_quotient_expansion rfl (ne_of_gt hkpos) (ne_of_gt hlpos)
        (ne_of_gt houter) (ne_of_gt hlast)
    _ ≤ u t * p13SecondBarycentricFirstOrderCoefficient n C E +
          |remainder t| := by
      have hrle : remainder t ≤ |remainder t| := le_abs_self _
      simpa [A, K, L, p13SecondBarycentricFirstOrderCoefficient] using
        add_le_add_left hrle (u t * A)

end HighamBench
