import HighamBench.P13Definitions

namespace HighamBench

open scoped BigOperators

private lemma p13_gamma_nonneg {u : ℝ} {k : ℕ}
    (hu : 0 ≤ u) (hk : GammaValid u k) : 0 ≤ gamma u k := by
  rw [gamma]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu)
    (sub_nonneg.mpr (le_of_lt hk))

private lemma p13_weighted_sum_error_le {m : ℕ}
    (a v : Fin m → ℝ) (e : ℝ)
    (hv : ∀ j, |v j - 1| ≤ e) :
    |(∑ j, a j * v j) - ∑ j, a j| ≤ e * ∑ j, |a j| := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ j, (a j * v j - a j)| ≤ ∑ j, |a j * v j - a j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |a j| * |v j - 1| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ ∑ j, |a j| * e := by
      exact Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)
    _ = e * ∑ j, |a j| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

private lemma p13_weighted_sum_normalized_error_le {m : ℕ}
    (a v : Fin m → ℝ) (e : ℝ) (hsum : ∑ j, a j ≠ 0)
    (hv : ∀ j, |v j - 1| ≤ e) :
    |((∑ j, a j * v j) - ∑ j, a j) / (∑ j, a j)| ≤
      e * ((∑ j, |a j|) / |∑ j, a j|) := by
  rw [abs_div]
  have habs : 0 < |∑ j, a j| := abs_pos.mpr hsum
  calc
    |(∑ j, a j * v j) - ∑ j, a j| / |∑ j, a j| ≤
        (e * ∑ j, |a j|) / |∑ j, a j| :=
      (div_le_div_iff_of_pos_right habs).2
        (p13_weighted_sum_error_le a v e hv)
    _ = e * ((∑ j, |a j|) / |∑ j, a j|) := by ring

private lemma p13_gamma_tendsto_zero
    {iota : Type*} {l : Filter iota} (u : iota → ℝ)
    (hu : Filter.Tendsto u l (nhds 0)) (k : ℕ) :
    Filter.Tendsto (fun t ↦ gamma (u t) k) l (nhds 0) := by
  have hden : Filter.Tendsto
      (fun t ↦ 1 - (k : ℝ) * u t) l (nhds 1) := by
    convert tendsto_const_nhds.sub (hu.const_mul (k : ℝ)) using 1 <;> ring
  unfold gamma
  convert (hu.const_mul (k : ℝ)).div hden one_ne_zero using 1 <;> ring

private lemma p13_normalized_quotient_bound (alpha beta : ℝ)
    (hbeta : |beta| < 1) :
    |1 - (1 + alpha) / (1 + beta)| ≤
      (|alpha| + |beta|) / (1 - |beta|) := by
  have hdenpos : 0 < 1 - |beta| := sub_pos.mpr hbeta
  have honebeta : 1 + beta ≠ 0 := by
    intro h
    have : beta = -1 := by linarith
    subst beta
    norm_num at hbeta
  rw [one_sub_div honebeta, abs_div]
  have hnum : |(1 + beta) - (1 + alpha)| ≤ |alpha| + |beta| := by
    calc
      |(1 + beta) - (1 + alpha)| = |beta - alpha| := by ring_nf
      _ ≤ |beta| + |alpha| := abs_sub _ _
      _ = |alpha| + |beta| := add_comm _ _
  have hden : 1 - |beta| ≤ |1 + beta| := by
    have h := abs_sub (1 + beta) beta
    norm_num at h
    linarith
  exact div_le_div₀ (add_nonneg (abs_nonneg _) (abs_nonneg _))
    hnum hdenpos hden

private lemma p13_quotient_relative_error_le
    (A B A' B' a b : ℝ) (hA : A ≠ 0) (hB : B ≠ 0)
    (halpha : |(A' - A) / A| ≤ a)
    (hbeta : |(B' - B) / B| ≤ b) (hb : b < 1) :
    |A / B - A' / B'| / |A / B| ≤ (a + b) / (1 - b) := by
  let alpha := (A' - A) / A
  let beta := (B' - B) / B
  have hbeta' : |beta| < 1 := lt_of_le_of_lt hbeta hb
  have hB' : B' ≠ 0 := by
    intro hzero
    have hbeq : beta = -1 := by
      dsimp [beta]
      rw [hzero, zero_sub, neg_div]
      simp [hB]
    rw [hbeq] at hbeta'
    norm_num at hbeta'
  have hAB : A / B ≠ 0 := div_ne_zero hA hB
  have hnormalize :
      |A / B - A' / B'| / |A / B| =
        |1 - (1 + alpha) / (1 + beta)| := by
    rw [← abs_div]
    calc
      |(A / B - A' / B') / (A / B)| =
          |1 - (A' / B') / (A / B)| := by rw [one_sub_div hAB]
      _ = |1 - (1 + alpha) / (1 + beta)| := by
        congr 2
        dsimp [alpha, beta]
        field_simp [hA, hB, hB']
        <;> ring
  rw [hnormalize]
  calc
    |1 - (1 + alpha) / (1 + beta)| ≤
        (|alpha| + |beta|) / (1 - |beta|) :=
      p13_normalized_quotient_bound alpha beta hbeta'
    _ ≤ (a + b) / (1 - b) := by
      have ha0 : 0 ≤ a := le_trans (abs_nonneg _) halpha
      have hb0 : 0 ≤ b := le_trans (abs_nonneg _) hbeta
      apply div_le_div₀
      · exact add_nonneg ha0 hb0
      · exact add_le_add halpha hbeta
      · exact sub_pos.mpr hb
      · exact sub_le_sub_left hbeta 1

private lemma p13_gamma_quotient_remainder_isBigO
    {k q : ℕ} {iota : Type*} {l : Filter iota}
    (u : iota → ℝ) (hu : Filter.Tendsto u l (nhds 0)) (c d : ℝ) :
    (fun t ↦
      (gamma (u t) k * c + gamma (u t) q * d) /
          (1 - gamma (u t) q * d) -
        u t * ((k : ℝ) * c + (q : ℝ) * d)) =O[l]
      (fun t ↦ (u t) ^ 2) := by
  let K : ℝ := k
  let Q : ℝ := q
  let C : ℝ := K * c + Q * d
  let H : iota → ℝ := fun t ↦
    (K * K * c * (1 - Q * u t) / (1 - K * u t) +
        Q * Q * d + C * Q * d) /
      (1 - Q * u t - Q * u t * d)
  have hKden : Filter.Tendsto (fun t ↦ 1 - K * u t) l (nhds 1) := by
    convert tendsto_const_nhds.sub (hu.const_mul K) using 1 <;> ring
  have hQden : Filter.Tendsto (fun t ↦ 1 - Q * u t) l (nhds 1) := by
    convert tendsto_const_nhds.sub (hu.const_mul Q) using 1 <;> ring
  have hlast :
      Filter.Tendsto (fun t ↦ 1 - Q * u t - Q * u t * d) l (nhds 1) := by
    convert (tendsto_const_nhds.sub (hu.const_mul Q)).sub
      ((hu.const_mul Q).mul_const d) using 1 <;> ring
  have hterm :
      Filter.Tendsto
        (fun t ↦ K * K * c * (1 - Q * u t) / (1 - K * u t)) l
        (nhds (K * K * c)) := by
    have hnum : Filter.Tendsto
        (fun t ↦ K * K * c * (1 - Q * u t)) l (nhds (K * K * c)) := by
      convert hQden.const_mul (K * K * c) using 1 <;> ring
    convert hnum.div hKden one_ne_zero using 1 <;> norm_num
  have hH : Filter.Tendsto H l
      (nhds (K * K * c + Q * Q * d + C * Q * d)) := by
    dsimp [H]
    convert
      ((hterm.add tendsto_const_nhds).add tendsto_const_nhds).div
        hlast one_ne_zero using 1 <;> norm_num
  have hKne : ∀ᶠ t in l, 1 - K * u t ≠ 0 :=
    hKden.eventually_ne one_ne_zero
  have hQne : ∀ᶠ t in l, 1 - Q * u t ≠ 0 :=
    hQden.eventually_ne one_ne_zero
  have hlastne :
      ∀ᶠ t in l, 1 - Q * u t - Q * u t * d ≠ 0 :=
    hlast.eventually_ne one_ne_zero
  have heq :
      (fun t ↦
        (gamma (u t) k * c + gamma (u t) q * d) /
            (1 - gamma (u t) q * d) -
          u t * ((k : ℝ) * c + (q : ℝ) * d)) =ᶠ[l]
        (fun t ↦ (u t) ^ 2 * H t) := by
    filter_upwards [hKne, hQne, hlastne] with t hKt hQt hLt
    dsimp [H, C, K, Q] at hKt hQt hLt ⊢
    have hKt' : 1 - u t * (k : ℝ) ≠ 0 := by
      convert hKt using 1 <;> ring
    have hQt' : 1 - u t * (q : ℝ) ≠ 0 := by
      convert hQt using 1 <;> ring
    have hLt' :
        1 - u t * (q : ℝ) - u t * (q : ℝ) * d ≠ 0 := by
      convert hLt using 1 <;> ring
    rw [gamma, gamma]
    have houter :
        1 - ((q : ℝ) * u t / (1 - (q : ℝ) * u t)) * d =
          (1 - (q : ℝ) * u t - (q : ℝ) * u t * d) /
            (1 - (q : ℝ) * u t) := by
      field_simp [hQt]
    rw [houter]
    field_simp [hKt, hQt, hLt, hKt', hQt', hLt']
    ring
  have hmul :=
    (Asymptotics.isBigO_refl (fun t ↦ (u t) ^ 2) l).mul
      (hH.isBigO_one ℝ)
  apply hmul.congr' heq.symm
  filter_upwards with t
  simp

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
  let coeff : Fin (n + 1) → ℝ :=
    p13DirectBarycentricCoefficient problem.nodes problem.x
  let N : ℝ := ∑ j, coeff j * problem.data j
  let D : ℝ := ∑ j, coeff j
  let Nhat : ι → ℝ := fun t ↦
    ∑ j, (coeff j * problem.data j) * ((run t).numeratorCounter j).value
  let Dhat : ι → ℝ := fun t ↦
    ∑ j, coeff j * ((run t).denominatorCounter j).value
  let cData : ℝ := p13SecondBarycentricDataCondition problem
  let cOne : ℝ := p13SecondBarycentricOneCondition problem
  let kN : ℕ := p13NumeratorCounterLength n
  let kD : ℕ := p13DenominatorCounterLength n
  let remainder : ι → ℝ := fun t ↦
    (gamma (u t) kN * cData + gamma (u t) kD * cOne) /
        (1 - gamma (u t) kD * cOne) -
      u t * ((kN : ℝ) * cData + (kD : ℝ) * cOne)
  refine ⟨remainder, ?_, ?_⟩
  · simpa [remainder, kN, kD, cData, cOne] using
      (p13_gamma_quotient_remainder_isBigO u hu
        (p13SecondBarycentricDataCondition problem)
        (p13SecondBarycentricOneCondition problem)
        (k := p13NumeratorCounterLength n)
        (q := p13DenominatorCounterLength n))
  · have hbzero : Filter.Tendsto
        (fun t ↦ gamma (u t) kD * cOne) l (nhds 0) := by
      convert (p13_gamma_tendsto_zero u hu kD).mul_const cOne using 1 <;> ring
    have hblt : ∀ᶠ t in l, gamma (u t) kD * cOne < 1 :=
      (tendsto_order.mp hbzero).2 1 zero_lt_one
    filter_upwards [hblt] with t hbt
    have hN_eq : p13SecondBarycentricNumerator problem = N := by
      simp [N, coeff, p13SecondBarycentricNumerator,
        p13InterpolationValue]
    have hD_eq : p13SecondBarycentricDenominator problem = D := by
      simp [D, coeff, p13SecondBarycentricDenominator,
        p13InterpolationValue]
    have hN : N ≠ 0 := by
      rw [← hN_eq]
      exact hnumerator
    have hD : D ≠ 0 := by
      rw [← hD_eq]
      exact hdenominator
    have hNerr :
        |(Nhat t - N) / N| ≤ gamma (u t) kN * cData := by
      have hweighted := p13_weighted_sum_normalized_error_le
        (fun j ↦ coeff j * problem.data j)
        (fun j ↦ ((run t).numeratorCounter j).value)
        (gamma (u t) kN) hN
        (fun j ↦ ((run t).numeratorCounter j).gamma_le
          (run t).numeratorGammaValid)
      simpa [Nhat, N, cData, kN,
        p13SecondBarycentricDataCondition, p13Condition,
        p13SecondBarycentricNumerator, p13InterpolationValue, coeff] using hweighted
    have hDerr :
        |(Dhat t - D) / D| ≤ gamma (u t) kD * cOne := by
      have hweighted := p13_weighted_sum_normalized_error_le
        coeff
        (fun j ↦ ((run t).denominatorCounter j).value)
        (gamma (u t) kD) hD
        (fun j ↦ ((run t).denominatorCounter j).gamma_le
          (run t).denominatorGammaValid)
      simpa [Dhat, D, cOne, kD,
        p13SecondBarycentricOneCondition, p13Condition,
        p13SecondBarycentricDenominator, p13InterpolationValue, coeff] using hweighted
    have hcomputed :
        p13SecondBarycentricComputed (run t) = Nhat t / Dhat t := by
      rw [p13SecondBarycentricComputed, div_mul_eq_mul_div]
      congr 1
      · rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [(run t).numeratorCounter_eq j]
        ring
      · apply Finset.sum_congr rfl
        intro j _
        rw [(run t).denominatorCounter_eq j]
        ring
    have hquotient := p13_quotient_relative_error_le
      N D (Nhat t) (Dhat t)
      (gamma (u t) kN * cData) (gamma (u t) kD * cOne)
      hN hD hNerr hDerr hbt
    rw [p13SecondBarycentricRelativeError,
      p13SecondBarycentricExact, hcomputed, hN_eq, hD_eq]
    change |N / D - Nhat t / Dhat t| / |N / D| ≤ _
    calc
      |N / D - Nhat t / Dhat t| / |N / D| ≤
          (gamma (u t) kN * cData + gamma (u t) kD * cOne) /
            (1 - gamma (u t) kD * cOne) := hquotient
      _ = u t * p13SecondBarycentricFirstOrderCoefficient n
            (p13SecondBarycentricDataCondition problem)
            (p13SecondBarycentricOneCondition problem) + remainder t := by
          simp only [remainder, cData, cOne, kN, kD,
            p13SecondBarycentricFirstOrderCoefficient]
          ring
      _ ≤ u t * p13SecondBarycentricFirstOrderCoefficient n
            (p13SecondBarycentricDataCondition problem)
            (p13SecondBarycentricOneCondition problem) + |remainder t| := by
          exact add_le_add (le_refl _) (le_abs_self (remainder t))

end HighamBench
