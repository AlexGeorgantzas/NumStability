import NumStability.Source.Higham.Chapter01.Section17.HornerEvaluation

namespace NumStability

/-!
# Nonrandom rounding on the source interval

Finite-normal range certificates and an error-evaluation identity for Kahan's
Horner rational function on the source interval used in Higham Section 1.17.
The main result is
`ieeeDoubleKahanRationalFunction_eq_errorEval_on_source_interval`.
-/

private theorem kahanIeeeDoubleUnitRoundoff_lt_one_thousandth :
    kahanIeeeDoubleUnitRoundoff < (1 : ℝ) / 1000 := by
  rw [kahanIeeeDoubleUnitRoundoff,
    FloatingPointFormat.ieeeDoubleFormat_unitRoundoff]
  norm_num [zpow_neg]

private theorem kahanIeeeDouble_delta_bounds
    {δ : ℝ} (hδ : |δ| < kahanIeeeDoubleUnitRoundoff) :
    (999 : ℝ) / 1000 < 1 + δ ∧
      1 + δ < (1001 : ℝ) / 1000 := by
  have hδu := abs_lt.mp hδ
  have hu := kahanIeeeDoubleUnitRoundoff_lt_one_thousandth
  constructor <;> nlinarith

/-- IEEE double represents every real with magnitude between one and one thousand
as a finite-normal value. This bound is shared with the stored-grid certificate. -/
theorem ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    {z : ℝ} (hzlo : (1 : ℝ) ≤ |z|) (hzhi : |z| ≤ 1000) :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange z := by
  constructor
  · have hmin : FloatingPointFormat.ieeeDoubleFormat.minNormalMagnitude ≤
        (1 : ℝ) := by
      norm_num [FloatingPointFormat.minNormalMagnitude,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
      exact inv_le_one_of_one_le₀
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    exact le_trans hmin hzlo
  · have hmax : (1000 : ℝ) ≤
        FloatingPointFormat.ieeeDoubleFormat.maxFiniteMagnitude := by
      norm_num [FloatingPointFormat.maxFiniteMagnitude,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
      have hpow : (2000 : ℝ) ≤ 2 ^ 1024 := by
        have h11 : (2000 : ℝ) ≤ 2 ^ 11 := by norm_num
        have hmono : (2 : ℝ) ^ 11 ≤ 2 ^ 1024 :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num)
        exact le_trans h11 hmono
      have hfrac :
          (1 : ℝ) / 2 ≤
            (9007199254740991 : ℝ) / 9007199254740992 := by
        norm_num
      have hprod :
          (2000 : ℝ) * ((1 : ℝ) / 2) ≤
            2 ^ 1024 *
              ((9007199254740991 : ℝ) / 9007199254740992) :=
        mul_le_mul hpow hfrac (by norm_num) (by positivity)
      norm_num at hprod
      exact hprod
    exact le_trans hzhi hmax

private theorem ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    {z : ℝ} (hzlo : (1 : ℝ) ≤ z) (hzhi : z ≤ 1000) :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange z := by
  apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
  · rwa [abs_of_nonneg (le_trans zero_le_one hzlo)]
  · rwa [abs_of_nonneg (le_trans zero_le_one hzlo)]

private theorem mul_interval_mono
    {a b la ua lb ub : ℝ} (hla : la ≤ a) (hua : a ≤ ua)
    (hlb : lb ≤ b) (hub : b ≤ ub) (hla0 : 0 ≤ la) (hlb0 : 0 ≤ lb) :
    la * lb ≤ a * b ∧ a * b ≤ ua * ub := by
  constructor
  · exact mul_le_mul hla hlb hlb0 (le_trans hla0 hla)
  · exact mul_le_mul hua hub (le_trans hlb0 hlb)
      (le_trans hla0 (le_trans hla hua))

private theorem kahan_source_interval_x_bounds
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    (803 : ℝ) / 500 ≤ x ∧ x ≤ (1607 : ℝ) / 1000 := by
  refine ⟨hxlo, ?_⟩
  have htail :
      (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52 ≤
        (1607 : ℝ) / 1000 := by
    norm_num
  exact le_trans hxhi htail

private theorem kahan_source_interval_ieeeDouble_finiteNormalRange
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange x := by
  have hxb := kahan_source_interval_x_bounds hxlo hxhi
  apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
  · nlinarith
  · nlinarith

private theorem kahan_source_interval_numerator_m0_normal
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.mul 4 x) := by
  have hxb := kahan_source_interval_x_bounds hxlo hxhi
  apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
  · simp [BasicOp.exact]
    nlinarith
  · simp [BasicOp.exact]
    nlinarith

private theorem kahan_source_interval_denominator_s0_normal
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.sub 14 x) := by
  have hxb := kahan_source_interval_x_bounds hxlo hxhi
  apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
  · simp [BasicOp.exact]
    nlinarith
  · simp [BasicOp.exact]
    nlinarith

set_option maxHeartbeats 800000 in
theorem ieeeDoubleKahanNumeratorNormalTrace_of_source_interval
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    IeeeDoubleKahanNumeratorNormalTrace x := by
  have hxb := kahan_source_interval_x_bounds hxlo hxhi
  have hm0N := kahan_source_interval_numerator_m0_normal hxlo hxhi
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := 4) (y := x) hm0N with ⟨δm0, hδm0, hm0eq⟩
  have hδm0b := kahanIeeeDouble_delta_bounds hδm0
  have hm0eq' :
      ieeeDoubleKahanNumerator_m0 x = (4 * x) * (1 + δm0) := by
    simpa [ieeeDoubleKahanNumerator_m0, BasicOp.exact] using hm0eq
  have hm0_exact_lo : (6 : ℝ) ≤ 4 * x := by linarith [hxb.1]
  have hm0_exact_hi : 4 * x ≤ 7 := by linarith [hxb.2]
  have hm0_prod :=
    mul_interval_mono hm0_exact_lo hm0_exact_hi
      (le_of_lt hδm0b.1) (le_of_lt hδm0b.2)
      (by norm_num : (0 : ℝ) ≤ 6)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm0_lo : (5 : ℝ) ≤ ieeeDoubleKahanNumerator_m0 x := by
    rw [hm0eq']
    linarith [hm0_prod.1]
  have hm0_hi : ieeeDoubleKahanNumerator_m0 x ≤ (8 : ℝ) := by
    rw [hm0eq']
    linarith [hm0_prod.2]
  have hs0N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.sub 59 (ieeeDoubleKahanNumerator_m0 x)) := by
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm0_hi]
    · simp [BasicOp.exact]
      linarith [hm0_lo]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 59) (y := ieeeDoubleKahanNumerator_m0 x) hs0N with
    ⟨δs0, hδs0, hs0eq⟩
  have hδs0b := kahanIeeeDouble_delta_bounds hδs0
  have hs0eq' :
      ieeeDoubleKahanNumerator_s0 x =
        (59 - ieeeDoubleKahanNumerator_m0 x) * (1 + δs0) := by
    simpa [ieeeDoubleKahanNumerator_s0, BasicOp.exact] using hs0eq
  have hs0_exact_lo : (51 : ℝ) ≤ 59 - ieeeDoubleKahanNumerator_m0 x := by
    linarith [hm0_hi]
  have hs0_exact_hi : 59 - ieeeDoubleKahanNumerator_m0 x ≤ (54 : ℝ) := by
    linarith [hm0_lo]
  have hs0_prod :=
    mul_interval_mono hs0_exact_lo hs0_exact_hi
      (le_of_lt hδs0b.1) (le_of_lt hδs0b.2)
      (by norm_num : (0 : ℝ) ≤ 51)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs0_lo : (50 : ℝ) ≤ ieeeDoubleKahanNumerator_s0 x := by
    rw [hs0eq']
    linarith [hs0_prod.1]
  have hs0_hi : ieeeDoubleKahanNumerator_s0 x ≤ (55 : ℝ) := by
    rw [hs0eq']
    linarith [hs0_prod.2]
  have hm1N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanNumerator_s0 x)) := by
    have hm1_prod :=
      mul_interval_mono hxb.1 hxb.2 hs0_lo hs0_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ 50)
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm1_prod.1]
    · simp [BasicOp.exact]
      linarith [hm1_prod.2]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanNumerator_s0 x) hm1N with
    ⟨δm1, hδm1, hm1eq⟩
  have hδm1b := kahanIeeeDouble_delta_bounds hδm1
  have hm1eq' :
      ieeeDoubleKahanNumerator_m1 x =
        (x * ieeeDoubleKahanNumerator_s0 x) * (1 + δm1) := by
    simpa [ieeeDoubleKahanNumerator_m1, BasicOp.exact] using hm1eq
  have hm1_exact_lo : (80 : ℝ) ≤ x * ieeeDoubleKahanNumerator_s0 x := by
    have hm1_prod :=
      mul_interval_mono hxb.1 hxb.2 hs0_lo hs0_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ 50)
    linarith [hm1_prod.1]
  have hm1_exact_hi : x * ieeeDoubleKahanNumerator_s0 x ≤ (89 : ℝ) := by
    have hm1_prod :=
      mul_interval_mono hxb.1 hxb.2 hs0_lo hs0_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ 50)
    linarith [hm1_prod.2]
  have hm1_prod_round :=
    mul_interval_mono hm1_exact_lo hm1_exact_hi
      (le_of_lt hδm1b.1) (le_of_lt hδm1b.2)
      (by norm_num : (0 : ℝ) ≤ 80)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm1_lo : (79 : ℝ) ≤ ieeeDoubleKahanNumerator_m1 x := by
    rw [hm1eq']
    linarith [hm1_prod_round.1]
  have hm1_hi : ieeeDoubleKahanNumerator_m1 x ≤ (90 : ℝ) := by
    rw [hm1eq']
    linarith [hm1_prod_round.2]
  have hs1N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.sub 324 (ieeeDoubleKahanNumerator_m1 x)) := by
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm1_hi]
    · simp [BasicOp.exact]
      linarith [hm1_lo]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 324) (y := ieeeDoubleKahanNumerator_m1 x) hs1N with
    ⟨δs1, hδs1, hs1eq⟩
  have hδs1b := kahanIeeeDouble_delta_bounds hδs1
  have hs1eq' :
      ieeeDoubleKahanNumerator_s1 x =
        (324 - ieeeDoubleKahanNumerator_m1 x) * (1 + δs1) := by
    simpa [ieeeDoubleKahanNumerator_s1, BasicOp.exact] using hs1eq
  have hs1_exact_lo : (234 : ℝ) ≤ 324 - ieeeDoubleKahanNumerator_m1 x := by
    linarith [hm1_hi]
  have hs1_exact_hi : 324 - ieeeDoubleKahanNumerator_m1 x ≤ (245 : ℝ) := by
    linarith [hm1_lo]
  have hs1_prod_round :=
    mul_interval_mono hs1_exact_lo hs1_exact_hi
      (le_of_lt hδs1b.1) (le_of_lt hδs1b.2)
      (by norm_num : (0 : ℝ) ≤ 234)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs1_lo : (233 : ℝ) ≤ ieeeDoubleKahanNumerator_s1 x := by
    rw [hs1eq']
    linarith [hs1_prod_round.1]
  have hs1_hi : ieeeDoubleKahanNumerator_s1 x ≤ (246 : ℝ) := by
    rw [hs1eq']
    linarith [hs1_prod_round.2]
  have hm2N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanNumerator_s1 x)) := by
    have hm2_prod :=
      mul_interval_mono hxb.1 hxb.2 hs1_lo hs1_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ 233)
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm2_prod.1]
    · simp [BasicOp.exact]
      linarith [hm2_prod.2]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanNumerator_s1 x) hm2N with
    ⟨δm2, hδm2, hm2eq⟩
  have hδm2b := kahanIeeeDouble_delta_bounds hδm2
  have hm2eq' :
      ieeeDoubleKahanNumerator_m2 x =
        (x * ieeeDoubleKahanNumerator_s1 x) * (1 + δm2) := by
    simpa [ieeeDoubleKahanNumerator_m2, BasicOp.exact] using hm2eq
  have hm2_exact_lo : (374 : ℝ) ≤ x * ieeeDoubleKahanNumerator_s1 x := by
    have hm2_prod :=
      mul_interval_mono hxb.1 hxb.2 hs1_lo hs1_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ 233)
    linarith [hm2_prod.1]
  have hm2_exact_hi : x * ieeeDoubleKahanNumerator_s1 x ≤ (396 : ℝ) := by
    have hm2_prod :=
      mul_interval_mono hxb.1 hxb.2 hs1_lo hs1_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ 233)
    linarith [hm2_prod.2]
  have hm2_prod_round :=
    mul_interval_mono hm2_exact_lo hm2_exact_hi
      (le_of_lt hδm2b.1) (le_of_lt hδm2b.2)
      (by norm_num : (0 : ℝ) ≤ 374)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm2_lo : (373 : ℝ) ≤ ieeeDoubleKahanNumerator_m2 x := by
    rw [hm2eq']
    linarith [hm2_prod_round.1]
  have hm2_hi : ieeeDoubleKahanNumerator_m2 x ≤ (397 : ℝ) := by
    rw [hm2eq']
    linarith [hm2_prod_round.2]
  have hs2N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.sub 751 (ieeeDoubleKahanNumerator_m2 x)) := by
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm2_hi]
    · simp [BasicOp.exact]
      linarith [hm2_lo]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 751) (y := ieeeDoubleKahanNumerator_m2 x) hs2N with
    ⟨δs2, hδs2, hs2eq⟩
  have hδs2b := kahanIeeeDouble_delta_bounds hδs2
  have hs2eq' :
      ieeeDoubleKahanNumerator_s2 x =
        (751 - ieeeDoubleKahanNumerator_m2 x) * (1 + δs2) := by
    simpa [ieeeDoubleKahanNumerator_s2, BasicOp.exact] using hs2eq
  have hs2_exact_lo : (354 : ℝ) ≤ 751 - ieeeDoubleKahanNumerator_m2 x := by
    linarith [hm2_hi]
  have hs2_exact_hi : 751 - ieeeDoubleKahanNumerator_m2 x ≤ (378 : ℝ) := by
    linarith [hm2_lo]
  have hs2_prod_round :=
    mul_interval_mono hs2_exact_lo hs2_exact_hi
      (le_of_lt hδs2b.1) (le_of_lt hδs2b.2)
      (by norm_num : (0 : ℝ) ≤ 354)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs2_lo : (353 : ℝ) ≤ ieeeDoubleKahanNumerator_s2 x := by
    rw [hs2eq']
    linarith [hs2_prod_round.1]
  have hs2_hi : ieeeDoubleKahanNumerator_s2 x ≤ (379 : ℝ) := by
    rw [hs2eq']
    linarith [hs2_prod_round.2]
  have hm3N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanNumerator_s2 x)) := by
    have hm3_prod :=
      mul_interval_mono hxb.1 hxb.2 hs2_lo hs2_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ 353)
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm3_prod.1]
    · simp [BasicOp.exact]
      linarith [hm3_prod.2]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanNumerator_s2 x) hm3N with
    ⟨δm3, hδm3, hm3eq⟩
  have hδm3b := kahanIeeeDouble_delta_bounds hδm3
  have hm3eq' :
      ieeeDoubleKahanNumerator_m3 x =
        (x * ieeeDoubleKahanNumerator_s2 x) * (1 + δm3) := by
    simpa [ieeeDoubleKahanNumerator_m3, BasicOp.exact] using hm3eq
  have hm3_exact_lo : (566 : ℝ) ≤ x * ieeeDoubleKahanNumerator_s2 x := by
    have hm3_prod :=
      mul_interval_mono hxb.1 hxb.2 hs2_lo hs2_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ 353)
    linarith [hm3_prod.1]
  have hm3_exact_hi : x * ieeeDoubleKahanNumerator_s2 x ≤ (610 : ℝ) := by
    have hm3_prod :=
      mul_interval_mono hxb.1 hxb.2 hs2_lo hs2_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ 353)
    linarith [hm3_prod.2]
  have hm3_prod_round :=
    mul_interval_mono hm3_exact_lo hm3_exact_hi
      (le_of_lt hδm3b.1) (le_of_lt hδm3b.2)
      (by norm_num : (0 : ℝ) ≤ 566)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm3_lo : (565 : ℝ) ≤ ieeeDoubleKahanNumerator_m3 x := by
    rw [hm3eq']
    linarith [hm3_prod_round.1]
  have hm3_hi : ieeeDoubleKahanNumerator_m3 x ≤ (611 : ℝ) := by
    rw [hm3eq']
    linarith [hm3_prod_round.2]
  have hresultN : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.sub 622 (ieeeDoubleKahanNumerator_m3 x)) := by
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm3_hi]
    · simp [BasicOp.exact]
      linarith [hm3_lo]
  exact
    { m0 := hm0N
      s0 := hs0N
      m1 := hm1N
      s1 := hs1N
      m2 := hm2N
      s2 := hs2N
      m3 := hm3N
      result := hresultN }

set_option maxHeartbeats 800000 in
theorem ieeeDoubleKahanDenominatorNormalTrace_of_source_interval
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    IeeeDoubleKahanDenominatorNormalTrace x := by
  have hxb := kahan_source_interval_x_bounds hxlo hxhi
  have hs0N := kahan_source_interval_denominator_s0_normal hxlo hxhi
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 14) (y := x) hs0N with ⟨δs0, hδs0, hs0eq⟩
  have hδs0b := kahanIeeeDouble_delta_bounds hδs0
  have hs0eq' :
      ieeeDoubleKahanDenominator_s0 x = (14 - x) * (1 + δs0) := by
    simpa [ieeeDoubleKahanDenominator_s0, BasicOp.exact] using hs0eq
  have hs0_exact_lo : (1239 : ℝ) / 100 ≤ 14 - x := by linarith [hxb.2]
  have hs0_exact_hi : 14 - x ≤ (25 : ℝ) / 2 := by linarith [hxb.1]
  have hs0_prod_round :=
    mul_interval_mono hs0_exact_lo hs0_exact_hi
      (le_of_lt hδs0b.1) (le_of_lt hδs0b.2)
      (by norm_num : (0 : ℝ) ≤ (1239 : ℝ) / 100)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs0_lo : (123 : ℝ) / 10 ≤ ieeeDoubleKahanDenominator_s0 x := by
    rw [hs0eq']
    linarith [hs0_prod_round.1]
  have hs0_hi : ieeeDoubleKahanDenominator_s0 x ≤ (63 : ℝ) / 5 := by
    rw [hs0eq']
    linarith [hs0_prod_round.2]
  have hm1N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanDenominator_s0 x)) := by
    have hm1_prod :=
      mul_interval_mono hxb.1 hxb.2 hs0_lo hs0_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ (123 : ℝ) / 10)
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm1_prod.1]
    · simp [BasicOp.exact]
      linarith [hm1_prod.2]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanDenominator_s0 x) hm1N with
    ⟨δm1, hδm1, hm1eq⟩
  have hδm1b := kahanIeeeDouble_delta_bounds hδm1
  have hm1eq' :
      ieeeDoubleKahanDenominator_m1 x =
        (x * ieeeDoubleKahanDenominator_s0 x) * (1 + δm1) := by
    simpa [ieeeDoubleKahanDenominator_m1, BasicOp.exact] using hm1eq
  have hm1_exact_lo : (197 : ℝ) / 10 ≤ x * ieeeDoubleKahanDenominator_s0 x := by
    have hm1_prod :=
      mul_interval_mono hxb.1 hxb.2 hs0_lo hs0_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ (123 : ℝ) / 10)
    linarith [hm1_prod.1]
  have hm1_exact_hi : x * ieeeDoubleKahanDenominator_s0 x ≤ (102 : ℝ) / 5 := by
    have hm1_prod :=
      mul_interval_mono hxb.1 hxb.2 hs0_lo hs0_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ (123 : ℝ) / 10)
    linarith [hm1_prod.2]
  have hm1_prod_round :=
    mul_interval_mono hm1_exact_lo hm1_exact_hi
      (le_of_lt hδm1b.1) (le_of_lt hδm1b.2)
      (by norm_num : (0 : ℝ) ≤ (197 : ℝ) / 10)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm1_lo : (98 : ℝ) / 5 ≤ ieeeDoubleKahanDenominator_m1 x := by
    rw [hm1eq']
    linarith [hm1_prod_round.1]
  have hm1_hi : ieeeDoubleKahanDenominator_m1 x ≤ (103 : ℝ) / 5 := by
    rw [hm1eq']
    linarith [hm1_prod_round.2]
  have hs1N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.sub 72 (ieeeDoubleKahanDenominator_m1 x)) := by
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm1_hi]
    · simp [BasicOp.exact]
      linarith [hm1_lo]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 72) (y := ieeeDoubleKahanDenominator_m1 x) hs1N with
    ⟨δs1, hδs1, hs1eq⟩
  have hδs1b := kahanIeeeDouble_delta_bounds hδs1
  have hs1eq' :
      ieeeDoubleKahanDenominator_s1 x =
        (72 - ieeeDoubleKahanDenominator_m1 x) * (1 + δs1) := by
    simpa [ieeeDoubleKahanDenominator_s1, BasicOp.exact] using hs1eq
  have hs1_exact_lo : (257 : ℝ) / 5 ≤ 72 - ieeeDoubleKahanDenominator_m1 x := by
    linarith [hm1_hi]
  have hs1_exact_hi : 72 - ieeeDoubleKahanDenominator_m1 x ≤ (262 : ℝ) / 5 := by
    linarith [hm1_lo]
  have hs1_prod_round :=
    mul_interval_mono hs1_exact_lo hs1_exact_hi
      (le_of_lt hδs1b.1) (le_of_lt hδs1b.2)
      (by norm_num : (0 : ℝ) ≤ (257 : ℝ) / 5)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs1_lo : (513 : ℝ) / 10 ≤ ieeeDoubleKahanDenominator_s1 x := by
    rw [hs1eq']
    linarith [hs1_prod_round.1]
  have hs1_hi : ieeeDoubleKahanDenominator_s1 x ≤ (105 : ℝ) / 2 := by
    rw [hs1eq']
    linarith [hs1_prod_round.2]
  have hm2N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanDenominator_s1 x)) := by
    have hm2_prod :=
      mul_interval_mono hxb.1 hxb.2 hs1_lo hs1_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ (513 : ℝ) / 10)
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm2_prod.1]
    · simp [BasicOp.exact]
      linarith [hm2_prod.2]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanDenominator_s1 x) hm2N with
    ⟨δm2, hδm2, hm2eq⟩
  have hδm2b := kahanIeeeDouble_delta_bounds hδm2
  have hm2eq' :
      ieeeDoubleKahanDenominator_m2 x =
        (x * ieeeDoubleKahanDenominator_s1 x) * (1 + δm2) := by
    simpa [ieeeDoubleKahanDenominator_m2, BasicOp.exact] using hm2eq
  have hm2_exact_lo : (823 : ℝ) / 10 ≤ x * ieeeDoubleKahanDenominator_s1 x := by
    have hm2_prod :=
      mul_interval_mono hxb.1 hxb.2 hs1_lo hs1_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ (513 : ℝ) / 10)
    linarith [hm2_prod.1]
  have hm2_exact_hi : x * ieeeDoubleKahanDenominator_s1 x ≤ (422 : ℝ) / 5 := by
    have hm2_prod :=
      mul_interval_mono hxb.1 hxb.2 hs1_lo hs1_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ (513 : ℝ) / 10)
    linarith [hm2_prod.2]
  have hm2_prod_round :=
    mul_interval_mono hm2_exact_lo hm2_exact_hi
      (le_of_lt hδm2b.1) (le_of_lt hδm2b.2)
      (by norm_num : (0 : ℝ) ≤ (823 : ℝ) / 10)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm2_lo : (411 : ℝ) / 5 ≤ ieeeDoubleKahanDenominator_m2 x := by
    rw [hm2eq']
    linarith [hm2_prod_round.1]
  have hm2_hi : ieeeDoubleKahanDenominator_m2 x ≤ (169 : ℝ) / 2 := by
    rw [hm2eq']
    linarith [hm2_prod_round.2]
  have hs2N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.sub 151 (ieeeDoubleKahanDenominator_m2 x)) := by
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm2_hi]
    · simp [BasicOp.exact]
      linarith [hm2_lo]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 151) (y := ieeeDoubleKahanDenominator_m2 x) hs2N with
    ⟨δs2, hδs2, hs2eq⟩
  have hδs2b := kahanIeeeDouble_delta_bounds hδs2
  have hs2eq' :
      ieeeDoubleKahanDenominator_s2 x =
        (151 - ieeeDoubleKahanDenominator_m2 x) * (1 + δs2) := by
    simpa [ieeeDoubleKahanDenominator_s2, BasicOp.exact] using hs2eq
  have hs2_exact_lo : (133 : ℝ) / 2 ≤ 151 - ieeeDoubleKahanDenominator_m2 x := by
    linarith [hm2_hi]
  have hs2_exact_hi : 151 - ieeeDoubleKahanDenominator_m2 x ≤ (344 : ℝ) / 5 := by
    linarith [hm2_lo]
  have hs2_prod_round :=
    mul_interval_mono hs2_exact_lo hs2_exact_hi
      (le_of_lt hδs2b.1) (le_of_lt hδs2b.2)
      (by norm_num : (0 : ℝ) ≤ (133 : ℝ) / 2)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs2_lo : (332 : ℝ) / 5 ≤ ieeeDoubleKahanDenominator_s2 x := by
    rw [hs2eq']
    linarith [hs2_prod_round.1]
  have hs2_hi : ieeeDoubleKahanDenominator_s2 x ≤ (689 : ℝ) / 10 := by
    rw [hs2eq']
    linarith [hs2_prod_round.2]
  have hm3N : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanDenominator_s2 x)) := by
    have hm3_prod :=
      mul_interval_mono hxb.1 hxb.2 hs2_lo hs2_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ (332 : ℝ) / 5)
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm3_prod.1]
    · simp [BasicOp.exact]
      linarith [hm3_prod.2]
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanDenominator_s2 x) hm3N with
    ⟨δm3, hδm3, hm3eq⟩
  have hδm3b := kahanIeeeDouble_delta_bounds hδm3
  have hm3eq' :
      ieeeDoubleKahanDenominator_m3 x =
        (x * ieeeDoubleKahanDenominator_s2 x) * (1 + δm3) := by
    simpa [ieeeDoubleKahanDenominator_m3, BasicOp.exact] using hm3eq
  have hm3_exact_lo : (106 : ℝ) ≤ x * ieeeDoubleKahanDenominator_s2 x := by
    have hm3_prod :=
      mul_interval_mono hxb.1 hxb.2 hs2_lo hs2_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ (332 : ℝ) / 5)
    linarith [hm3_prod.1]
  have hm3_exact_hi : x * ieeeDoubleKahanDenominator_s2 x ≤ (554 : ℝ) / 5 := by
    have hm3_prod :=
      mul_interval_mono hxb.1 hxb.2 hs2_lo hs2_hi
        (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
        (by norm_num : (0 : ℝ) ≤ (332 : ℝ) / 5)
    linarith [hm3_prod.2]
  have hm3_prod_round :=
    mul_interval_mono hm3_exact_lo hm3_exact_hi
      (le_of_lt hδm3b.1) (le_of_lt hδm3b.2)
      (by norm_num : (0 : ℝ) ≤ 106)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm3_lo : (105 : ℝ) ≤ ieeeDoubleKahanDenominator_m3 x := by
    rw [hm3eq']
    linarith [hm3_prod_round.1]
  have hm3_hi : ieeeDoubleKahanDenominator_m3 x ≤ (111 : ℝ) := by
    rw [hm3eq']
    linarith [hm3_prod_round.2]
  have hresultN : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (BasicOp.exact BasicOp.sub 112 (ieeeDoubleKahanDenominator_m3 x)) := by
    apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
    · simp [BasicOp.exact]
      linarith [hm3_hi]
    · simp [BasicOp.exact]
      linarith [hm3_lo]
  exact
    { s0 := hs0N
      m1 := hm1N
      s1 := hs1N
      m2 := hm2N
      s2 := hs2N
      m3 := hm3N
      result := hresultN }

set_option maxHeartbeats 800000 in
theorem kahanHornerNumeratorErrorEval_source_interval_bounds
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52)
    (δ : Fin 8 → ℝ) (hδ : ∀ i, |δ i| < kahanIeeeDoubleUnitRoundoff) :
    (10 : ℝ) ≤ kahanHornerNumeratorErrorEval x δ ∧
      kahanHornerNumeratorErrorEval x δ ≤ 58 := by
  have hxb := kahan_source_interval_x_bounds hxlo hxhi
  have hδ0 := kahanIeeeDouble_delta_bounds (hδ 0)
  have hδ1 := kahanIeeeDouble_delta_bounds (hδ 1)
  have hδ2 := kahanIeeeDouble_delta_bounds (hδ 2)
  have hδ3 := kahanIeeeDouble_delta_bounds (hδ 3)
  have hδ4 := kahanIeeeDouble_delta_bounds (hδ 4)
  have hδ5 := kahanIeeeDouble_delta_bounds (hδ 5)
  have hδ6 := kahanIeeeDouble_delta_bounds (hδ 6)
  have hδ7 := kahanIeeeDouble_delta_bounds (hδ 7)
  let m0 := (4 * x) * (1 + δ 0)
  have hm0_exact_lo : (6 : ℝ) ≤ 4 * x := by linarith [hxb.1]
  have hm0_exact_hi : 4 * x ≤ 7 := by linarith [hxb.2]
  have hm0_prod :=
    mul_interval_mono hm0_exact_lo hm0_exact_hi
      (le_of_lt hδ0.1) (le_of_lt hδ0.2)
      (by norm_num : (0 : ℝ) ≤ 6)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm0_lo : (5 : ℝ) ≤ m0 := by
    dsimp [m0]
    linarith [hm0_prod.1]
  have hm0_hi : m0 ≤ (8 : ℝ) := by
    dsimp [m0]
    linarith [hm0_prod.2]
  let s0 := (59 - m0) * (1 + δ 1)
  have hs0_exact_lo : (51 : ℝ) ≤ 59 - m0 := by linarith [hm0_hi]
  have hs0_exact_hi : 59 - m0 ≤ (54 : ℝ) := by linarith [hm0_lo]
  have hs0_prod :=
    mul_interval_mono hs0_exact_lo hs0_exact_hi
      (le_of_lt hδ1.1) (le_of_lt hδ1.2)
      (by norm_num : (0 : ℝ) ≤ 51)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs0_lo : (50 : ℝ) ≤ s0 := by
    dsimp [s0]
    linarith [hs0_prod.1]
  have hs0_hi : s0 ≤ (55 : ℝ) := by
    dsimp [s0]
    linarith [hs0_prod.2]
  let m1 := (x * s0) * (1 + δ 2)
  have hm1_prod :=
    mul_interval_mono hxb.1 hxb.2 hs0_lo hs0_hi
      (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
      (by norm_num : (0 : ℝ) ≤ 50)
  have hm1_exact_lo : (80 : ℝ) ≤ x * s0 := by linarith [hm1_prod.1]
  have hm1_exact_hi : x * s0 ≤ (89 : ℝ) := by linarith [hm1_prod.2]
  have hm1_prod_round :=
    mul_interval_mono hm1_exact_lo hm1_exact_hi
      (le_of_lt hδ2.1) (le_of_lt hδ2.2)
      (by norm_num : (0 : ℝ) ≤ 80)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm1_lo : (79 : ℝ) ≤ m1 := by
    dsimp [m1]
    linarith [hm1_prod_round.1]
  have hm1_hi : m1 ≤ (90 : ℝ) := by
    dsimp [m1]
    linarith [hm1_prod_round.2]
  let s1 := (324 - m1) * (1 + δ 3)
  have hs1_exact_lo : (234 : ℝ) ≤ 324 - m1 := by linarith [hm1_hi]
  have hs1_exact_hi : 324 - m1 ≤ (245 : ℝ) := by linarith [hm1_lo]
  have hs1_prod :=
    mul_interval_mono hs1_exact_lo hs1_exact_hi
      (le_of_lt hδ3.1) (le_of_lt hδ3.2)
      (by norm_num : (0 : ℝ) ≤ 234)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs1_lo : (233 : ℝ) ≤ s1 := by
    dsimp [s1]
    linarith [hs1_prod.1]
  have hs1_hi : s1 ≤ (246 : ℝ) := by
    dsimp [s1]
    linarith [hs1_prod.2]
  let m2 := (x * s1) * (1 + δ 4)
  have hm2_prod :=
    mul_interval_mono hxb.1 hxb.2 hs1_lo hs1_hi
      (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
      (by norm_num : (0 : ℝ) ≤ 233)
  have hm2_exact_lo : (374 : ℝ) ≤ x * s1 := by linarith [hm2_prod.1]
  have hm2_exact_hi : x * s1 ≤ (396 : ℝ) := by linarith [hm2_prod.2]
  have hm2_prod_round :=
    mul_interval_mono hm2_exact_lo hm2_exact_hi
      (le_of_lt hδ4.1) (le_of_lt hδ4.2)
      (by norm_num : (0 : ℝ) ≤ 374)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm2_lo : (373 : ℝ) ≤ m2 := by
    dsimp [m2]
    linarith [hm2_prod_round.1]
  have hm2_hi : m2 ≤ (397 : ℝ) := by
    dsimp [m2]
    linarith [hm2_prod_round.2]
  let s2 := (751 - m2) * (1 + δ 5)
  have hs2_exact_lo : (354 : ℝ) ≤ 751 - m2 := by linarith [hm2_hi]
  have hs2_exact_hi : 751 - m2 ≤ (378 : ℝ) := by linarith [hm2_lo]
  have hs2_prod :=
    mul_interval_mono hs2_exact_lo hs2_exact_hi
      (le_of_lt hδ5.1) (le_of_lt hδ5.2)
      (by norm_num : (0 : ℝ) ≤ 354)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs2_lo : (353 : ℝ) ≤ s2 := by
    dsimp [s2]
    linarith [hs2_prod.1]
  have hs2_hi : s2 ≤ (379 : ℝ) := by
    dsimp [s2]
    linarith [hs2_prod.2]
  let m3 := (x * s2) * (1 + δ 6)
  have hm3_prod :=
    mul_interval_mono hxb.1 hxb.2 hs2_lo hs2_hi
      (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
      (by norm_num : (0 : ℝ) ≤ 353)
  have hm3_exact_lo : (566 : ℝ) ≤ x * s2 := by linarith [hm3_prod.1]
  have hm3_exact_hi : x * s2 ≤ (610 : ℝ) := by linarith [hm3_prod.2]
  have hm3_prod_round :=
    mul_interval_mono hm3_exact_lo hm3_exact_hi
      (le_of_lt hδ6.1) (le_of_lt hδ6.2)
      (by norm_num : (0 : ℝ) ≤ 566)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm3_lo : (565 : ℝ) ≤ m3 := by
    dsimp [m3]
    linarith [hm3_prod_round.1]
  have hm3_hi : m3 ≤ (611 : ℝ) := by
    dsimp [m3]
    linarith [hm3_prod_round.2]
  let result := (622 - m3) * (1 + δ 7)
  have hresult_exact_lo : (11 : ℝ) ≤ 622 - m3 := by linarith [hm3_hi]
  have hresult_exact_hi : 622 - m3 ≤ (57 : ℝ) := by linarith [hm3_lo]
  have hresult_prod :=
    mul_interval_mono hresult_exact_lo hresult_exact_hi
      (le_of_lt hδ7.1) (le_of_lt hδ7.2)
      (by norm_num : (0 : ℝ) ≤ 11)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hresult_lo : (10 : ℝ) ≤ result := by
    dsimp [result]
    linarith [hresult_prod.1]
  have hresult_hi : result ≤ (58 : ℝ) := by
    dsimp [result]
    linarith [hresult_prod.2]
  simpa [kahanHornerNumeratorErrorEval, result, m3, s2, m2, s1, m1, s0, m0]
    using And.intro hresult_lo hresult_hi

set_option maxHeartbeats 800000 in
theorem kahanHornerDenominatorErrorEval_source_interval_bounds
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52)
    (δ : Fin 7 → ℝ) (hδ : ∀ i, |δ i| < kahanIeeeDoubleUnitRoundoff) :
    (999 : ℝ) / 1000 ≤ kahanHornerDenominatorErrorEval x δ ∧
      kahanHornerDenominatorErrorEval x δ ≤ 8 := by
  have hxb := kahan_source_interval_x_bounds hxlo hxhi
  have hδ0 := kahanIeeeDouble_delta_bounds (hδ 0)
  have hδ1 := kahanIeeeDouble_delta_bounds (hδ 1)
  have hδ2 := kahanIeeeDouble_delta_bounds (hδ 2)
  have hδ3 := kahanIeeeDouble_delta_bounds (hδ 3)
  have hδ4 := kahanIeeeDouble_delta_bounds (hδ 4)
  have hδ5 := kahanIeeeDouble_delta_bounds (hδ 5)
  have hδ6 := kahanIeeeDouble_delta_bounds (hδ 6)
  let s0 := (14 - x) * (1 + δ 0)
  have hs0_exact_lo : (1239 : ℝ) / 100 ≤ 14 - x := by linarith [hxb.2]
  have hs0_exact_hi : 14 - x ≤ (25 : ℝ) / 2 := by linarith [hxb.1]
  have hs0_prod :=
    mul_interval_mono hs0_exact_lo hs0_exact_hi
      (le_of_lt hδ0.1) (le_of_lt hδ0.2)
      (by norm_num : (0 : ℝ) ≤ (1239 : ℝ) / 100)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs0_lo : (123 : ℝ) / 10 ≤ s0 := by
    dsimp [s0]
    linarith [hs0_prod.1]
  have hs0_hi : s0 ≤ (63 : ℝ) / 5 := by
    dsimp [s0]
    linarith [hs0_prod.2]
  let m1 := (x * s0) * (1 + δ 1)
  have hm1_prod :=
    mul_interval_mono hxb.1 hxb.2 hs0_lo hs0_hi
      (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
      (by norm_num : (0 : ℝ) ≤ (123 : ℝ) / 10)
  have hm1_exact_lo : (197 : ℝ) / 10 ≤ x * s0 := by linarith [hm1_prod.1]
  have hm1_exact_hi : x * s0 ≤ (102 : ℝ) / 5 := by linarith [hm1_prod.2]
  have hm1_prod_round :=
    mul_interval_mono hm1_exact_lo hm1_exact_hi
      (le_of_lt hδ1.1) (le_of_lt hδ1.2)
      (by norm_num : (0 : ℝ) ≤ (197 : ℝ) / 10)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm1_lo : (98 : ℝ) / 5 ≤ m1 := by
    dsimp [m1]
    linarith [hm1_prod_round.1]
  have hm1_hi : m1 ≤ (103 : ℝ) / 5 := by
    dsimp [m1]
    linarith [hm1_prod_round.2]
  let s1 := (72 - m1) * (1 + δ 2)
  have hs1_exact_lo : (257 : ℝ) / 5 ≤ 72 - m1 := by linarith [hm1_hi]
  have hs1_exact_hi : 72 - m1 ≤ (262 : ℝ) / 5 := by linarith [hm1_lo]
  have hs1_prod :=
    mul_interval_mono hs1_exact_lo hs1_exact_hi
      (le_of_lt hδ2.1) (le_of_lt hδ2.2)
      (by norm_num : (0 : ℝ) ≤ (257 : ℝ) / 5)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs1_lo : (513 : ℝ) / 10 ≤ s1 := by
    dsimp [s1]
    linarith [hs1_prod.1]
  have hs1_hi : s1 ≤ (105 : ℝ) / 2 := by
    dsimp [s1]
    linarith [hs1_prod.2]
  let m2 := (x * s1) * (1 + δ 3)
  have hm2_prod :=
    mul_interval_mono hxb.1 hxb.2 hs1_lo hs1_hi
      (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
      (by norm_num : (0 : ℝ) ≤ (513 : ℝ) / 10)
  have hm2_exact_lo : (823 : ℝ) / 10 ≤ x * s1 := by linarith [hm2_prod.1]
  have hm2_exact_hi : x * s1 ≤ (422 : ℝ) / 5 := by linarith [hm2_prod.2]
  have hm2_prod_round :=
    mul_interval_mono hm2_exact_lo hm2_exact_hi
      (le_of_lt hδ3.1) (le_of_lt hδ3.2)
      (by norm_num : (0 : ℝ) ≤ (823 : ℝ) / 10)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm2_lo : (411 : ℝ) / 5 ≤ m2 := by
    dsimp [m2]
    linarith [hm2_prod_round.1]
  have hm2_hi : m2 ≤ (169 : ℝ) / 2 := by
    dsimp [m2]
    linarith [hm2_prod_round.2]
  let s2 := (151 - m2) * (1 + δ 4)
  have hs2_exact_lo : (133 : ℝ) / 2 ≤ 151 - m2 := by linarith [hm2_hi]
  have hs2_exact_hi : 151 - m2 ≤ (344 : ℝ) / 5 := by linarith [hm2_lo]
  have hs2_prod :=
    mul_interval_mono hs2_exact_lo hs2_exact_hi
      (le_of_lt hδ4.1) (le_of_lt hδ4.2)
      (by norm_num : (0 : ℝ) ≤ (133 : ℝ) / 2)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hs2_lo : (332 : ℝ) / 5 ≤ s2 := by
    dsimp [s2]
    linarith [hs2_prod.1]
  have hs2_hi : s2 ≤ (689 : ℝ) / 10 := by
    dsimp [s2]
    linarith [hs2_prod.2]
  let m3 := (x * s2) * (1 + δ 5)
  have hm3_prod :=
    mul_interval_mono hxb.1 hxb.2 hs2_lo hs2_hi
      (by norm_num : (0 : ℝ) ≤ (803 : ℝ) / 500)
      (by norm_num : (0 : ℝ) ≤ (332 : ℝ) / 5)
  have hm3_exact_lo : (106 : ℝ) ≤ x * s2 := by linarith [hm3_prod.1]
  have hm3_exact_hi : x * s2 ≤ (554 : ℝ) / 5 := by linarith [hm3_prod.2]
  have hm3_prod_round :=
    mul_interval_mono hm3_exact_lo hm3_exact_hi
      (le_of_lt hδ5.1) (le_of_lt hδ5.2)
      (by norm_num : (0 : ℝ) ≤ 106)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hm3_lo : (105 : ℝ) ≤ m3 := by
    dsimp [m3]
    linarith [hm3_prod_round.1]
  have hm3_hi : m3 ≤ (111 : ℝ) := by
    dsimp [m3]
    linarith [hm3_prod_round.2]
  let result := (112 - m3) * (1 + δ 6)
  have hresult_exact_lo : (1 : ℝ) ≤ 112 - m3 := by linarith [hm3_hi]
  have hresult_exact_hi : 112 - m3 ≤ (7 : ℝ) := by linarith [hm3_lo]
  have hresult_prod :=
    mul_interval_mono hresult_exact_lo hresult_exact_hi
      (le_of_lt hδ6.1) (le_of_lt hδ6.2)
      (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) ≤ (999 : ℝ) / 1000)
  have hresult_lo : (999 : ℝ) / 1000 ≤ result := by
    dsimp [result]
    linarith [hresult_prod.1]
  have hresult_hi : result ≤ (8 : ℝ) := by
    dsimp [result]
    linarith [hresult_prod.2]
  simpa [kahanHornerDenominatorErrorEval, result, m3, s2, m2, s1, m1, s0]
    using And.intro hresult_lo hresult_hi

/-- The numerator IEEE-double Horner trace is finite-normal on every point of
the source interval used for Figure 1.6. -/
theorem ieeeDoubleKahanHornerNumerator_eq_errorEval_on_source_interval
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    ∃ δ : Fin 8 → ℝ,
      (∀ i, |δ i| < kahanIeeeDoubleUnitRoundoff) ∧
        ieeeDoubleKahanHornerNumerator x =
          kahanHornerNumeratorErrorEval x δ :=
  ieeeDoubleKahanHornerNumerator_eq_errorEval_of_finiteNormal x
    (ieeeDoubleKahanNumeratorNormalTrace_of_source_interval hxlo hxhi)

/-- The denominator IEEE-double Horner trace is finite-normal on every point of
the source interval used for Figure 1.6. -/
theorem ieeeDoubleKahanHornerDenominator_eq_errorEval_on_source_interval
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    ∃ δ : Fin 7 → ℝ,
      (∀ i, |δ i| < kahanIeeeDoubleUnitRoundoff) ∧
        ieeeDoubleKahanHornerDenominator x =
          kahanHornerDenominatorErrorEval x δ :=
  ieeeDoubleKahanHornerDenominator_eq_errorEval_of_finiteNormal x
    (ieeeDoubleKahanDenominatorNormalTrace_of_source_interval hxlo hxhi)

theorem ieeeDoubleKahanHornerNumerator_source_interval_bounds
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    (10 : ℝ) ≤ ieeeDoubleKahanHornerNumerator x ∧
      ieeeDoubleKahanHornerNumerator x ≤ 58 := by
  rcases ieeeDoubleKahanHornerNumerator_eq_errorEval_on_source_interval
      hxlo hxhi with ⟨δ, hδ, hnum⟩
  have hbounds :=
    kahanHornerNumeratorErrorEval_source_interval_bounds hxlo hxhi δ hδ
  rw [hnum]
  exact hbounds

theorem ieeeDoubleKahanHornerDenominator_source_interval_bounds
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    (999 : ℝ) / 1000 ≤ ieeeDoubleKahanHornerDenominator x ∧
      ieeeDoubleKahanHornerDenominator x ≤ 8 := by
  rcases ieeeDoubleKahanHornerDenominator_eq_errorEval_on_source_interval
      hxlo hxhi with ⟨δ, hδ, hden⟩
  have hbounds :=
    kahanHornerDenominatorErrorEval_source_interval_bounds hxlo hxhi δ hδ
  rw [hden]
  exact hbounds

theorem ieeeDoubleKahanQuotientNormalTrace_of_source_interval
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    IeeeDoubleKahanQuotientNormalTrace x := by
  have hnumTrace := ieeeDoubleKahanNumeratorNormalTrace_of_source_interval hxlo hxhi
  have hdenTrace := ieeeDoubleKahanDenominatorNormalTrace_of_source_interval hxlo hxhi
  have hnumBounds := ieeeDoubleKahanHornerNumerator_source_interval_bounds hxlo hxhi
  have hdenBounds := ieeeDoubleKahanHornerDenominator_source_interval_bounds hxlo hxhi
  have hdenPos : 0 < ieeeDoubleKahanHornerDenominator x := by
    nlinarith [hdenBounds.1]
  refine
    { numerator := hnumTrace
      denominator := hdenTrace
      quotient := ?_ }
  apply ieeeDouble_finiteNormalRange_of_pos_between_one_thousand
  · simp [BasicOp.exact]
    rw [le_div_iff₀ hdenPos]
    linarith [hnumBounds.1, hdenBounds.2]
  · simp [BasicOp.exact]
    rw [div_le_iff₀ hdenPos]
    nlinarith [hnumBounds.2, hdenBounds.1]

theorem ieeeDoubleKahanRationalFunction_eq_errorEval_on_source_interval
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    ∃ δN : Fin 8 → ℝ, ∃ δD : Fin 7 → ℝ, ∃ δq : ℝ,
      (∀ i, |δN i| < kahanIeeeDoubleUnitRoundoff) ∧
      (∀ i, |δD i| < kahanIeeeDoubleUnitRoundoff) ∧
      |δq| < kahanIeeeDoubleUnitRoundoff ∧
        ieeeDoubleKahanRationalFunction x =
          (kahanHornerNumeratorErrorEval x δN /
            kahanHornerDenominatorErrorEval x δD) * (1 + δq) :=
  ieeeDoubleKahanRationalFunction_eq_errorEval_of_finiteNormal x
    (ieeeDoubleKahanQuotientNormalTrace_of_source_interval hxlo hxhi)

end NumStability
