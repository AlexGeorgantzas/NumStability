import NumStability.Source.Higham.Chapter01.Section17.SourceInterval

namespace NumStability

/-!
# Nonrandom rounding grid and exact-curve variation

Polynomial identities, source-grid variation bounds, and the selected-pair
error-spread bridge for Kahan's Higham Section 1.17 example. The culminating
result is
`ieeeDoubleKahanRationalFunction_175_289_error_spread_gt_of_output_spread`.
-/

/-- The numerator is the quartic polynomial displayed by the Horner form. -/
theorem kahanHornerNumerator_eq_poly (x : ℝ) :
    kahanHornerNumerator x =
      622 - 751 * x + 324 * x ^ 2 - 59 * x ^ 3 + 4 * x ^ 4 := by
  unfold kahanHornerNumerator
  ring

/-- The denominator is the quartic polynomial displayed by the Horner form. -/
theorem kahanHornerDenominator_eq_poly (x : ℝ) :
    kahanHornerDenominator x =
      112 - 151 * x + 72 * x ^ 2 - 14 * x ^ 3 + x ^ 4 := by
  unfold kahanHornerDenominator
  ring

/-- The denominator expanded around the first source grid point `1.606`. -/
theorem kahanHornerDenominator_shifted_eq (t : ℝ) :
    kahanHornerDenominator ((803 : ℝ) / 500 + t) =
      241244257481 / 62500000000 -
        359215623 / 31250000 * t +
        2502927 / 125000 * t ^ 2 -
        947 / 125 * t ^ 3 + t ^ 4 := by
  rw [kahanHornerDenominator_eq_poly]
  ring

/-- The numerator expanded around the first source grid point `1.606`. -/
theorem kahanHornerNumerator_shifted_eq (t : ℝ) :
    kahanHornerNumerator ((803 : ℝ) / 500 + t) =
      131966286839 / 3906250000 -
        3142522617 / 31250000 * t +
        6352479 / 62500 * t ^ 2 -
        4163 / 125 * t ^ 3 + 4 * t ^ 4 := by
  rw [kahanHornerNumerator_eq_poly]
  ring

/-- Source grid point `x = 1.606 + (k-1) * 2^-52`, with source indexing. -/
noncomputable def kahanHornerGridPoint (k : ℕ) : ℝ :=
  (803 : ℝ) / 500 + ((k : ℝ) - 1) / (2 : ℝ) ^ 52

/-- The first source grid point, `k = 1`, is `1.606`. -/
theorem kahanHornerGridPoint_one :
    kahanHornerGridPoint 1 = (803 : ℝ) / 500 := by
  norm_num [kahanHornerGridPoint]

/-- Consecutive source grid points are separated by `2^-52`. -/
theorem kahanHornerGridPoint_succ_sub (k : ℕ) :
    kahanHornerGridPoint (k + 1) - kahanHornerGridPoint k =
      1 / (2 : ℝ) ^ 52 := by
  unfold kahanHornerGridPoint
  rw [Nat.cast_add, Nat.cast_one]
  ring

/-- The final source grid point for `k = 361`. -/
theorem kahanHornerGridPoint_three_sixty_one :
    kahanHornerGridPoint 361 =
      (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52 := by
  norm_num [kahanHornerGridPoint]

/-- Every source grid point lies in the sampled interval starting at `1.606`
and ending at `1.606 + 360*2^-52`. -/
theorem kahanHornerGridPoint_mem_source_interval
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    0 ≤ kahanHornerGridPoint k - (803 : ℝ) / 500 ∧
      kahanHornerGridPoint k - (803 : ℝ) / 500 ≤ 360 / (2 : ℝ) ^ 52 := by
  unfold kahanHornerGridPoint
  constructor
  · have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    nlinarith
  · have hk361R : (k : ℝ) ≤ 361 := by exact_mod_cast hk361
    nlinarith

/-- Any two of the 361 source grid points are at most the full source
interval width apart. -/
theorem kahanHornerGridPoint_pairwise_distance_le_source_width
    (k l : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361)
    (hl1 : 1 ≤ l) (hl361 : l ≤ 361) :
    |kahanHornerGridPoint k - kahanHornerGridPoint l| ≤
      360 / (2 : ℝ) ^ 52 := by
  have hk := kahanHornerGridPoint_mem_source_interval k hk1 hk361
  have hl := kahanHornerGridPoint_mem_source_interval l hl1 hl361
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- Source-grid specialization of the finite-normal numerator certificate. -/
theorem ieeeDoubleKahanNumeratorNormalTrace_of_source_grid
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    IeeeDoubleKahanNumeratorNormalTrace (kahanHornerGridPoint k) := by
  have hmem := kahanHornerGridPoint_mem_source_interval k hk1 hk361
  apply ieeeDoubleKahanNumeratorNormalTrace_of_source_interval
  · linarith [hmem.1]
  · linarith [hmem.2]

/-- Source-grid specialization of the finite-normal denominator certificate. -/
theorem ieeeDoubleKahanDenominatorNormalTrace_of_source_grid
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    IeeeDoubleKahanDenominatorNormalTrace (kahanHornerGridPoint k) := by
  have hmem := kahanHornerGridPoint_mem_source_interval k hk1 hk361
  apply ieeeDoubleKahanDenominatorNormalTrace_of_source_interval
  · linarith [hmem.1]
  · linarith [hmem.2]

/-- Source-grid specialization of the IEEE-double numerator local-error
expansion. -/
theorem ieeeDoubleKahanHornerNumerator_grid_eq_errorEval
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    ∃ δ : Fin 8 → ℝ,
      (∀ i, |δ i| < kahanIeeeDoubleUnitRoundoff) ∧
        ieeeDoubleKahanHornerNumerator (kahanHornerGridPoint k) =
          kahanHornerNumeratorErrorEval (kahanHornerGridPoint k) δ :=
  ieeeDoubleKahanHornerNumerator_eq_errorEval_of_finiteNormal
    (kahanHornerGridPoint k)
    (ieeeDoubleKahanNumeratorNormalTrace_of_source_grid k hk1 hk361)

/-- Source-grid specialization of the IEEE-double denominator local-error
expansion. -/
theorem ieeeDoubleKahanHornerDenominator_grid_eq_errorEval
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    ∃ δ : Fin 7 → ℝ,
      (∀ i, |δ i| < kahanIeeeDoubleUnitRoundoff) ∧
        ieeeDoubleKahanHornerDenominator (kahanHornerGridPoint k) =
          kahanHornerDenominatorErrorEval (kahanHornerGridPoint k) δ :=
  ieeeDoubleKahanHornerDenominator_eq_errorEval_of_finiteNormal
    (kahanHornerGridPoint k)
    (ieeeDoubleKahanDenominatorNormalTrace_of_source_grid k hk1 hk361)

/-- Source-grid specialization of the complete IEEE-double quotient
finite-normal certificate. -/
theorem ieeeDoubleKahanQuotientNormalTrace_of_source_grid
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    IeeeDoubleKahanQuotientNormalTrace (kahanHornerGridPoint k) := by
  have hmem := kahanHornerGridPoint_mem_source_interval k hk1 hk361
  apply ieeeDoubleKahanQuotientNormalTrace_of_source_interval
  · linarith [hmem.1]
  · linarith [hmem.2]

/-- Source-grid specialization of the full IEEE-double rounded rational-function
local-error expansion, including the final rounded division. -/
theorem ieeeDoubleKahanRationalFunction_grid_eq_errorEval
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    ∃ δN : Fin 8 → ℝ, ∃ δD : Fin 7 → ℝ, ∃ δq : ℝ,
      (∀ i, |δN i| < kahanIeeeDoubleUnitRoundoff) ∧
      (∀ i, |δD i| < kahanIeeeDoubleUnitRoundoff) ∧
      |δq| < kahanIeeeDoubleUnitRoundoff ∧
        ieeeDoubleKahanRationalFunction (kahanHornerGridPoint k) =
          (kahanHornerNumeratorErrorEval (kahanHornerGridPoint k) δN /
            kahanHornerDenominatorErrorEval (kahanHornerGridPoint k) δD) *
              (1 + δq) :=
  ieeeDoubleKahanRationalFunction_eq_errorEval_of_finiteNormal
    (kahanHornerGridPoint k)
    (ieeeDoubleKahanQuotientNormalTrace_of_source_grid k hk1 hk361)

/-- At the first grid point the exact denominator is positive. -/
theorem kahanHornerDenominator_grid_one_pos :
    0 < kahanHornerDenominator (kahanHornerGridPoint 1) := by
  norm_num [kahanHornerGridPoint_one, kahanHornerDenominator]

/-- On the source grid interval the exact denominator is bounded away from
zero by the simple lower bound `3`. -/
theorem kahanHornerDenominator_gt_three_on_source_grid_interval (t : ℝ)
    (_ht0 : 0 ≤ t) (ht : t ≤ 360 / (2 : ℝ) ^ 52) :
    3 < kahanHornerDenominator ((803 : ℝ) / 500 + t) := by
  rw [kahanHornerDenominator_shifted_eq]
  nlinarith [ht]

/-- The exact denominator is positive on the whole source grid interval
`1.606 <= x <= 1.606 + 360*2^-52`. -/
theorem kahanHornerDenominator_pos_on_source_grid_interval (t : ℝ)
    (_ht0 : 0 ≤ t) (ht : t ≤ 360 / (2 : ℝ) ^ 52) :
    0 < kahanHornerDenominator ((803 : ℝ) / 500 + t) := by
  rw [kahanHornerDenominator_shifted_eq]
  nlinarith [ht]

/-- The exact denominator is positive at every one of the 361 source grid
points used in Figure 1.6. -/
theorem kahanHornerDenominator_grid_pos_of_one_le_of_le_three_sixty_one
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    0 < kahanHornerDenominator (kahanHornerGridPoint k) := by
  unfold kahanHornerGridPoint
  apply kahanHornerDenominator_pos_on_source_grid_interval
  · have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    exact div_nonneg (sub_nonneg.mpr hk1R) (by positivity)
  · have hk361R : (k : ℝ) ≤ 361 := by exact_mod_cast hk361
    have hnum : (k : ℝ) - 1 ≤ 360 := by linarith
    exact div_le_div_of_nonneg_right hnum (by positivity)

/-- Exact Euclidean-algorithm identity behind the continued-fraction
reference curve.  The hypotheses are precisely the nonzero intermediate
denominators generated by the continued fraction and the displayed rational
function denominator. -/
theorem kahanContinuedFraction_eq_rationalFunction (x : ℝ)
    (h0 : x - 3 ≠ 0)
    (hp2 : kahanContinuedFractionP2 x ≠ 0)
    (hp1 : kahanContinuedFractionP1 x ≠ 0)
    (hD : kahanHornerDenominator x ≠ 0) :
    kahanContinuedFraction x = kahanRationalFunction x := by
  have htail1 :
      kahanContinuedFractionTail1 x =
        kahanContinuedFractionP2 x / (x - 3) := by
    unfold kahanContinuedFractionTail1 kahanContinuedFractionP2
    field_simp [h0]
    ring
  have htail2 :
      kahanContinuedFractionTail2 x =
        kahanContinuedFractionP1 x / kahanContinuedFractionP2 x := by
    unfold kahanContinuedFractionTail2
    rw [htail1]
    field_simp [h0, hp2]
    unfold kahanContinuedFractionP1 kahanContinuedFractionP2
    ring_nf
  have htail3 :
      kahanContinuedFractionTail3 x =
        kahanHornerDenominator x / kahanContinuedFractionP1 x := by
    unfold kahanContinuedFractionTail3
    rw [htail2, kahanHornerDenominator_eq_poly]
    field_simp [hp1, hp2]
    unfold kahanContinuedFractionP1 kahanContinuedFractionP2
    ring_nf
    norm_num
    rfl
  have hnum :
      4 * kahanHornerDenominator x - 3 * kahanContinuedFractionP1 x =
        kahanHornerNumerator x := by
    rw [kahanHornerNumerator_eq_poly, kahanHornerDenominator_eq_poly]
    unfold kahanContinuedFractionP1
    ring
  unfold kahanContinuedFraction kahanRationalFunction
  rw [htail3]
  calc
    4 - 3 / (kahanHornerDenominator x / kahanContinuedFractionP1 x)
        = (4 * kahanHornerDenominator x -
              3 * kahanContinuedFractionP1 x) /
            kahanHornerDenominator x := by
          field_simp [hp1, hD]
    _ = kahanHornerNumerator x / kahanHornerDenominator x := by
          rw [hnum]

/-- On the source interval, the quadratic continued-fraction denominator is
bounded away from zero. -/
theorem kahanContinuedFractionP2_neg_on_source_interval
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    kahanContinuedFractionP2 x < 0 := by
  unfold kahanContinuedFractionP2
  nlinarith [hxlo, hxhi]

/-- On the source interval, the cubic continued-fraction denominator is
bounded away from zero. -/
theorem kahanContinuedFractionP1_neg_on_source_interval
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    kahanContinuedFractionP1 x < 0 := by
  unfold kahanContinuedFractionP1
  nlinarith [hxlo, hxhi]

/-- The continued-fraction reference expression equals the exact rational
function throughout the full source interval used for Figure 1.6. -/
theorem kahanContinuedFraction_eq_rationalFunction_on_source_interval
    {x : ℝ} (hxlo : (803 : ℝ) / 500 ≤ x)
    (hxhi : x ≤ (803 : ℝ) / 500 + 360 / (2 : ℝ) ^ 52) :
    kahanContinuedFraction x = kahanRationalFunction x := by
  have h0 : x - 3 ≠ 0 := by nlinarith
  have hp2 : kahanContinuedFractionP2 x ≠ 0 :=
    ne_of_lt (kahanContinuedFractionP2_neg_on_source_interval hxlo hxhi)
  have hp1 : kahanContinuedFractionP1 x ≠ 0 :=
    ne_of_lt (kahanContinuedFractionP1_neg_on_source_interval hxlo hxhi)
  have ht0 : 0 ≤ x - (803 : ℝ) / 500 := by linarith
  have htw : x - (803 : ℝ) / 500 ≤ 360 / (2 : ℝ) ^ 52 := by linarith
  have hDpos :=
    kahanHornerDenominator_pos_on_source_grid_interval
      (x - (803 : ℝ) / 500) ht0 htw
  have harg : (803 : ℝ) / 500 + (x - (803 : ℝ) / 500) = x := by ring
  rw [harg] at hDpos
  exact kahanContinuedFraction_eq_rationalFunction x h0 hp2 hp1
    (ne_of_gt hDpos)

/-- Source-grid specialization of the exact continued-fraction reference
identity. -/
theorem kahanContinuedFraction_grid_eq_rationalFunction
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    kahanContinuedFraction (kahanHornerGridPoint k) =
      kahanRationalFunction (kahanHornerGridPoint k) := by
  have hmem := kahanHornerGridPoint_mem_source_interval k hk1 hk361
  apply kahanContinuedFraction_eq_rationalFunction_on_source_interval
  · linarith [hmem.1]
  · linarith [hmem.2]

/-- Cubic kernel for the exact numerator difference
`r(1.606+t)-r(1.606)` after clearing denominators. -/
noncomputable def kahanRationalFunctionFirstDiffKernel (t : ℝ) : ℝ :=
  (-2292967119 / 125000000 : ℝ) * t ^ 3 +
    (7962026674329 / 62500000000 : ℝ) * t ^ 2 -
    (8879334238671813 / 31250000000000 : ℝ) * t +
    (2832765715803387 / 15625000000000000 : ℝ)

/-- On the tiny source interval, the exact first-difference kernel is bounded
by `1`.  This is deliberately conservative; it keeps the all-grid reference
curve proof parametric instead of checking the 361 points one by one. -/
theorem kahanRationalFunctionFirstDiffKernel_abs_lt_one
    (t : ℝ) (ht0 : 0 ≤ t) (htw : t ≤ 360 / (2 : ℝ) ^ 52) :
    |kahanRationalFunctionFirstDiffKernel t| < 1 := by
  unfold kahanRationalFunctionFirstDiffKernel
  rw [abs_lt]
  constructor <;> nlinarith [ht0, htw]

/-- Exact cleared-denominator factorization for the change from the first
source grid point to `1.606+t`. -/
theorem kahanRationalFunction_first_diff_num_factor (t : ℝ) :
    kahanHornerNumerator ((803 : ℝ) / 500 + t) *
          kahanHornerDenominator ((803 : ℝ) / 500) -
        kahanHornerNumerator ((803 : ℝ) / 500) *
          kahanHornerDenominator ((803 : ℝ) / 500 + t) =
      t * kahanRationalFunctionFirstDiffKernel t := by
  rw [kahanHornerNumerator_shifted_eq, kahanHornerDenominator_shifted_eq]
  norm_num [kahanRationalFunctionFirstDiffKernel, kahanHornerNumerator,
    kahanHornerDenominator]
  ring

/-- The exact reference rational function is virtually constant throughout the
whole source interval, relative to the first source grid point.  This is exact
real arithmetic only; it does not model double-precision Horner evaluation. -/
theorem kahanRationalFunction_source_interval_variation_from_first_lt
    (t : ℝ) (ht0 : 0 ≤ t) (htw : t ≤ 360 / (2 : ℝ) ^ 52) :
    |kahanRationalFunction ((803 : ℝ) / 500 + t) -
        kahanRationalFunction ((803 : ℝ) / 500)| < (1 : ℝ) / 10 ^ 12 := by
  have hD0 : 0 < kahanHornerDenominator ((803 : ℝ) / 500) := by
    norm_num [kahanHornerDenominator]
  have hDt : 0 < kahanHornerDenominator ((803 : ℝ) / 500 + t) :=
    kahanHornerDenominator_pos_on_source_grid_interval t ht0 htw
  simp only [kahanRationalFunction]
  rw [div_sub_div]
  · rw [abs_div]
    have hnum :
        |kahanHornerNumerator ((803 : ℝ) / 500 + t) *
              kahanHornerDenominator ((803 : ℝ) / 500) -
            kahanHornerNumerator ((803 : ℝ) / 500) *
              kahanHornerDenominator ((803 : ℝ) / 500 + t)|
          < (1 / 10 ^ 12) *
              |kahanHornerDenominator ((803 : ℝ) / 500 + t) *
                kahanHornerDenominator ((803 : ℝ) / 500)| := by
      rw [kahanRationalFunction_first_diff_num_factor t]
      rw [abs_mul, abs_of_nonneg ht0]
      have hkernel := kahanRationalFunctionFirstDiffKernel_abs_lt_one t ht0 htw
      have hnum_le :
          t * |kahanRationalFunctionFirstDiffKernel t| ≤ t := by
        exact mul_le_of_le_one_right ht0 (le_of_lt hkernel)
      have hDt3 :
          3 < kahanHornerDenominator ((803 : ℝ) / 500 + t) :=
        kahanHornerDenominator_gt_three_on_source_grid_interval t ht0 htw
      have hD03 : (3 : ℝ) < kahanHornerDenominator ((803 : ℝ) / 500) := by
        norm_num [kahanHornerDenominator]
      have hprod_abs :
          |kahanHornerDenominator ((803 : ℝ) / 500 + t) *
              kahanHornerDenominator ((803 : ℝ) / 500)| =
            kahanHornerDenominator ((803 : ℝ) / 500 + t) *
              kahanHornerDenominator ((803 : ℝ) / 500) := by
        exact abs_of_pos (mul_pos hDt hD0)
      rw [hprod_abs]
      have ht_target :
          t < (1 / 10 ^ 12) *
              (kahanHornerDenominator ((803 : ℝ) / 500 + t) *
                kahanHornerDenominator ((803 : ℝ) / 500)) := by
        nlinarith [htw, hDt3, hD03]
      exact lt_of_le_of_lt hnum_le ht_target
    have hdenAbsPos :
        0 < |kahanHornerDenominator ((803 : ℝ) / 500 + t) *
              kahanHornerDenominator ((803 : ℝ) / 500)| :=
      abs_pos.mpr (mul_ne_zero (ne_of_gt hDt) (ne_of_gt hD0))
    rw [div_lt_iff₀ hdenAbsPos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnum
  · exact ne_of_gt hDt
  · exact ne_of_gt hD0

/-- Every one of the 361 exact source-grid reference values is within
`10^-12` of the first reference value. -/
theorem kahanRationalFunction_grid_variation_from_first_lt
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    |kahanRationalFunction (kahanHornerGridPoint k) -
        kahanRationalFunction (kahanHornerGridPoint 1)| < (1 : ℝ) / 10 ^ 12 := by
  have hmem := kahanHornerGridPoint_mem_source_interval k hk1 hk361
  have h :=
    kahanRationalFunction_source_interval_variation_from_first_lt
      (kahanHornerGridPoint k - (803 : ℝ) / 500) hmem.1 hmem.2
  have harg :
      (803 : ℝ) / 500 + (kahanHornerGridPoint k - (803 : ℝ) / 500) =
        kahanHornerGridPoint k := by
    ring
  rw [harg, ← kahanHornerGridPoint_one] at h
  exact h

/-- Every one of the 361 continued-fraction reference values is within
`10^-12` of the first continued-fraction reference value. -/
theorem kahanContinuedFraction_grid_variation_from_first_lt
    (k : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361) :
    |kahanContinuedFraction (kahanHornerGridPoint k) -
        kahanContinuedFraction (kahanHornerGridPoint 1)| < (1 : ℝ) / 10 ^ 12 := by
  rw [kahanContinuedFraction_grid_eq_rationalFunction k hk1 hk361,
    kahanContinuedFraction_grid_eq_rationalFunction 1 (by norm_num) (by norm_num)]
  exact kahanRationalFunction_grid_variation_from_first_lt k hk1 hk361

/-- Any two of the 361 exact source-grid reference values differ by less than
`2*10^-12`.  This closes the all-grid exact-reference part of the statement
that the reference curve is virtually constant; it is not a rounded Horner
evaluation theorem. -/
theorem kahanRationalFunction_grid_pair_variation_lt_two
    (k l : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361)
    (hl1 : 1 ≤ l) (hl361 : l ≤ 361) :
    |kahanRationalFunction (kahanHornerGridPoint k) -
        kahanRationalFunction (kahanHornerGridPoint l)| <
      (2 : ℝ) / 10 ^ 12 := by
  have hk := kahanRationalFunction_grid_variation_from_first_lt k hk1 hk361
  have hl := kahanRationalFunction_grid_variation_from_first_lt l hl1 hl361
  have htri :
      |kahanRationalFunction (kahanHornerGridPoint k) -
          kahanRationalFunction (kahanHornerGridPoint l)| ≤
        |kahanRationalFunction (kahanHornerGridPoint k) -
          kahanRationalFunction (kahanHornerGridPoint 1)| +
        |kahanRationalFunction (kahanHornerGridPoint l) -
          kahanRationalFunction (kahanHornerGridPoint 1)| := by
    calc
      |kahanRationalFunction (kahanHornerGridPoint k) -
          kahanRationalFunction (kahanHornerGridPoint l)|
          = |(kahanRationalFunction (kahanHornerGridPoint k) -
                kahanRationalFunction (kahanHornerGridPoint 1)) +
              (kahanRationalFunction (kahanHornerGridPoint 1) -
                kahanRationalFunction (kahanHornerGridPoint l))| := by ring_nf
      _ ≤ |kahanRationalFunction (kahanHornerGridPoint k) -
              kahanRationalFunction (kahanHornerGridPoint 1)| +
            |kahanRationalFunction (kahanHornerGridPoint 1) -
              kahanRationalFunction (kahanHornerGridPoint l)| := abs_add_le _ _
      _ =
          |kahanRationalFunction (kahanHornerGridPoint k) -
              kahanRationalFunction (kahanHornerGridPoint 1)| +
            |kahanRationalFunction (kahanHornerGridPoint l) -
              kahanRationalFunction (kahanHornerGridPoint 1)| := by
            rw [abs_sub_comm
              (kahanRationalFunction (kahanHornerGridPoint 1))
              (kahanRationalFunction (kahanHornerGridPoint l))]
  nlinarith

/-- Figure 1.6 diagnostic bridge.  Since the exact reference values on the
source grid differ by less than `2*10^-12`, any supplied rounded values whose
spread exceeds that reference spread by `η` must have rounding-error values
whose spread exceeds `η`.  This packages the nonrandom-pattern comparison
without enumerating the plotted IEEE-double values. -/
theorem kahanRoundedGrid_error_spread_gt_of_output_spread
    (rounded : ℕ → ℝ) (k l : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361)
    (hl1 : 1 ≤ l) (hl361 : l ≤ 361) (η : ℝ)
    (hspread :
      (2 : ℝ) / 10 ^ 12 + η < |rounded k - rounded l|) :
    η <
      |(rounded k - kahanRationalFunction (kahanHornerGridPoint k)) -
        (rounded l - kahanRationalFunction (kahanHornerGridPoint l))| := by
  set exactK : ℝ := kahanRationalFunction (kahanHornerGridPoint k)
  set exactL : ℝ := kahanRationalFunction (kahanHornerGridPoint l)
  set errDiff : ℝ := (rounded k - exactK) - (rounded l - exactL)
  have hexact :
      |exactK - exactL| < (2 : ℝ) / 10 ^ 12 := by
    simpa [exactK, exactL] using
      kahanRationalFunction_grid_pair_variation_lt_two
        k l hk1 hk361 hl1 hl361
  have htri :
      |rounded k - rounded l| ≤ |errDiff| + |exactK - exactL| := by
    calc
      |rounded k - rounded l|
          = |errDiff + (exactK - exactL)| := by
              simp [errDiff]
              ring_nf
      _ ≤ |errDiff| + |exactK - exactL| := abs_add_le _ _
  by_contra hnot
  have herr : |errDiff| ≤ η := le_of_not_gt hnot
  have hle : |rounded k - rounded l| ≤ η + (2 : ℝ) / 10 ^ 12 := by
    nlinarith
  nlinarith

/-- The same Figure 1.6 diagnostic bridge specialized to the concrete
IEEE-double finite round-to-even Horner path already modeled in this file.  A
future proof of a visible rounded-output spread can feed this theorem directly;
the theorem itself still avoids enumerating the 361 plotted values. -/
theorem ieeeDoubleKahanRationalFunction_grid_error_spread_gt_of_output_spread
    (k l : ℕ) (hk1 : 1 ≤ k) (hk361 : k ≤ 361)
    (hl1 : 1 ≤ l) (hl361 : l ≤ 361) (η : ℝ)
    (hspread :
      (2 : ℝ) / 10 ^ 12 + η <
        |ieeeDoubleKahanRationalFunction (kahanHornerGridPoint k) -
          ieeeDoubleKahanRationalFunction (kahanHornerGridPoint l)|) :
    η <
      |(ieeeDoubleKahanRationalFunction (kahanHornerGridPoint k) -
          kahanRationalFunction (kahanHornerGridPoint k)) -
        (ieeeDoubleKahanRationalFunction (kahanHornerGridPoint l) -
          kahanRationalFunction (kahanHornerGridPoint l))| := by
  exact
    kahanRoundedGrid_error_spread_gt_of_output_spread
      (fun j => ieeeDoubleKahanRationalFunction (kahanHornerGridPoint j))
      k l hk1 hk361 hl1 hl361 η hspread

/-- The exact rational function changes by less than `10^-12` between the
first and last source grid points. This is a conservative exact-arithmetic
substrate for the PDF's statement that the reference curve is virtually
constant on the tiny sampled interval; it is not a Horner rounding theorem. -/
theorem kahanRationalFunction_first_to_last_variation_lt :
    |kahanRationalFunction (kahanHornerGridPoint 361) -
        kahanRationalFunction (kahanHornerGridPoint 1)| < (1 : ℝ) / 10 ^ 12 := by
  norm_num [kahanRationalFunction, kahanHornerGridPoint,
    kahanHornerNumerator, kahanHornerDenominator]

/-- Endpoint version of the Figure 1.6 diagnostic bridge.  The exact
first-to-last reference spread is below `10^-12`, so a supplied rounded
endpoint spread exceeding that by `η` forces the rounded-error endpoints to
differ by more than `η`. -/
theorem kahanRoundedGrid_endpoint_error_spread_gt_of_output_spread
    (rounded : ℕ → ℝ) (η : ℝ)
    (hspread :
      (1 : ℝ) / 10 ^ 12 + η < |rounded 361 - rounded 1|) :
    η <
      |(rounded 361 - kahanRationalFunction (kahanHornerGridPoint 361)) -
        (rounded 1 - kahanRationalFunction (kahanHornerGridPoint 1))| := by
  set exactLast : ℝ := kahanRationalFunction (kahanHornerGridPoint 361)
  set exactFirst : ℝ := kahanRationalFunction (kahanHornerGridPoint 1)
  set errDiff : ℝ := (rounded 361 - exactLast) - (rounded 1 - exactFirst)
  have hexact :
      |exactLast - exactFirst| < (1 : ℝ) / 10 ^ 12 := by
    simpa [exactLast, exactFirst] using
      kahanRationalFunction_first_to_last_variation_lt
  have htri :
      |rounded 361 - rounded 1| ≤ |errDiff| + |exactLast - exactFirst| := by
    calc
      |rounded 361 - rounded 1|
          = |errDiff + (exactLast - exactFirst)| := by
              simp [errDiff]
              ring_nf
      _ ≤ |errDiff| + |exactLast - exactFirst| := abs_add_le _ _
  by_contra hnot
  have herr : |errDiff| ≤ η := le_of_not_gt hnot
  have hle : |rounded 361 - rounded 1| ≤ η + (1 : ℝ) / 10 ^ 12 := by
    nlinarith
  nlinarith

/-- Endpoint Figure 1.6 diagnostic bridge specialized to the concrete
IEEE-double finite round-to-even Horner path. -/
theorem ieeeDoubleKahanRationalFunction_endpoint_error_spread_gt_of_output_spread
    (η : ℝ)
    (hspread :
      (1 : ℝ) / 10 ^ 12 + η <
        |ieeeDoubleKahanRationalFunction (kahanHornerGridPoint 361) -
          ieeeDoubleKahanRationalFunction (kahanHornerGridPoint 1)|) :
    η <
      |(ieeeDoubleKahanRationalFunction (kahanHornerGridPoint 361) -
          kahanRationalFunction (kahanHornerGridPoint 361)) -
        (ieeeDoubleKahanRationalFunction (kahanHornerGridPoint 1) -
          kahanRationalFunction (kahanHornerGridPoint 1))| := by
  exact
    kahanRoundedGrid_endpoint_error_spread_gt_of_output_spread
      (fun j => ieeeDoubleKahanRationalFunction (kahanHornerGridPoint j))
      η hspread

/-- The exact reference spread between the selected grid points `175` and
`289` is below `10^-15`.  These are the two grid indices used for the compact
two-point Figure 1.6 diagnostic route. -/
theorem kahanRationalFunction_grid_175_289_variation_lt_one_e15 :
    |kahanRationalFunction (kahanHornerGridPoint 289) -
        kahanRationalFunction (kahanHornerGridPoint 175)| < (1 : ℝ) / 10 ^ 15 := by
  norm_num [kahanRationalFunction, kahanHornerGridPoint,
    kahanHornerNumerator, kahanHornerDenominator]

/-- Two-point Figure 1.6 diagnostic bridge for the selected grid points `175`
and `289`.  Because the exact reference spread is below `10^-15`, a supplied
rounded-output spread above `10^-15 + η` forces the rounded-error values at
these two points to differ by more than `η`. -/
theorem kahanRoundedGrid_175_289_error_spread_gt_of_output_spread
    (rounded : ℕ → ℝ) (η : ℝ)
    (hspread :
      (1 : ℝ) / 10 ^ 15 + η < |rounded 289 - rounded 175|) :
    η <
      |(rounded 289 - kahanRationalFunction (kahanHornerGridPoint 289)) -
        (rounded 175 - kahanRationalFunction (kahanHornerGridPoint 175))| := by
  set exactHi : ℝ := kahanRationalFunction (kahanHornerGridPoint 289)
  set exactLo : ℝ := kahanRationalFunction (kahanHornerGridPoint 175)
  set errDiff : ℝ := (rounded 289 - exactHi) - (rounded 175 - exactLo)
  have hexact :
      |exactHi - exactLo| < (1 : ℝ) / 10 ^ 15 := by
    simpa [exactHi, exactLo] using
      kahanRationalFunction_grid_175_289_variation_lt_one_e15
  have htri :
      |rounded 289 - rounded 175| ≤ |errDiff| + |exactHi - exactLo| := by
    calc
      |rounded 289 - rounded 175|
          = |errDiff + (exactHi - exactLo)| := by
              simp [errDiff]
              ring_nf
      _ ≤ |errDiff| + |exactHi - exactLo| := abs_add_le _ _
  by_contra hnot
  have herr : |errDiff| ≤ η := le_of_not_gt hnot
  have hle : |rounded 289 - rounded 175| ≤ η + (1 : ℝ) / 10 ^ 15 := by
    nlinarith
  nlinarith

/-- Selected-pair Figure 1.6 diagnostic bridge specialized to the modeled
IEEE-double finite round-to-even Horner path. -/
theorem ieeeDoubleKahanRationalFunction_175_289_error_spread_gt_of_output_spread
    (η : ℝ)
    (hspread :
      (1 : ℝ) / 10 ^ 15 + η <
        |ieeeDoubleKahanRationalFunction (kahanHornerGridPoint 289) -
          ieeeDoubleKahanRationalFunction (kahanHornerGridPoint 175)|) :
    η <
      |(ieeeDoubleKahanRationalFunction (kahanHornerGridPoint 289) -
          kahanRationalFunction (kahanHornerGridPoint 289)) -
        (ieeeDoubleKahanRationalFunction (kahanHornerGridPoint 175) -
          kahanRationalFunction (kahanHornerGridPoint 175))| := by
  exact
    kahanRoundedGrid_175_289_error_spread_gt_of_output_spread
      (fun j => ieeeDoubleKahanRationalFunction (kahanHornerGridPoint j))
      η hspread

end NumStability
