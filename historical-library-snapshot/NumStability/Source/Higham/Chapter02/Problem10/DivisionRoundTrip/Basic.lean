import NumStability.Source.Higham.Chapter02.Problem09.DoubleRounding.Counterexample.Results

/-!
# Chapter02 Problem10 DivisionRoundTrip Basic

Canonical destination for material split out of
`NumStability.Analysis.Problem2_10` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

namespace FloatingPointFormat

theorem problem2_10_ieeeDouble_two_pow_le_maxFiniteMagnitude
    {k : ℕ} (hk : k ≤ 1023) :
    (2 : ℝ) ^ k ≤ ieeeDoubleFormat.maxFiniteMagnitude := by
  rw [maxFiniteMagnitude, ieeeDoubleFormat, betaR]
  change (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (1024 : ℤ) *
    (1 - (2 : ℝ) ^ (-53 : ℤ))
  have hfactor : (1 / 2 : ℝ) ≤ 1 - (2 : ℝ) ^ (-53 : ℤ) := by
    rw [zpow_neg]
    have hden : (2 : ℝ) ≤ (2 : ℝ) ^ (53 : ℕ) := by
      exact le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (53 : ℕ) ≠ 0)
    have hinv : 1 / ((2 : ℝ) ^ (53 : ℕ)) ≤ 1 / (2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hden
    norm_num at hinv ⊢
  have hpow_k : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (1023 : ℕ) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
  have hhalf :
      (2 : ℝ) ^ (1023 : ℕ) =
        (2 : ℝ) ^ (1024 : ℤ) * (1 / 2 : ℝ) := by
    rw [show (1024 : ℤ) = ((1023 : ℕ) : ℤ) + 1 by norm_num]
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, zpow_one]
    field_simp
  calc
    (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (1023 : ℕ) := hpow_k
    _ = (2 : ℝ) ^ (1024 : ℤ) * (1 / 2 : ℝ) := hhalf
    _ ≤ (2 : ℝ) ^ (1024 : ℤ) * (1 - (2 : ℝ) ^ (-53 : ℤ)) :=
      mul_le_mul_of_nonneg_left hfactor
        (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) (1024 : ℤ)))

/-- The generic rounded lower approximation to `(2^k)/3`, multiplied exactly
by `3`, is the midpoint immediately below `2^k`. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_thirds_mul_three_midpoint
    {k : ℕ} :
    ((6004799503160661 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 54))) * 3 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 54)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 54)) * (2 : ℝ) ^ (54 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 54)) (54 : ℤ)
    have hexp : ((k : ℤ) - 54) + 54 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  rw [hpow]
  norm_num [zpow_natCast]
  ring

/-- The generic rounded lower approximation to `-(2^k)/3`, multiplied exactly
by `3`, is the midpoint immediately above `-2^k`. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_thirds_mul_three_midpoint
    {k : ℕ} :
    (-((6004799503160661 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 54)))) * 3 =
      -((2 : ℝ) ^ k) + (2 : ℝ) ^ (((k : ℤ) - 54)) := by
  rw [show
      (-((6004799503160661 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 54)))) * 3 =
        -(((6004799503160661 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 54))) * 3) by
    ring]
  rw [problem2_10_ieeeDouble_rounded_two_pow_thirds_mul_three_midpoint]
  ring

theorem problem2_10_displayed_denominator_eq_power_sum :
    (3 : ℕ) = 2 ^ (1 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_powerOfTwo_numerator_kahan_hypotheses
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (3 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨1, 0, problem2_10_displayed_denominator_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

theorem problem2_10_negative_powerOfTwo_numerator_kahan_hypotheses
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (3 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨1, 0, problem2_10_displayed_denominator_eq_power_sum⟩
  · simpa using
      (problem2_10_powerOfTwo_numerator_kahan_hypotheses (k := k) hk).2

/-- Integer-side denominator shape from Kahan's quoted theorem.  We use
integer exponents over `ℚ` so the source's first listed value `1` is represented
as `2^(-1) + 2^(-1)`. -/
def problem2_10_allowableDenominator (n : ℕ) : Prop :=
  ∃ i j : ℤ, (n : ℚ) = (2 : ℚ) ^ i + (2 : ℚ) ^ j

/-- Natural-exponent denominator sums are allowable in the rational-exponent
source model used for Problem 2.10. -/
theorem problem2_10_allowableDenominator_of_nat_power_sum
    {n i j : ℕ} (hn : n = 2 ^ i + 2 ^ j) :
    problem2_10_allowableDenominator n := by
  subst n
  exact ⟨(i : ℤ), (j : ℤ), by simp [zpow_natCast]⟩

/-- Every allowable denominator in Kahan's Problem 2.10 theorem is nonzero.
This discharges the nonzero-denominator side condition for the zero-numerator
branch directly from the source shape `n = 2^i + 2^j`. -/
theorem problem2_10_allowableDenominator_ne_zero
    {n : ℕ} (hn : problem2_10_allowableDenominator n) :
    n ≠ 0 := by
  rcases hn with ⟨i, j, hsum⟩
  intro hzero
  subst n
  have hpos :
      (0 : ℚ) < (2 : ℚ) ^ i + (2 : ℚ) ^ j :=
    add_pos (zpow_pos (by norm_num : (0 : ℚ) < 2) i)
      (zpow_pos (by norm_num : (0 : ℚ) < 2) j)
  norm_num at hsum
  linarith

/-- Source-shape integer hypotheses for Kahan's Problem 2.10 theorem, using
the repository's rational-exponent allowable-denominator predicate. -/
theorem problem2_10_kahan_integer_hypotheses_of_allowableDenominator
    {m : ℤ} {n : ℕ}
    (hn : problem2_10_allowableDenominator n)
    (hm : |m| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1)) :
    problem2_10_allowableDenominator n ∧
      |m| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
  ⟨hn, hm⟩

/-- Power-of-two numerator source hypotheses for arbitrary allowable
denominators.  This generalizes the earlier denominator-`3` integer-side
wrappers; the operation-level rounding trace remains the hard open part. -/
theorem problem2_10_powerOfTwo_numerator_kahan_hypotheses_of_allowableDenominator
    {n k : ℕ}
    (hn : problem2_10_allowableDenominator n)
    (hk : k < ieeeDoubleFormat.t - 1) :
    problem2_10_allowableDenominator n ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  refine problem2_10_kahan_integer_hypotheses_of_allowableDenominator
    (m := (2 : ℤ) ^ k) hn ?_
  have hpow :
      (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
    pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
  have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
  simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed power-of-two numerator source hypotheses for arbitrary allowable
denominators. -/
theorem problem2_10_negative_powerOfTwo_numerator_kahan_hypotheses_of_allowableDenominator
    {n k : ℕ}
    (hn : problem2_10_allowableDenominator n)
    (hk : k < ieeeDoubleFormat.t - 1) :
    problem2_10_allowableDenominator n ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  refine problem2_10_kahan_integer_hypotheses_of_allowableDenominator
    (m := -((2 : ℤ) ^ k)) hn ?_
  simpa using
    (problem2_10_powerOfTwo_numerator_kahan_hypotheses_of_allowableDenominator
      (n := n) (k := k) hn hk).2

/-- The displayed initial segment of allowable denominators in Problem 2.10. -/
def problem2_10_displayedAllowableDenominatorPrefix : List ℕ :=
  [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 17, 18, 20]

theorem problem2_10_displayedAllowableDenominatorPrefix_allowable
    {n : ℕ} (hn : n ∈ problem2_10_displayedAllowableDenominatorPrefix) :
    problem2_10_allowableDenominator n := by
  simp [problem2_10_displayedAllowableDenominatorPrefix] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨-1, -1, by norm_num [zpow_neg]⟩
  · exact ⟨0, 0, by norm_num⟩
  · exact ⟨1, 0, by norm_num⟩
  · exact ⟨1, 1, by norm_num⟩
  · exact ⟨2, 0, by norm_num⟩
  · exact ⟨2, 1, by norm_num⟩
  · exact ⟨2, 2, by norm_num⟩
  · exact ⟨3, 0, by norm_num⟩
  · exact ⟨3, 1, by norm_num⟩
  · exact ⟨3, 2, by norm_num⟩
  · exact ⟨3, 3, by norm_num⟩
  · exact ⟨4, 0, by norm_num⟩
  · exact ⟨4, 1, by norm_num⟩
  · exact ⟨4, 2, by norm_num⟩

/-- The next nontrivial allowable denominator after `3` in the displayed
Problem 2.10 prefix. -/
theorem problem2_10_denominator_five_eq_power_sum :
    (5 : ℕ) = 2 ^ (2 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_five_allowableDenominator :
    problem2_10_allowableDenominator 5 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_five_eq_power_sum

/-- The next displayed-prefix allowable denominator after `5`. -/
theorem problem2_10_denominator_six_eq_power_sum :
    (6 : ℕ) = 2 ^ (2 : ℕ) + 2 ^ (1 : ℕ) := by
  norm_num

theorem problem2_10_six_allowableDenominator :
    problem2_10_allowableDenominator 6 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_six_eq_power_sum

/-- The first displayed-prefix denominator after `8`. -/
theorem problem2_10_denominator_nine_eq_power_sum :
    (9 : ℕ) = 2 ^ (3 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_nine_allowableDenominator :
    problem2_10_allowableDenominator 9 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_nine_eq_power_sum

/-- The next displayed-prefix allowable denominator after `9`. -/
theorem problem2_10_denominator_ten_eq_power_sum :
    (10 : ℕ) = 2 ^ (3 : ℕ) + 2 ^ (1 : ℕ) := by
  norm_num

theorem problem2_10_ten_allowableDenominator :
    problem2_10_allowableDenominator 10 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_ten_eq_power_sum

/-- The displayed-prefix allowable denominator after `10`. -/
theorem problem2_10_denominator_twelve_eq_power_sum :
    (12 : ℕ) = 2 ^ (3 : ℕ) + 2 ^ (2 : ℕ) := by
  norm_num

theorem problem2_10_twelve_allowableDenominator :
    problem2_10_allowableDenominator 12 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_twelve_eq_power_sum

/-- The displayed-prefix allowable denominator after `16`. -/
theorem problem2_10_denominator_seventeen_eq_power_sum :
    (17 : ℕ) = 2 ^ (4 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_seventeen_allowableDenominator :
    problem2_10_allowableDenominator 17 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_seventeen_eq_power_sum

/-- The displayed-prefix allowable denominator after `17`. -/
theorem problem2_10_denominator_eighteen_eq_power_sum :
    (18 : ℕ) = 2 ^ (4 : ℕ) + 2 ^ (1 : ℕ) := by
  norm_num

theorem problem2_10_eighteen_allowableDenominator :
    problem2_10_allowableDenominator 18 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_eighteen_eq_power_sum

/-- The displayed-prefix allowable denominator `20`. -/
theorem problem2_10_denominator_twenty_eq_power_sum :
    (20 : ℕ) = 2 ^ (4 : ℕ) + 2 ^ (2 : ℕ) := by
  norm_num

theorem problem2_10_twenty_allowableDenominator :
    problem2_10_allowableDenominator 20 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_twenty_eq_power_sum

/-- The next odd allowable denominator after `17` used in the power-of-two
route. -/
theorem problem2_10_denominator_thirtythree_eq_power_sum :
    (33 : ℕ) = 2 ^ (5 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_thirtythree_allowableDenominator :
    problem2_10_allowableDenominator 33 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_thirtythree_eq_power_sum

/-- The next odd allowable denominator after `33` used in the power-of-two
route. -/
theorem problem2_10_denominator_sixtyfive_eq_power_sum :
    (65 : ℕ) = 2 ^ (6 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_sixtyfive_allowableDenominator :
    problem2_10_allowableDenominator 65 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_sixtyfive_eq_power_sum

/-- The next odd allowable denominator after `65` used in the power-of-two
route. -/
theorem problem2_10_denominator_onehundredtwentynine_eq_power_sum :
    (129 : ℕ) = 2 ^ (7 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_onehundredtwentynine_allowableDenominator :
    problem2_10_allowableDenominator 129 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_onehundredtwentynine_eq_power_sum

/-- The next odd allowable denominator after `129` used in the power-of-two
route. -/
theorem problem2_10_denominator_twohundredfiftyseven_eq_power_sum :
    (257 : ℕ) = 2 ^ (8 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_twohundredfiftyseven_allowableDenominator :
    problem2_10_allowableDenominator 257 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_twohundredfiftyseven_eq_power_sum

/-- The next odd allowable denominator after `257` used in the power-of-two
route. -/
theorem problem2_10_denominator_fivehundredthirteen_eq_power_sum :
    (513 : ℕ) = 2 ^ (9 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_fivehundredthirteen_allowableDenominator :
    problem2_10_allowableDenominator 513 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_fivehundredthirteen_eq_power_sum

/-- The next odd allowable denominator after `513` used in the power-of-two
route. -/
theorem problem2_10_denominator_onethousandtwentyfive_eq_power_sum :
    (1025 : ℕ) = 2 ^ (10 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_onethousandtwentyfive_allowableDenominator :
    problem2_10_allowableDenominator 1025 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_onethousandtwentyfive_eq_power_sum

/-- The next odd allowable denominator after `1025` used in the power-of-two
route. -/
theorem problem2_10_denominator_twothousandfortynine_eq_power_sum :
    (2049 : ℕ) = 2 ^ (11 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_twothousandfortynine_allowableDenominator :
    problem2_10_allowableDenominator 2049 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_twothousandfortynine_eq_power_sum

/-- The next odd allowable denominator after `2049` used in the power-of-two
route. -/
theorem problem2_10_denominator_fourthousandninetyseven_eq_power_sum :
    (4097 : ℕ) = 2 ^ (12 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_fourthousandninetyseven_allowableDenominator :
    problem2_10_allowableDenominator 4097 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_fourthousandninetyseven_eq_power_sum

/-- The next odd allowable denominator after `4097` used in the power-of-two
route. -/
theorem problem2_10_denominator_eightthousandonehundredninetythree_eq_power_sum :
    (8193 : ℕ) = 2 ^ (13 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_eightthousandonehundredninetythree_allowableDenominator :
    problem2_10_allowableDenominator 8193 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_eightthousandonehundredninetythree_eq_power_sum

/-- The next odd allowable denominator after `8193` used in the power-of-two
route. -/
theorem problem2_10_denominator_sixteenthousandthreehundredeightyfive_eq_power_sum :
    (16385 : ℕ) = 2 ^ (14 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_sixteenthousandthreehundredeightyfive_allowableDenominator :
    problem2_10_allowableDenominator 16385 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_sixteenthousandthreehundredeightyfive_eq_power_sum

/-- The next odd allowable denominator after `16385` used in the power-of-two
route. -/
theorem problem2_10_denominator_thirtytwothousandsevenhundredsixtynine_eq_power_sum :
    (32769 : ℕ) = 2 ^ (15 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_thirtytwothousandsevenhundredsixtynine_allowableDenominator :
    problem2_10_allowableDenominator 32769 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_thirtytwothousandsevenhundredsixtynine_eq_power_sum

/-- The next odd allowable denominator after `32769` used in the power-of-two
route. -/
theorem problem2_10_denominator_sixtyfivethousandfivehundredthirtyseven_eq_power_sum :
    (65537 : ℕ) = 2 ^ (16 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_sixtyfivethousandfivehundredthirtyseven_allowableDenominator :
    problem2_10_allowableDenominator 65537 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_sixtyfivethousandfivehundredthirtyseven_eq_power_sum

/-- The next odd allowable denominator after `65537` used in the power-of-two
route. -/
theorem problem2_10_denominator_onehundredthirtyonethousandseventythree_eq_power_sum :
    (131073 : ℕ) = 2 ^ (17 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_onehundredthirtyonethousandseventythree_allowableDenominator :
    problem2_10_allowableDenominator 131073 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_onehundredthirtyonethousandseventythree_eq_power_sum

/-- The next odd allowable denominator after `131073` used in the power-of-two
route. -/
theorem problem2_10_denominator_twohundredsixtytwothousandonehundredfortyfive_eq_power_sum :
    (262145 : ℕ) = 2 ^ (18 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_twohundredsixtytwothousandonehundredfortyfive_allowableDenominator :
    problem2_10_allowableDenominator 262145 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_twohundredsixtytwothousandonehundredfortyfive_eq_power_sum

/-- The next odd allowable denominator after `262145` used in the power-of-two
route. -/
theorem problem2_10_denominator_fivehundredtwentyfourthousandtwohundredeightynine_eq_power_sum :
    (524289 : ℕ) = 2 ^ (19 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_fivehundredtwentyfourthousandtwohundredeightynine_allowableDenominator :
    problem2_10_allowableDenominator 524289 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_fivehundredtwentyfourthousandtwohundredeightynine_eq_power_sum

/-- The next odd allowable denominator after `524289` used in the power-of-two
route. -/
theorem problem2_10_denominator_onemillionfortyeightthousandfivehundredseventyseven_eq_power_sum :
    (1048577 : ℕ) = 2 ^ (20 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_onemillionfortyeightthousandfivehundredseventyseven_allowableDenominator :
    problem2_10_allowableDenominator 1048577 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_onemillionfortyeightthousandfivehundredseventyseven_eq_power_sum

/-- The next odd allowable denominator after `1048577` used in the
power-of-two route. -/
theorem problem2_10_denominator_twomillionninetyseventhousandonehundredfiftythree_eq_power_sum :
    (2097153 : ℕ) = 2 ^ (21 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_twomillionninetyseventhousandonehundredfiftythree_allowableDenominator :
    problem2_10_allowableDenominator 2097153 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_twomillionninetyseventhousandonehundredfiftythree_eq_power_sum

/-- The next odd allowable denominator after `2097153` used in the
power-of-two route. -/
theorem problem2_10_denominator_fourmilliononehundredninetyfourthousandthreehundredfive_eq_power_sum :
    (4194305 : ℕ) = 2 ^ (22 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_fourmilliononehundredninetyfourthousandthreehundredfive_allowableDenominator :
    problem2_10_allowableDenominator 4194305 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_fourmilliononehundredninetyfourthousandthreehundredfive_eq_power_sum

/-- The next odd allowable denominator after `4194305` used in the
power-of-two route. -/
theorem problem2_10_denominator_eightmillionthreehundredeightyeightthousandsixhundrednine_eq_power_sum :
    (8388609 : ℕ) = 2 ^ (23 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_eightmillionthreehundredeightyeightthousandsixhundrednine_allowableDenominator :
    problem2_10_allowableDenominator 8388609 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_eightmillionthreehundredeightyeightthousandsixhundrednine_eq_power_sum

/-- The next odd allowable denominator after `8388609` used in the
power-of-two route. -/
theorem problem2_10_denominator_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeen_eq_power_sum :
    (16777217 : ℕ) = 2 ^ (24 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeen_allowableDenominator :
    problem2_10_allowableDenominator 16777217 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeen_eq_power_sum

/-- The next odd allowable denominator after `16777217` used in the
power-of-two route. -/
theorem problem2_10_denominator_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythree_eq_power_sum :
    (33554433 : ℕ) = 2 ^ (25 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythree_allowableDenominator :
    problem2_10_allowableDenominator 33554433 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythree_eq_power_sum

/-- The next odd allowable denominator after `33554433` used in the
power-of-two route. -/
theorem problem2_10_denominator_sixtysevenmilliononehundredeightthousandeighthundredsixtyfive_eq_power_sum :
    (67108865 : ℕ) = 2 ^ (26 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_sixtysevenmilliononehundredeightthousandeighthundredsixtyfive_allowableDenominator :
    problem2_10_allowableDenominator 67108865 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_sixtysevenmilliononehundredeightthousandeighthundredsixtyfive_eq_power_sum

/-- The next odd allowable denominator after `67108865` used in the
power-of-two route. -/
theorem problem2_10_denominator_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentynine_eq_power_sum :
    (134217729 : ℕ) = 2 ^ (27 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentynine_allowableDenominator :
    problem2_10_allowableDenominator 134217729 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentynine_eq_power_sum

/-- The next odd allowable denominator after `134217729` used in the
power-of-two route. -/
theorem problem2_10_denominator_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftyseven_eq_power_sum :
    (268435457 : ℕ) = 2 ^ (28 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftyseven_allowableDenominator :
    problem2_10_allowableDenominator 268435457 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftyseven_eq_power_sum

/-- The next odd allowable denominator after `268435457` used in the
power-of-two route. -/
theorem problem2_10_denominator_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteen_eq_power_sum :
    (536870913 : ℕ) = 2 ^ (29 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteen_allowableDenominator :
    problem2_10_allowableDenominator 536870913 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteen_eq_power_sum

/-- The next odd allowable denominator after `536870913` used in the
power-of-two route. -/
theorem problem2_10_denominator_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfive_eq_power_sum :
    (1073741825 : ℕ) = 2 ^ (30 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfive_allowableDenominator :
    problem2_10_allowableDenominator 1073741825 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfive_eq_power_sum

/-- The next odd allowable denominator after `1073741825` used in the
power-of-two route. -/
theorem problem2_10_denominator_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortynine_eq_power_sum :
    (2147483649 : ℕ) = 2 ^ (31 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortynine_allowableDenominator :
    problem2_10_allowableDenominator 2147483649 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortynine_eq_power_sum

/-- The next odd allowable denominator after `2147483649` used in the
power-of-two route. -/
theorem problem2_10_denominator_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetyseven_eq_power_sum :
    (4294967297 : ℕ) = 2 ^ (32 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetyseven_allowableDenominator :
    problem2_10_allowableDenominator 4294967297 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetyseven_eq_power_sum

/-- The next odd allowable denominator after `4294967297` used in the
power-of-two route. -/
theorem problem2_10_denominator_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythree_eq_power_sum :
    (8589934593 : ℕ) = 2 ^ (33 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythree_allowableDenominator :
    problem2_10_allowableDenominator 8589934593 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythree_eq_power_sum

/-- The next odd allowable denominator after `8589934593` used in the
power-of-two route. -/
theorem problem2_10_denominator_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfive_eq_power_sum :
    (17179869185 : ℕ) = 2 ^ (34 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfive_allowableDenominator :
    problem2_10_allowableDenominator 17179869185 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfive_eq_power_sum

/-- The next odd allowable denominator after `17179869185` used in the
power-of-two route. -/
theorem problem2_10_denominator_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtynine_eq_power_sum :
    (34359738369 : ℕ) = 2 ^ (35 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtynine_allowableDenominator :
    problem2_10_allowableDenominator 34359738369 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtynine_eq_power_sum

/-- The next odd allowable denominator after `34359738369` used in the
power-of-two route. -/
theorem problem2_10_denominator_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtyseven_eq_power_sum :
    (68719476737 : ℕ) = 2 ^ (36 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtyseven_allowableDenominator :
    problem2_10_allowableDenominator 68719476737 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtyseven_eq_power_sum

/-- The next odd allowable denominator after `68719476737` used in the
power-of-two route. -/
theorem problem2_10_denominator_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythree_eq_power_sum :
    (137438953473 : ℕ) = 2 ^ (37 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythree_allowableDenominator :
    problem2_10_allowableDenominator 137438953473 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythree_eq_power_sum

/-- The next odd allowable denominator after `137438953473` used in the
power-of-two route. -/
theorem problem2_10_denominator_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfive_eq_power_sum :
    (274877906945 : ℕ) = 2 ^ (38 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfive_allowableDenominator :
    problem2_10_allowableDenominator 274877906945 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfive_eq_power_sum

/-- The next odd allowable denominator after `274877906945` used in the
power-of-two route. -/
theorem problem2_10_denominator_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightynine_eq_power_sum :
    (549755813889 : ℕ) = 2 ^ (39 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightynine_allowableDenominator :
    problem2_10_allowableDenominator 549755813889 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightynine_eq_power_sum

/-- The next odd allowable denominator after `549755813889` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_forty_plus_one_eq_power_sum :
    (1099511627777 : ℕ) = 2 ^ (40 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_forty_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 1099511627777 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_forty_plus_one_eq_power_sum

/-- The next odd allowable denominator after `1099511627777` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_forty_one_plus_one_eq_power_sum :
    (2199023255553 : ℕ) = 2 ^ (41 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_forty_one_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 2199023255553 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_forty_one_plus_one_eq_power_sum

/-- The next odd allowable denominator after `2199023255553` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_forty_two_plus_one_eq_power_sum :
    (4398046511105 : ℕ) = 2 ^ (42 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_forty_two_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 4398046511105 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_forty_two_plus_one_eq_power_sum

/-- The next odd allowable denominator after `4398046511105` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_forty_three_plus_one_eq_power_sum :
    (8796093022209 : ℕ) = 2 ^ (43 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_forty_three_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 8796093022209 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_forty_three_plus_one_eq_power_sum

/-- The next odd allowable denominator after `8796093022209` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_forty_four_plus_one_eq_power_sum :
    (17592186044417 : ℕ) = 2 ^ (44 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_forty_four_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 17592186044417 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_forty_four_plus_one_eq_power_sum

/-- The next odd allowable denominator after `17592186044417` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_forty_five_plus_one_eq_power_sum :
    (35184372088833 : ℕ) = 2 ^ (45 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_forty_five_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 35184372088833 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_forty_five_plus_one_eq_power_sum

/-- The next odd allowable denominator after `35184372088833` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_forty_six_plus_one_eq_power_sum :
    (70368744177665 : ℕ) = 2 ^ (46 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_forty_six_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 70368744177665 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_forty_six_plus_one_eq_power_sum

/-- The next odd allowable denominator after `70368744177665` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_forty_seven_plus_one_eq_power_sum :
    (140737488355329 : ℕ) = 2 ^ (47 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_forty_seven_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 140737488355329 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_forty_seven_plus_one_eq_power_sum

/-- The next odd allowable denominator after `140737488355329` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_forty_eight_plus_one_eq_power_sum :
    (281474976710657 : ℕ) = 2 ^ (48 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_forty_eight_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 281474976710657 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_forty_eight_plus_one_eq_power_sum

/-- The next odd allowable denominator after `281474976710657` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_forty_nine_plus_one_eq_power_sum :
    (562949953421313 : ℕ) = 2 ^ (49 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_forty_nine_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 562949953421313 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_forty_nine_plus_one_eq_power_sum

/-- The next odd allowable denominator after `562949953421313` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_fifty_plus_one_eq_power_sum :
    (1125899906842625 : ℕ) = 2 ^ (50 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_fifty_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 1125899906842625 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_fifty_plus_one_eq_power_sum

/-- The next odd allowable denominator after `1125899906842625` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_fifty_one_plus_one_eq_power_sum :
    (2251799813685249 : ℕ) = 2 ^ (51 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_fifty_one_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 2251799813685249 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_fifty_one_plus_one_eq_power_sum

/-- The next odd allowable denominator after `2251799813685249` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_fifty_two_plus_one_eq_power_sum :
    (4503599627370497 : ℕ) = 2 ^ (52 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_fifty_two_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 4503599627370497 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_fifty_two_plus_one_eq_power_sum

/-- The next odd allowable denominator after `4503599627370497` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_fifty_three_plus_one_eq_power_sum :
    (9007199254740993 : ℕ) = 2 ^ (53 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_fifty_three_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 9007199254740993 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_fifty_three_plus_one_eq_power_sum

/-- The next odd allowable denominator after `9007199254740993` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_fifty_four_plus_one_eq_power_sum :
    (18014398509481985 : ℕ) = 2 ^ (54 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_fifty_four_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 18014398509481985 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_fifty_four_plus_one_eq_power_sum

/-- The next odd allowable denominator after `18014398509481985` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_fifty_five_plus_one_eq_power_sum :
    (36028797018963969 : ℕ) = 2 ^ (55 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_fifty_five_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 36028797018963969 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_fifty_five_plus_one_eq_power_sum

/-- The next odd allowable denominator after `36028797018963969` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_fifty_six_plus_one_eq_power_sum :
    (72057594037927937 : ℕ) = 2 ^ (56 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_fifty_six_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 72057594037927937 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_fifty_six_plus_one_eq_power_sum

/-- The next odd allowable denominator after `72057594037927937` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_fifty_seven_plus_one_eq_power_sum :
    (144115188075855873 : ℕ) = 2 ^ (57 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_fifty_seven_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 144115188075855873 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_fifty_seven_plus_one_eq_power_sum

/-- The next odd allowable denominator after `144115188075855873` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_fifty_eight_plus_one_eq_power_sum :
    (288230376151711745 : ℕ) = 2 ^ (58 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_fifty_eight_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 288230376151711745 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_fifty_eight_plus_one_eq_power_sum

/-- The next odd allowable denominator after `288230376151711745` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_fifty_nine_plus_one_eq_power_sum :
    (576460752303423489 : ℕ) = 2 ^ (59 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_fifty_nine_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 576460752303423489 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_fifty_nine_plus_one_eq_power_sum

/-- The next odd allowable denominator after `576460752303423489` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_sixty_plus_one_eq_power_sum :
    (1152921504606846977 : ℕ) = 2 ^ (60 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_sixty_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 1152921504606846977 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_sixty_plus_one_eq_power_sum

/-- The next odd allowable denominator after `1152921504606846977` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_sixty_one_plus_one_eq_power_sum :
    (2305843009213693953 : ℕ) = 2 ^ (61 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_sixty_one_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 2305843009213693953 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_sixty_one_plus_one_eq_power_sum

/-- The next odd allowable denominator after `2305843009213693953` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_sixty_two_plus_one_eq_power_sum :
    (4611686018427387905 : ℕ) = 2 ^ (62 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_sixty_two_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 4611686018427387905 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_sixty_two_plus_one_eq_power_sum

/-- The next odd allowable denominator after `4611686018427387905` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_sixty_three_plus_one_eq_power_sum :
    (9223372036854775809 : ℕ) = 2 ^ (63 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_sixty_three_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 9223372036854775809 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_sixty_three_plus_one_eq_power_sum

/-- The next odd allowable denominator after `9223372036854775809` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_sixty_four_plus_one_eq_power_sum :
    (18446744073709551617 : ℕ) = 2 ^ (64 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_sixty_four_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 18446744073709551617 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_sixty_four_plus_one_eq_power_sum

/-- The next odd allowable denominator after `18446744073709551617` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_sixty_five_plus_one_eq_power_sum :
    (36893488147419103233 : ℕ) = 2 ^ (65 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_sixty_five_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 36893488147419103233 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_sixty_five_plus_one_eq_power_sum

/-- The next odd allowable denominator after `36893488147419103233` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_sixty_six_plus_one_eq_power_sum :
    (73786976294838206465 : ℕ) = 2 ^ (66 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_sixty_six_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 73786976294838206465 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_sixty_six_plus_one_eq_power_sum

/-- The next odd allowable denominator after `73786976294838206465` used in the
power-of-two route. -/
theorem problem2_10_denominator_two_pow_sixty_seven_plus_one_eq_power_sum :
    (147573952589676412929 : ℕ) = 2 ^ (67 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_sixty_seven_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 147573952589676412929 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_sixty_seven_plus_one_eq_power_sum

/-- The next odd allowable denominator after `147573952589676412929` used in
the power-of-two route. -/
theorem problem2_10_denominator_two_pow_sixty_eight_plus_one_eq_power_sum :
    (295147905179352825857 : ℕ) = 2 ^ (68 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_sixty_eight_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 295147905179352825857 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_sixty_eight_plus_one_eq_power_sum

/-- The next odd allowable denominator after `295147905179352825857` used in
the power-of-two route. -/
theorem problem2_10_denominator_two_pow_sixty_nine_plus_one_eq_power_sum :
    (590295810358705651713 : ℕ) = 2 ^ (69 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_sixty_nine_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 590295810358705651713 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_sixty_nine_plus_one_eq_power_sum

/-- The next odd allowable denominator after `590295810358705651713` used in
the power-of-two route. -/
theorem problem2_10_denominator_two_pow_seventy_plus_one_eq_power_sum :
    (1180591620717411303425 : ℕ) = 2 ^ (70 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_seventy_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 1180591620717411303425 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_seventy_plus_one_eq_power_sum

/-- The next odd allowable denominator after `1180591620717411303425` used in
the power-of-two route. -/
theorem problem2_10_denominator_two_pow_seventy_one_plus_one_eq_power_sum :
    (2361183241434822606849 : ℕ) = 2 ^ (71 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_seventy_one_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 2361183241434822606849 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_seventy_one_plus_one_eq_power_sum

/-- The next odd allowable denominator after `2361183241434822606849` used in
the power-of-two route. -/
theorem problem2_10_denominator_two_pow_seventy_two_plus_one_eq_power_sum :
    (4722366482869645213697 : ℕ) = 2 ^ (72 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_seventy_two_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 4722366482869645213697 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_seventy_two_plus_one_eq_power_sum

/-- The next odd allowable denominator after `4722366482869645213697` used in
the power-of-two route. -/
theorem problem2_10_denominator_two_pow_seventy_three_plus_one_eq_power_sum :
    (9444732965739290427393 : ℕ) = 2 ^ (73 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_seventy_three_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 9444732965739290427393 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_seventy_three_plus_one_eq_power_sum

/-- The next odd allowable denominator after `9444732965739290427393` used in
the power-of-two route. -/
theorem problem2_10_denominator_two_pow_seventy_four_plus_one_eq_power_sum :
    (18889465931478580854785 : ℕ) = 2 ^ (74 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_seventy_four_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 18889465931478580854785 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_seventy_four_plus_one_eq_power_sum

/-- The next odd allowable denominator after `18889465931478580854785` used in
the power-of-two route. -/
theorem problem2_10_denominator_two_pow_seventy_five_plus_one_eq_power_sum :
    (37778931862957161709569 : ℕ) = 2 ^ (75 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_seventy_five_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 37778931862957161709569 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_seventy_five_plus_one_eq_power_sum

/-- The next odd allowable denominator after `37778931862957161709569` used in
the power-of-two route. -/
theorem problem2_10_denominator_two_pow_seventy_six_plus_one_eq_power_sum :
    (75557863725914323419137 : ℕ) = 2 ^ (76 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_seventy_six_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 75557863725914323419137 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_seventy_six_plus_one_eq_power_sum

/-- The next odd allowable denominator after `75557863725914323419137` used in
the power-of-two route. -/
theorem problem2_10_denominator_two_pow_seventy_seven_plus_one_eq_power_sum :
    (151115727451828646838273 : ℕ) = 2 ^ (77 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_seventy_seven_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 151115727451828646838273 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_seventy_seven_plus_one_eq_power_sum

/-- The next odd allowable denominator after `151115727451828646838273` used in
the power-of-two route. -/
theorem problem2_10_denominator_two_pow_seventy_eight_plus_one_eq_power_sum :
    (302231454903657293676545 : ℕ) = 2 ^ (78 : ℕ) + 2 ^ (0 : ℕ) := by
  norm_num

theorem problem2_10_two_pow_seventy_eight_plus_one_allowableDenominator :
    problem2_10_allowableDenominator 302231454903657293676545 :=
  problem2_10_allowableDenominator_of_nat_power_sum
    problem2_10_denominator_two_pow_seventy_eight_plus_one_eq_power_sum

/-- The first denominator-`6` numerator pair `m = 1`, `n = 6` satisfies
the integer-side hypotheses in Kahan's quoted theorem. -/
theorem problem2_10_one_sixth_kahan_hypotheses :
    (∃ i j : ℕ, (6 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(1 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨2, 1, problem2_10_denominator_six_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- The signed companion `m = -1`, `n = 6` satisfies the integer-side
hypotheses in Kahan's quoted theorem. -/
theorem problem2_10_negative_one_sixth_kahan_hypotheses :
    (∃ i j : ℕ, (6 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-1 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨2, 1, problem2_10_denominator_six_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- The first denominator-`10` numerator pair `m = 1`, `n = 10` satisfies
the integer-side hypotheses in Kahan's quoted theorem. -/
theorem problem2_10_one_tenth_kahan_hypotheses :
    (∃ i j : ℕ, (10 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(1 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨3, 1, problem2_10_denominator_ten_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- The signed companion `m = -1`, `n = 10` satisfies the integer-side
hypotheses in Kahan's quoted theorem. -/
theorem problem2_10_negative_one_tenth_kahan_hypotheses :
    (∃ i j : ℕ, (10 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-1 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨3, 1, problem2_10_denominator_ten_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- Source-side integer hypotheses for the denominator-`10` shifted
power-of-two numerator family `m = 2^(k+1)`. -/
theorem problem2_10_two_pow_succ_numerator_kahan_hypotheses_of_ten
    {k : ℕ} (hk : k + 2 < ieeeDoubleFormat.t) :
    (∃ i j : ℕ, (10 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ (k + 1))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨3, 1, problem2_10_denominator_ten_eq_power_sum⟩
  · have hlt_exp : k + 1 < ieeeDoubleFormat.t - 1 := by omega
    have hpow :
        (2 : ℤ) ^ (k + 1) < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hlt_exp
    have hnonneg : 0 ≤ (2 : ℤ) ^ (k + 1) := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^(k+1)`, `n = 10`. -/
theorem problem2_10_negative_two_pow_succ_numerator_kahan_hypotheses_of_ten
    {k : ℕ} (hk : k + 2 < ieeeDoubleFormat.t) :
    (∃ i j : ℕ, (10 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ (k + 1)))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨3, 1, problem2_10_denominator_ten_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_succ_numerator_kahan_hypotheses_of_ten
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`12` shifted
power-of-two numerator family `m = 2^(k+2)`. -/
theorem problem2_10_two_pow_add_two_numerator_kahan_hypotheses_of_twelve
    {k : ℕ} (hk : k + 3 < ieeeDoubleFormat.t) :
    (∃ i j : ℕ, (12 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ (k + 2))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨3, 2, problem2_10_denominator_twelve_eq_power_sum⟩
  · have hlt_exp : k + 2 < ieeeDoubleFormat.t - 1 := by omega
    have hpow :
        (2 : ℤ) ^ (k + 2) < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hlt_exp
    have hnonneg : 0 ≤ (2 : ℤ) ^ (k + 2) := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^(k+2)`, `n = 12`. -/
theorem problem2_10_negative_two_pow_add_two_numerator_kahan_hypotheses_of_twelve
    {k : ℕ} (hk : k + 3 < ieeeDoubleFormat.t) :
    (∃ i j : ℕ, (12 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ (k + 2)))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨3, 2, problem2_10_denominator_twelve_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_add_two_numerator_kahan_hypotheses_of_twelve
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`20` shifted
power-of-two numerator family `m = 2^(k+2)`. -/
theorem problem2_10_two_pow_add_two_numerator_kahan_hypotheses_of_twenty
    {k : ℕ} (hk : k + 3 < ieeeDoubleFormat.t) :
    (∃ i j : ℕ, (20 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ (k + 2))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨4, 2, problem2_10_denominator_twenty_eq_power_sum⟩
  · have hlt_exp : k + 2 < ieeeDoubleFormat.t - 1 := by omega
    have hpow :
        (2 : ℤ) ^ (k + 2) < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hlt_exp
    have hnonneg : 0 ≤ (2 : ℤ) ^ (k + 2) := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^(k+2)`, `n = 20`. -/
theorem problem2_10_negative_two_pow_add_two_numerator_kahan_hypotheses_of_twenty
    {k : ℕ} (hk : k + 3 < ieeeDoubleFormat.t) :
    (∃ i j : ℕ, (20 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ (k + 2)))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨4, 2, problem2_10_denominator_twenty_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_add_two_numerator_kahan_hypotheses_of_twenty
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`9` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_nine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (9 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨3, 0, problem2_10_denominator_nine_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 9`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_nine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (9 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨3, 0, problem2_10_denominator_nine_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_nine
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`17` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_seventeen
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (17 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨4, 0, problem2_10_denominator_seventeen_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 17`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_seventeen
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (17 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨4, 0, problem2_10_denominator_seventeen_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_seventeen
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`33` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_thirtythree
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (33 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨5, 0, problem2_10_denominator_thirtythree_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 33`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_thirtythree
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (33 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨5, 0, problem2_10_denominator_thirtythree_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_thirtythree
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`65` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_sixtyfive
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (65 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨6, 0, problem2_10_denominator_sixtyfive_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 65`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_sixtyfive
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (65 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨6, 0, problem2_10_denominator_sixtyfive_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_sixtyfive
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`129` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_onehundredtwentynine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (129 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨7, 0, problem2_10_denominator_onehundredtwentynine_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 129`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onehundredtwentynine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (129 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨7, 0, problem2_10_denominator_onehundredtwentynine_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_onehundredtwentynine
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`257` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_twohundredfiftyseven
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (257 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨8, 0, problem2_10_denominator_twohundredfiftyseven_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 257`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twohundredfiftyseven
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (257 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨8, 0, problem2_10_denominator_twohundredfiftyseven_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_twohundredfiftyseven
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`513` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_fivehundredthirteen
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (513 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨9, 0, problem2_10_denominator_fivehundredthirteen_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 513`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fivehundredthirteen
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (513 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨9, 0, problem2_10_denominator_fivehundredthirteen_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_fivehundredthirteen
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`1025` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_onethousandtwentyfive
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (1025 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨10, 0, problem2_10_denominator_onethousandtwentyfive_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 1025`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onethousandtwentyfive
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (1025 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨10, 0, problem2_10_denominator_onethousandtwentyfive_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_onethousandtwentyfive
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`2049` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_twothousandfortynine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (2049 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨11, 0, problem2_10_denominator_twothousandfortynine_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 2049`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twothousandfortynine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (2049 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨11, 0, problem2_10_denominator_twothousandfortynine_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_twothousandfortynine
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`4097` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_fourthousandninetyseven
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (4097 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨12, 0, problem2_10_denominator_fourthousandninetyseven_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 4097`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fourthousandninetyseven
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (4097 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨12, 0, problem2_10_denominator_fourthousandninetyseven_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_fourthousandninetyseven
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`8193` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_eightthousandonehundredninetythree
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (8193 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨13, 0, problem2_10_denominator_eightthousandonehundredninetythree_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 8193`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_eightthousandonehundredninetythree
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (8193 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨13, 0, problem2_10_denominator_eightthousandonehundredninetythree_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_eightthousandonehundredninetythree
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`16385` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_sixteenthousandthreehundredeightyfive
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (16385 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨14, 0, problem2_10_denominator_sixteenthousandthreehundredeightyfive_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 16385`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_sixteenthousandthreehundredeightyfive
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (16385 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨14, 0, problem2_10_denominator_sixteenthousandthreehundredeightyfive_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_sixteenthousandthreehundredeightyfive
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`32769` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_thirtytwothousandsevenhundredsixtynine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (32769 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨15, 0, problem2_10_denominator_thirtytwothousandsevenhundredsixtynine_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 32769`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_thirtytwothousandsevenhundredsixtynine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (32769 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨15, 0, problem2_10_denominator_thirtytwothousandsevenhundredsixtynine_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_thirtytwothousandsevenhundredsixtynine
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`65537` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_sixtyfivethousandfivehundredthirtyseven
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (65537 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨16, 0, problem2_10_denominator_sixtyfivethousandfivehundredthirtyseven_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 65537`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_sixtyfivethousandfivehundredthirtyseven
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (65537 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨16, 0, problem2_10_denominator_sixtyfivethousandfivehundredthirtyseven_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_sixtyfivethousandfivehundredthirtyseven
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`131073` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_onehundredthirtyonethousandseventythree
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (131073 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨17, 0, problem2_10_denominator_onehundredthirtyonethousandseventythree_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 131073`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onehundredthirtyonethousandseventythree
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (131073 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨17, 0, problem2_10_denominator_onehundredthirtyonethousandseventythree_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_onehundredthirtyonethousandseventythree
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`262145` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_twohundredsixtytwothousandonehundredfortyfive
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (262145 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨18, 0, problem2_10_denominator_twohundredsixtytwothousandonehundredfortyfive_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 262145`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twohundredsixtytwothousandonehundredfortyfive
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (262145 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨18, 0, problem2_10_denominator_twohundredsixtytwothousandonehundredfortyfive_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_twohundredsixtytwothousandonehundredfortyfive
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`524289` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_fivehundredtwentyfourthousandtwohundredeightynine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (524289 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨19, 0, problem2_10_denominator_fivehundredtwentyfourthousandtwohundredeightynine_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 524289`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fivehundredtwentyfourthousandtwohundredeightynine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (524289 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨19, 0, problem2_10_denominator_fivehundredtwentyfourthousandtwohundredeightynine_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_fivehundredtwentyfourthousandtwohundredeightynine
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`1048577` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_onemillionfortyeightthousandfivehundredseventyseven
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (1048577 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨20, 0, problem2_10_denominator_onemillionfortyeightthousandfivehundredseventyseven_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 1048577`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onemillionfortyeightthousandfivehundredseventyseven
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (1048577 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨20, 0, problem2_10_denominator_onemillionfortyeightthousandfivehundredseventyseven_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_onemillionfortyeightthousandfivehundredseventyseven
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`2097153` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_twomillionninetyseventhousandonehundredfiftythree
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (2097153 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨21, 0, problem2_10_denominator_twomillionninetyseventhousandonehundredfiftythree_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 2097153`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twomillionninetyseventhousandonehundredfiftythree
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (2097153 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨21, 0, problem2_10_denominator_twomillionninetyseventhousandonehundredfiftythree_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_twomillionninetyseventhousandonehundredfiftythree
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`4194305` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_fourmilliononehundredninetyfourthousandthreehundredfive
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (4194305 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨22, 0, problem2_10_denominator_fourmilliononehundredninetyfourthousandthreehundredfive_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 4194305`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fourmilliononehundredninetyfourthousandthreehundredfive
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (4194305 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨22, 0, problem2_10_denominator_fourmilliononehundredninetyfourthousandthreehundredfive_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_fourmilliononehundredninetyfourthousandthreehundredfive
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`8388609` power-of-two
numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_eightmillionthreehundredeightyeightthousandsixhundrednine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (8388609 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨23, 0, problem2_10_denominator_eightmillionthreehundredeightyeightthousandsixhundrednine_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 8388609`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_eightmillionthreehundredeightyeightthousandsixhundrednine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (8388609 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨23, 0, problem2_10_denominator_eightmillionthreehundredeightyeightthousandsixhundrednine_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_eightmillionthreehundredeightyeightthousandsixhundrednine
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`16777217`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeen
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (16777217 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨24, 0, problem2_10_denominator_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeen_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 16777217`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeen
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (16777217 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨24, 0, problem2_10_denominator_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeen_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeen
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`33554433`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythree
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (33554433 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨25, 0, problem2_10_denominator_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythree_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 33554433`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythree
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (33554433 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨25, 0, problem2_10_denominator_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythree_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythree
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`67108865`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_sixtysevenmilliononehundredeightthousandeighthundredsixtyfive
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (67108865 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨26, 0, problem2_10_denominator_sixtysevenmilliononehundredeightthousandeighthundredsixtyfive_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 67108865`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_sixtysevenmilliononehundredeightthousandeighthundredsixtyfive
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (67108865 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨26, 0, problem2_10_denominator_sixtysevenmilliononehundredeightthousandeighthundredsixtyfive_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_sixtysevenmilliononehundredeightthousandeighthundredsixtyfive
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`134217729`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentynine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (134217729 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨27, 0,
      problem2_10_denominator_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentynine_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 134217729`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentynine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (134217729 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨27, 0,
      problem2_10_denominator_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentynine_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentynine
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`268435457`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftyseven
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (268435457 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨28, 0,
      problem2_10_denominator_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftyseven_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 268435457`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftyseven
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (268435457 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨28, 0,
      problem2_10_denominator_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftyseven_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftyseven
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`536870913`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteen
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (536870913 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨29, 0,
      problem2_10_denominator_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteen_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 536870913`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteen
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (536870913 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨29, 0,
      problem2_10_denominator_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteen_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteen
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`1073741825`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfive
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (1073741825 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨30, 0,
      problem2_10_denominator_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfive_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 1073741825`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfive
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (1073741825 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨30, 0,
      problem2_10_denominator_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfive_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfive
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`2147483649`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortynine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (2147483649 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨31, 0,
      problem2_10_denominator_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortynine_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 2147483649`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortynine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (2147483649 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨31, 0,
      problem2_10_denominator_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortynine_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortynine
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`4294967297`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetyseven
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (4294967297 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨32, 0,
      problem2_10_denominator_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetyseven_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 4294967297`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetyseven
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (4294967297 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨32, 0,
      problem2_10_denominator_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetyseven_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetyseven
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`8589934593`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythree
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (8589934593 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨33, 0,
      problem2_10_denominator_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythree_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 8589934593`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythree
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (8589934593 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨33, 0,
      problem2_10_denominator_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythree_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythree
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`17179869185`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfive
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (17179869185 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨34, 0,
      problem2_10_denominator_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfive_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 17179869185`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfive
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (17179869185 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨34, 0,
      problem2_10_denominator_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfive_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfive
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`34359738369`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtynine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (34359738369 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨35, 0,
      problem2_10_denominator_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtynine_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 34359738369`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtynine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (34359738369 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨35, 0,
      problem2_10_denominator_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtynine_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtynine
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`68719476737`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtyseven
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (68719476737 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨36, 0,
      problem2_10_denominator_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtyseven_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 68719476737`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtyseven
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (68719476737 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨36, 0,
      problem2_10_denominator_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtyseven_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtyseven
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`137438953473`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythree
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (137438953473 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨37, 0,
      problem2_10_denominator_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythree_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 137438953473`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythree
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (137438953473 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨37, 0,
      problem2_10_denominator_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythree_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythree
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`274877906945`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfive
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (274877906945 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨38, 0,
      problem2_10_denominator_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfive_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 274877906945`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfive
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (274877906945 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨38, 0,
      problem2_10_denominator_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfive_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfive
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`549755813889`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightynine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (549755813889 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨39, 0,
      problem2_10_denominator_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightynine_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 549755813889`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightynine
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (549755813889 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨39, 0,
      problem2_10_denominator_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightynine_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightynine
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`1099511627777`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (1099511627777 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨40, 0,
      problem2_10_denominator_two_pow_forty_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 1099511627777`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (1099511627777 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨40, 0,
      problem2_10_denominator_two_pow_forty_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`2199023255553`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_one_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (2199023255553 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨41, 0,
      problem2_10_denominator_two_pow_forty_one_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 2199023255553`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_one_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (2199023255553 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨41, 0,
      problem2_10_denominator_two_pow_forty_one_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_one_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`4398046511105`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_two_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (4398046511105 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨42, 0,
      problem2_10_denominator_two_pow_forty_two_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 4398046511105`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_two_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (4398046511105 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨42, 0,
      problem2_10_denominator_two_pow_forty_two_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_two_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`8796093022209`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_three_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (8796093022209 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨43, 0,
      problem2_10_denominator_two_pow_forty_three_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 8796093022209`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_three_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (8796093022209 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨43, 0,
      problem2_10_denominator_two_pow_forty_three_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_three_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`17592186044417`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_four_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (17592186044417 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨44, 0,
      problem2_10_denominator_two_pow_forty_four_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 17592186044417`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_four_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (17592186044417 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨44, 0,
      problem2_10_denominator_two_pow_forty_four_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_four_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`35184372088833`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_five_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (35184372088833 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨45, 0,
      problem2_10_denominator_two_pow_forty_five_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 35184372088833`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_five_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (35184372088833 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨45, 0,
      problem2_10_denominator_two_pow_forty_five_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_five_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`70368744177665`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_six_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (70368744177665 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨46, 0,
      problem2_10_denominator_two_pow_forty_six_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 70368744177665`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_six_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (70368744177665 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨46, 0,
      problem2_10_denominator_two_pow_forty_six_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_six_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`140737488355329`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_seven_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (140737488355329 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨47, 0,
      problem2_10_denominator_two_pow_forty_seven_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 140737488355329`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_seven_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (140737488355329 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨47, 0,
      problem2_10_denominator_two_pow_forty_seven_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_seven_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`281474976710657`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_eight_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (281474976710657 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨48, 0,
      problem2_10_denominator_two_pow_forty_eight_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 281474976710657`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_eight_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (281474976710657 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨48, 0,
      problem2_10_denominator_two_pow_forty_eight_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_eight_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`562949953421313`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_nine_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (562949953421313 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨49, 0,
      problem2_10_denominator_two_pow_forty_nine_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 562949953421313`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_nine_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (562949953421313 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨49, 0,
      problem2_10_denominator_two_pow_forty_nine_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_forty_nine_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`1125899906842625`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (1125899906842625 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨50, 0,
      problem2_10_denominator_two_pow_fifty_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 1125899906842625`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (1125899906842625 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨50, 0,
      problem2_10_denominator_two_pow_fifty_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`2251799813685249`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_one_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (2251799813685249 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨51, 0,
      problem2_10_denominator_two_pow_fifty_one_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 2251799813685249`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_one_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (2251799813685249 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨51, 0,
      problem2_10_denominator_two_pow_fifty_one_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_one_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`4503599627370497`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_two_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (4503599627370497 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨52, 0,
      problem2_10_denominator_two_pow_fifty_two_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 4503599627370497`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_two_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (4503599627370497 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨52, 0,
      problem2_10_denominator_two_pow_fifty_two_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_two_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`9007199254740993`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_three_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (9007199254740993 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨53, 0,
      problem2_10_denominator_two_pow_fifty_three_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 9007199254740993`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_three_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (9007199254740993 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨53, 0,
      problem2_10_denominator_two_pow_fifty_three_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_three_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`18014398509481985`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_four_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (18014398509481985 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨54, 0,
      problem2_10_denominator_two_pow_fifty_four_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 18014398509481985`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_four_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (18014398509481985 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨54, 0,
      problem2_10_denominator_two_pow_fifty_four_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_four_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`36028797018963969`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_five_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (36028797018963969 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨55, 0,
      problem2_10_denominator_two_pow_fifty_five_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 36028797018963969`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_five_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (36028797018963969 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨55, 0,
      problem2_10_denominator_two_pow_fifty_five_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_five_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`72057594037927937`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_six_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (72057594037927937 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨56, 0,
      problem2_10_denominator_two_pow_fifty_six_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 72057594037927937`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_six_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (72057594037927937 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨56, 0,
      problem2_10_denominator_two_pow_fifty_six_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_six_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`144115188075855873`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_seven_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (144115188075855873 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨57, 0,
      problem2_10_denominator_two_pow_fifty_seven_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 144115188075855873`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_seven_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (144115188075855873 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨57, 0,
      problem2_10_denominator_two_pow_fifty_seven_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_seven_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`288230376151711745`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_eight_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (288230376151711745 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨58, 0,
      problem2_10_denominator_two_pow_fifty_eight_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 288230376151711745`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_eight_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (288230376151711745 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨58, 0,
      problem2_10_denominator_two_pow_fifty_eight_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_eight_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`576460752303423489`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_nine_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (576460752303423489 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨59, 0,
      problem2_10_denominator_two_pow_fifty_nine_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 576460752303423489`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_nine_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (576460752303423489 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨59, 0,
      problem2_10_denominator_two_pow_fifty_nine_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_fifty_nine_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`1152921504606846977`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (1152921504606846977 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨60, 0,
      problem2_10_denominator_two_pow_sixty_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 1152921504606846977`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (1152921504606846977 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨60, 0,
      problem2_10_denominator_two_pow_sixty_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`2305843009213693953`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_one_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (2305843009213693953 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨61, 0,
      problem2_10_denominator_two_pow_sixty_one_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 2305843009213693953`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_one_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (2305843009213693953 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨61, 0,
      problem2_10_denominator_two_pow_sixty_one_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_one_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`4611686018427387905`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_two_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (4611686018427387905 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨62, 0,
      problem2_10_denominator_two_pow_sixty_two_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 4611686018427387905`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_two_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (4611686018427387905 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨62, 0,
      problem2_10_denominator_two_pow_sixty_two_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_two_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`9223372036854775809`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_three_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (9223372036854775809 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨63, 0,
      problem2_10_denominator_two_pow_sixty_three_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 9223372036854775809`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_three_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (9223372036854775809 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨63, 0,
      problem2_10_denominator_two_pow_sixty_three_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_three_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`18446744073709551617`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_four_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (18446744073709551617 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨64, 0,
      problem2_10_denominator_two_pow_sixty_four_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 18446744073709551617`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_four_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (18446744073709551617 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨64, 0,
      problem2_10_denominator_two_pow_sixty_four_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_four_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`36893488147419103233`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_five_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (36893488147419103233 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨65, 0,
      problem2_10_denominator_two_pow_sixty_five_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 36893488147419103233`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_five_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (36893488147419103233 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨65, 0,
      problem2_10_denominator_two_pow_sixty_five_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_five_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`73786976294838206465`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_six_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (73786976294838206465 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨66, 0,
      problem2_10_denominator_two_pow_sixty_six_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 73786976294838206465`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_six_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (73786976294838206465 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨66, 0,
      problem2_10_denominator_two_pow_sixty_six_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_six_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`147573952589676412929`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_seven_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (147573952589676412929 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨67, 0,
      problem2_10_denominator_two_pow_sixty_seven_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 147573952589676412929`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_seven_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (147573952589676412929 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨67, 0,
      problem2_10_denominator_two_pow_sixty_seven_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_seven_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`295147905179352825857`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_eight_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (295147905179352825857 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨68, 0,
      problem2_10_denominator_two_pow_sixty_eight_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 295147905179352825857`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_eight_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (295147905179352825857 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨68, 0,
      problem2_10_denominator_two_pow_sixty_eight_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_eight_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`590295810358705651713`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_nine_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (590295810358705651713 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨69, 0,
      problem2_10_denominator_two_pow_sixty_nine_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 590295810358705651713`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_nine_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (590295810358705651713 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨69, 0,
      problem2_10_denominator_two_pow_sixty_nine_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_sixty_nine_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`1180591620717411303425`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (1180591620717411303425 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨70, 0,
      problem2_10_denominator_two_pow_seventy_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 1180591620717411303425`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (1180591620717411303425 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨70, 0,
      problem2_10_denominator_two_pow_seventy_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`2361183241434822606849`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_one_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (2361183241434822606849 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨71, 0,
      problem2_10_denominator_two_pow_seventy_one_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 2361183241434822606849`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_one_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (2361183241434822606849 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨71, 0,
      problem2_10_denominator_two_pow_seventy_one_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_one_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`4722366482869645213697`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_two_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (4722366482869645213697 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨72, 0,
      problem2_10_denominator_two_pow_seventy_two_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 4722366482869645213697`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_two_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (4722366482869645213697 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨72, 0,
      problem2_10_denominator_two_pow_seventy_two_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_two_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`9444732965739290427393`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_three_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (9444732965739290427393 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨73, 0,
      problem2_10_denominator_two_pow_seventy_three_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 9444732965739290427393`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_three_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (9444732965739290427393 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨73, 0,
      problem2_10_denominator_two_pow_seventy_three_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_three_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`18889465931478580854785`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_four_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (18889465931478580854785 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨74, 0,
      problem2_10_denominator_two_pow_seventy_four_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 18889465931478580854785`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_four_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (18889465931478580854785 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨74, 0,
      problem2_10_denominator_two_pow_seventy_four_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_four_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`37778931862957161709569`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_five_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (37778931862957161709569 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨75, 0,
      problem2_10_denominator_two_pow_seventy_five_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 37778931862957161709569`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_five_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (37778931862957161709569 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨75, 0,
      problem2_10_denominator_two_pow_seventy_five_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_five_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`75557863725914323419137`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_six_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (75557863725914323419137 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨76, 0,
      problem2_10_denominator_two_pow_seventy_six_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 75557863725914323419137`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_six_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (75557863725914323419137 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨76, 0,
      problem2_10_denominator_two_pow_seventy_six_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_six_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`151115727451828646838273`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_seven_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (151115727451828646838273 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨77, 0,
      problem2_10_denominator_two_pow_seventy_seven_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 151115727451828646838273`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_seven_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (151115727451828646838273 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨77, 0,
      problem2_10_denominator_two_pow_seventy_seven_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_seven_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`302231454903657293676545`
power-of-two numerator family `m = 2^k`. -/
theorem problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_eight_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (302231454903657293676545 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ k)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨78, 0,
      problem2_10_denominator_two_pow_seventy_eight_plus_one_eq_power_sum⟩
  · have hpow :
        (2 : ℤ) ^ k < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hk
    have hnonneg : 0 ≤ (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^k`, `n = 302231454903657293676545`. -/
theorem problem2_10_negative_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_eight_plus_one
    {k : ℕ} (hk : k < ieeeDoubleFormat.t - 1) :
    (∃ i j : ℕ, (302231454903657293676545 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ k))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨78, 0,
      problem2_10_denominator_two_pow_seventy_eight_plus_one_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_numerator_kahan_hypotheses_of_two_pow_seventy_eight_plus_one
        (k := k) hk).2

/-- Source-side integer hypotheses for the denominator-`18` shifted
power-of-two numerator family `m = 2^(k+1)`. -/
theorem problem2_10_two_pow_succ_numerator_kahan_hypotheses_of_eighteen
    {k : ℕ} (hk : k + 2 < ieeeDoubleFormat.t) :
    (∃ i j : ℕ, (18 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((2 : ℤ) ^ (k + 1))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨4, 1, problem2_10_denominator_eighteen_eq_power_sum⟩
  · have hlt_exp : k + 1 < ieeeDoubleFormat.t - 1 := by omega
    have hpow :
        (2 : ℤ) ^ (k + 1) < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) hlt_exp
    have hnonneg : 0 ≤ (2 : ℤ) ^ (k + 1) := by positivity
    simpa [abs_of_nonneg hnonneg] using hpow

/-- Signed source-side integer hypotheses for
`m = -2^(k+1)`, `n = 18`. -/
theorem problem2_10_negative_two_pow_succ_numerator_kahan_hypotheses_of_eighteen
    {k : ℕ} (hk : k + 2 < ieeeDoubleFormat.t) :
    (∃ i j : ℕ, (18 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((2 : ℤ) ^ (k + 1)))| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨4, 1, problem2_10_denominator_eighteen_eq_power_sum⟩
  · simpa using
      (problem2_10_two_pow_succ_numerator_kahan_hypotheses_of_eighteen
        (k := k) hk).2

/-- The displayed `m = 1`, `n = 3` example satisfies the integer-side
hypotheses in Kahan's quoted theorem: `n` is a sum of two powers of two and
`|m| < 2^(t-1)` for IEEE double precision. -/
theorem problem2_10_displayed_kahan_hypotheses :
    (∃ i j : ℕ, (3 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(1 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨1, 0, problem2_10_displayed_denominator_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- The next displayed-prefix pair `m = 1`, `n = 5` satisfies the integer-side
hypotheses in Kahan's quoted theorem. -/
theorem problem2_10_one_fifth_kahan_hypotheses :
    (∃ i j : ℕ, (5 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(1 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨2, 0, problem2_10_denominator_five_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- The signed companion `m = -1`, `n = 5` satisfies the integer-side
hypotheses in Kahan's quoted theorem. -/
theorem problem2_10_negative_one_fifth_kahan_hypotheses :
    (∃ i j : ℕ, (5 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-1 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨2, 0, problem2_10_denominator_five_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- The next numerator magnitude `m = 2`, `n = 5` satisfies the integer-side
hypotheses in Kahan's quoted theorem. -/
theorem problem2_10_two_fifth_kahan_hypotheses :
    (∃ i j : ℕ, (5 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(2 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨2, 0, problem2_10_denominator_five_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- The signed companion `m = -2`, `n = 5` satisfies the integer-side
hypotheses in Kahan's quoted theorem. -/
theorem problem2_10_negative_two_fifth_kahan_hypotheses :
    (∃ i j : ℕ, (5 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-2 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨2, 0, problem2_10_denominator_five_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- The first denominator-`5` non-power-of-two numerator `m = 3` satisfies
the integer-side hypotheses in Kahan's quoted theorem. -/
theorem problem2_10_three_fifth_kahan_hypotheses :
    (∃ i j : ℕ, (5 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(3 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨2, 0, problem2_10_denominator_five_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- The signed companion `m = -3`, `n = 5` satisfies the integer-side
hypotheses in Kahan's quoted theorem. -/
theorem problem2_10_negative_three_fifth_kahan_hypotheses :
    (∃ i j : ℕ, (5 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-3 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨2, 0, problem2_10_denominator_five_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- Source-side integer hypotheses for the denominator-`5` scaled
non-power-of-two numerator family `m = 3*2^k`.  The side condition
`k + 2 < t` is the source-sized integer bound that implies
`3*2^k < 2^(t-1)`. -/
theorem problem2_10_three_mul_powerOfTwo_numerator_kahan_hypotheses_of_five
    {k : ℕ} (hk : k + 2 < ieeeDoubleFormat.t) :
    (∃ i j : ℕ, (5 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |((3 : ℤ) * (2 : ℤ) ^ k)| <
        (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨2, 0, problem2_10_denominator_five_eq_power_sum⟩
  · have hpow_pos : 0 < (2 : ℤ) ^ k :=
      pow_pos (by norm_num : (0 : ℤ) < 2) k
    have hlt_to_pow :
        (3 : ℤ) * (2 : ℤ) ^ k < (2 : ℤ) ^ (k + 2) := by
      calc
        (3 : ℤ) * (2 : ℤ) ^ k <
            (2 : ℤ) ^ (2 : ℕ) * (2 : ℤ) ^ k :=
          mul_lt_mul_of_pos_right (by norm_num : (3 : ℤ) < (2 : ℤ) ^ (2 : ℕ))
            hpow_pos
        _ = (2 : ℤ) ^ (k + 2) := by
          rw [pow_add]
          ring
    have hle_exp : k + 2 ≤ ieeeDoubleFormat.t - 1 := by omega
    have hle_pow :
        (2 : ℤ) ^ (k + 2) ≤ (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hle_exp
    have hnonneg : 0 ≤ (3 : ℤ) * (2 : ℤ) ^ k := by positivity
    simpa [abs_of_nonneg hnonneg] using lt_of_lt_of_le hlt_to_pow hle_pow

/-- Signed source-side integer hypotheses for
`m = -(3*2^k)`, `n = 5`. -/
theorem problem2_10_negative_three_mul_powerOfTwo_numerator_kahan_hypotheses_of_five
    {k : ℕ} (hk : k + 2 < ieeeDoubleFormat.t) :
    (∃ i j : ℕ, (5 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-((3 : ℤ) * (2 : ℤ) ^ k))| <
        (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨2, 0, problem2_10_denominator_five_eq_power_sum⟩
  · simpa using
      (problem2_10_three_mul_powerOfTwo_numerator_kahan_hypotheses_of_five
        (k := k) hk).2

/-- The signed companion `m = -1`, `n = 3` also satisfies the integer-side
hypotheses in Kahan's quoted theorem. -/
theorem problem2_10_displayed_negative_kahan_hypotheses :
    (∃ i j : ℕ, (3 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-1 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨1, 0, problem2_10_displayed_denominator_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- The displayed `m = 2`, `n = 3` pair also satisfies the integer-side
hypotheses in Kahan's quoted theorem. -/
theorem problem2_10_displayed_two_kahan_hypotheses :
    (∃ i j : ℕ, (3 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(2 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨1, 0, problem2_10_displayed_denominator_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- The signed companion `m = -2`, `n = 3` satisfies the integer-side
hypotheses in Kahan's quoted theorem. -/
theorem problem2_10_displayed_negative_two_kahan_hypotheses :
    (∃ i j : ℕ, (3 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-2 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨1, 0, problem2_10_displayed_denominator_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- The `m = 4`, `n = 3` pair also satisfies the integer-side hypotheses in
Kahan's quoted theorem. -/
theorem problem2_10_displayed_four_kahan_hypotheses :
    (∃ i j : ℕ, (3 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(4 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨1, 0, problem2_10_displayed_denominator_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- The signed companion `m = -4`, `n = 3` satisfies the integer-side
hypotheses in Kahan's quoted theorem. -/
theorem problem2_10_displayed_negative_four_kahan_hypotheses :
    (∃ i j : ℕ, (3 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-4 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨1, 0, problem2_10_displayed_denominator_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- The `m = 8`, `n = 3` pair also satisfies the integer-side hypotheses in
Kahan's quoted theorem. -/
theorem problem2_10_displayed_eight_kahan_hypotheses :
    (∃ i j : ℕ, (3 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(8 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨1, 0, problem2_10_displayed_denominator_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- The signed companion `m = -8`, `n = 3` satisfies the integer-side
hypotheses in Kahan's quoted theorem. -/
theorem problem2_10_displayed_negative_eight_kahan_hypotheses :
    (∃ i j : ℕ, (3 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-8 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨1, 0, problem2_10_displayed_denominator_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- The `m = 16`, `n = 3` pair also satisfies the integer-side hypotheses in
Kahan's quoted theorem. -/
theorem problem2_10_displayed_sixteen_kahan_hypotheses :
    (∃ i j : ℕ, (3 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(16 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨1, 0, problem2_10_displayed_denominator_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- The signed companion `m = -16`, `n = 3` satisfies the integer-side
hypotheses in Kahan's quoted theorem. -/
theorem problem2_10_displayed_negative_sixteen_kahan_hypotheses :
    (∃ i j : ℕ, (3 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-16 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨1, 0, problem2_10_displayed_denominator_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- The `m = 32`, `n = 3` pair also satisfies the integer-side hypotheses in
Kahan's quoted theorem. -/
theorem problem2_10_displayed_thirtytwo_kahan_hypotheses :
    (∃ i j : ℕ, (3 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(32 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨1, 0, problem2_10_displayed_denominator_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

/-- The signed companion `m = -32`, `n = 3` satisfies the integer-side
hypotheses in Kahan's quoted theorem. -/
theorem problem2_10_displayed_negative_thirtytwo_kahan_hypotheses :
    (∃ i j : ℕ, (3 : ℕ) = 2 ^ i + 2 ^ j) ∧
      |(-32 : ℤ)| < (2 : ℤ) ^ (ieeeDoubleFormat.t - 1) := by
  constructor
  · exact ⟨1, 0, problem2_10_displayed_denominator_eq_power_sum⟩
  · norm_num [ieeeDoubleFormat]

theorem problem2_10_ieeeDouble_finiteSystem_one :
    ieeeDoubleFormat.finiteSystem (1 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 4503599627370496, (1 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeDoubleFormat, exponentInRange]
  · norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]
    rfl

theorem problem2_10_ieeeDouble_finiteSystem_two :
    ieeeDoubleFormat.finiteSystem (2 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 4503599627370496, (2 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeDoubleFormat, exponentInRange]
  · norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]
    rfl

theorem problem2_10_ieeeDouble_finiteSystem_four :
    ieeeDoubleFormat.finiteSystem (4 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 4503599627370496, (3 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeDoubleFormat, exponentInRange]
  · norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]
    rfl

theorem problem2_10_ieeeDouble_finiteSystem_eight :
    ieeeDoubleFormat.finiteSystem (8 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 4503599627370496, (4 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeDoubleFormat, exponentInRange]
  · norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]
    rfl

theorem problem2_10_ieeeDouble_finiteSystem_sixteen :
    ieeeDoubleFormat.finiteSystem (16 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 4503599627370496, (5 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeDoubleFormat, exponentInRange]
  · norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]
    rfl

theorem problem2_10_ieeeDouble_finiteSystem_thirtytwo :
    ieeeDoubleFormat.finiteSystem (32 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 4503599627370496, (6 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeDoubleFormat, exponentInRange]
  · norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]
    rfl

theorem problem2_10_ieeeDouble_finiteSystem_three :
    ieeeDoubleFormat.finiteSystem (3 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 6755399441055744, (2 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeDoubleFormat, exponentInRange]
  · norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]
    rfl

theorem problem2_10_ieeeDouble_finiteSystem_five :
    ieeeDoubleFormat.finiteSystem (5 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 5629499534213120, (3 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeDoubleFormat, exponentInRange]
  · norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]
    rfl

theorem problem2_10_ieeeDouble_finiteSystem_neg_one :
    ieeeDoubleFormat.finiteSystem (-1 : ℝ) := by
  simpa using
    ieeeDoubleFormat.finiteSystem_neg problem2_10_ieeeDouble_finiteSystem_one

theorem problem2_10_ieeeDouble_finiteSystem_neg_two :
    ieeeDoubleFormat.finiteSystem (-2 : ℝ) := by
  simpa using
    ieeeDoubleFormat.finiteSystem_neg problem2_10_ieeeDouble_finiteSystem_two

theorem problem2_10_ieeeDouble_finiteSystem_neg_three :
    ieeeDoubleFormat.finiteSystem (-3 : ℝ) := by
  simpa using
    ieeeDoubleFormat.finiteSystem_neg problem2_10_ieeeDouble_finiteSystem_three

theorem problem2_10_ieeeDouble_finiteSystem_neg_four :
    ieeeDoubleFormat.finiteSystem (-4 : ℝ) := by
  simpa using
    ieeeDoubleFormat.finiteSystem_neg problem2_10_ieeeDouble_finiteSystem_four

theorem problem2_10_ieeeDouble_finiteSystem_neg_eight :
    ieeeDoubleFormat.finiteSystem (-8 : ℝ) := by
  simpa using
    ieeeDoubleFormat.finiteSystem_neg problem2_10_ieeeDouble_finiteSystem_eight

theorem problem2_10_ieeeDouble_finiteSystem_neg_sixteen :
    ieeeDoubleFormat.finiteSystem (-16 : ℝ) := by
  simpa using
    ieeeDoubleFormat.finiteSystem_neg problem2_10_ieeeDouble_finiteSystem_sixteen

theorem problem2_10_ieeeDouble_finiteSystem_neg_thirtytwo :
    ieeeDoubleFormat.finiteSystem (-32 : ℝ) := by
  simpa using
    ieeeDoubleFormat.finiteSystem_neg problem2_10_ieeeDouble_finiteSystem_thirtytwo

theorem problem2_10_ieeeDouble_displayed_trace_finite_inputs :
    ieeeDoubleFormat.finiteSystem (1 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem (3 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (1 : ℝ) 3) := by
  exact ⟨problem2_10_ieeeDouble_finiteSystem_one,
    problem2_10_ieeeDouble_finiteSystem_three,
    ieeeDoubleFormat.finiteRoundToEvenOp_finiteSystem BasicOp.div (1 : ℝ) 3⟩

theorem problem2_10_ieeeDouble_negative_displayed_trace_finite_inputs :
    ieeeDoubleFormat.finiteSystem (-1 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem (3 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (-1 : ℝ) 3) := by
  exact ⟨problem2_10_ieeeDouble_finiteSystem_neg_one,
    problem2_10_ieeeDouble_finiteSystem_three,
    ieeeDoubleFormat.finiteRoundToEvenOp_finiteSystem BasicOp.div (-1 : ℝ) 3⟩

theorem problem2_10_ieeeDouble_one_fifth_trace_finite_inputs :
    ieeeDoubleFormat.finiteSystem (1 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem (5 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (1 : ℝ) 5) := by
  exact ⟨problem2_10_ieeeDouble_finiteSystem_one,
    problem2_10_ieeeDouble_finiteSystem_five,
    ieeeDoubleFormat.finiteRoundToEvenOp_finiteSystem BasicOp.div (1 : ℝ) 5⟩

theorem problem2_10_ieeeDouble_neg_one_fifth_trace_finite_inputs :
    ieeeDoubleFormat.finiteSystem (-1 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem (5 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (-1 : ℝ) 5) := by
  exact ⟨problem2_10_ieeeDouble_finiteSystem_neg_one,
    problem2_10_ieeeDouble_finiteSystem_five,
    ieeeDoubleFormat.finiteRoundToEvenOp_finiteSystem BasicOp.div (-1 : ℝ) 5⟩

theorem problem2_10_ieeeDouble_two_fifth_trace_finite_inputs :
    ieeeDoubleFormat.finiteSystem (2 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem (5 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (2 : ℝ) 5) := by
  exact ⟨problem2_10_ieeeDouble_finiteSystem_two,
    problem2_10_ieeeDouble_finiteSystem_five,
    ieeeDoubleFormat.finiteRoundToEvenOp_finiteSystem BasicOp.div (2 : ℝ) 5⟩

theorem problem2_10_ieeeDouble_neg_two_fifth_trace_finite_inputs :
    ieeeDoubleFormat.finiteSystem (-2 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem (5 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (-2 : ℝ) 5) := by
  exact ⟨problem2_10_ieeeDouble_finiteSystem_neg_two,
    problem2_10_ieeeDouble_finiteSystem_five,
    ieeeDoubleFormat.finiteRoundToEvenOp_finiteSystem BasicOp.div (-2 : ℝ) 5⟩

theorem problem2_10_ieeeDouble_three_fifth_trace_finite_inputs :
    ieeeDoubleFormat.finiteSystem (3 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem (5 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (3 : ℝ) 5) := by
  exact ⟨problem2_10_ieeeDouble_finiteSystem_three,
    problem2_10_ieeeDouble_finiteSystem_five,
    ieeeDoubleFormat.finiteRoundToEvenOp_finiteSystem BasicOp.div (3 : ℝ) 5⟩

theorem problem2_10_ieeeDouble_neg_three_fifth_trace_finite_inputs :
    ieeeDoubleFormat.finiteSystem (-3 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem (5 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (-3 : ℝ) 5) := by
  exact ⟨problem2_10_ieeeDouble_finiteSystem_neg_three,
    problem2_10_ieeeDouble_finiteSystem_five,
    ieeeDoubleFormat.finiteRoundToEvenOp_finiteSystem BasicOp.div (-3 : ℝ) 5⟩

theorem problem2_10_ieeeDouble_two_displayed_trace_finite_inputs :
    ieeeDoubleFormat.finiteSystem (2 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem (3 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (2 : ℝ) 3) := by
  exact ⟨problem2_10_ieeeDouble_finiteSystem_two,
    problem2_10_ieeeDouble_finiteSystem_three,
    ieeeDoubleFormat.finiteRoundToEvenOp_finiteSystem BasicOp.div (2 : ℝ) 3⟩

theorem problem2_10_ieeeDouble_negative_two_displayed_trace_finite_inputs :
    ieeeDoubleFormat.finiteSystem (-2 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem (3 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (-2 : ℝ) 3) := by
  exact ⟨problem2_10_ieeeDouble_finiteSystem_neg_two,
    problem2_10_ieeeDouble_finiteSystem_three,
    ieeeDoubleFormat.finiteRoundToEvenOp_finiteSystem BasicOp.div (-2 : ℝ) 3⟩

theorem problem2_10_ieeeDouble_four_displayed_trace_finite_inputs :
    ieeeDoubleFormat.finiteSystem (4 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem (3 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (4 : ℝ) 3) := by
  exact ⟨problem2_10_ieeeDouble_finiteSystem_four,
    problem2_10_ieeeDouble_finiteSystem_three,
    ieeeDoubleFormat.finiteRoundToEvenOp_finiteSystem BasicOp.div (4 : ℝ) 3⟩

theorem problem2_10_ieeeDouble_negative_four_displayed_trace_finite_inputs :
    ieeeDoubleFormat.finiteSystem (-4 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem (3 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (-4 : ℝ) 3) := by
  exact ⟨problem2_10_ieeeDouble_finiteSystem_neg_four,
    problem2_10_ieeeDouble_finiteSystem_three,
    ieeeDoubleFormat.finiteRoundToEvenOp_finiteSystem BasicOp.div (-4 : ℝ) 3⟩

theorem problem2_10_ieeeDouble_eight_displayed_trace_finite_inputs :
    ieeeDoubleFormat.finiteSystem (8 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem (3 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (8 : ℝ) 3) := by
  exact ⟨problem2_10_ieeeDouble_finiteSystem_eight,
    problem2_10_ieeeDouble_finiteSystem_three,
    ieeeDoubleFormat.finiteRoundToEvenOp_finiteSystem BasicOp.div (8 : ℝ) 3⟩

theorem problem2_10_ieeeDouble_negative_eight_displayed_trace_finite_inputs :
    ieeeDoubleFormat.finiteSystem (-8 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem (3 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (-8 : ℝ) 3) := by
  exact ⟨problem2_10_ieeeDouble_finiteSystem_neg_eight,
    problem2_10_ieeeDouble_finiteSystem_three,
    ieeeDoubleFormat.finiteRoundToEvenOp_finiteSystem BasicOp.div (-8 : ℝ) 3⟩

theorem problem2_10_ieeeDouble_sixteen_displayed_trace_finite_inputs :
    ieeeDoubleFormat.finiteSystem (16 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem (3 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (16 : ℝ) 3) := by
  exact ⟨problem2_10_ieeeDouble_finiteSystem_sixteen,
    problem2_10_ieeeDouble_finiteSystem_three,
    ieeeDoubleFormat.finiteRoundToEvenOp_finiteSystem BasicOp.div (16 : ℝ) 3⟩

theorem problem2_10_ieeeDouble_negative_sixteen_displayed_trace_finite_inputs :
    ieeeDoubleFormat.finiteSystem (-16 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem (3 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (-16 : ℝ) 3) := by
  exact ⟨problem2_10_ieeeDouble_finiteSystem_neg_sixteen,
    problem2_10_ieeeDouble_finiteSystem_three,
    ieeeDoubleFormat.finiteRoundToEvenOp_finiteSystem BasicOp.div (-16 : ℝ) 3⟩

theorem problem2_10_ieeeDouble_thirtytwo_displayed_trace_finite_inputs :
    ieeeDoubleFormat.finiteSystem (32 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem (3 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (32 : ℝ) 3) := by
  exact ⟨problem2_10_ieeeDouble_finiteSystem_thirtytwo,
    problem2_10_ieeeDouble_finiteSystem_three,
    ieeeDoubleFormat.finiteRoundToEvenOp_finiteSystem BasicOp.div (32 : ℝ) 3⟩

theorem problem2_10_ieeeDouble_negative_thirtytwo_displayed_trace_finite_inputs :
    ieeeDoubleFormat.finiteSystem (-32 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem (3 : ℝ) ∧
      ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (-32 : ℝ) 3) := by
  exact ⟨problem2_10_ieeeDouble_finiteSystem_neg_thirtytwo,
    problem2_10_ieeeDouble_finiteSystem_three,
    ieeeDoubleFormat.finiteRoundToEvenOp_finiteSystem BasicOp.div (-32 : ℝ) 3⟩

/-- Zero-numerator branch of Kahan's Problem 2.10 identity at the finite
round-to-even operation layer.  For any nonzero real denominator, the rounded
division `0/n` is exactly zero and the subsequent rounded multiplication by
`n` is again exactly zero. -/
theorem problem2_10_finiteRoundToEven_zero_div_mul
    (fmt : FloatingPointFormat) {n : ℝ} (hn : n ≠ 0) :
    fmt.finiteRoundToEvenOp BasicOp.mul
        (fmt.finiteRoundToEvenOp BasicOp.div (0 : ℝ) n) n = 0 := by
  have hzero_div : (0 : ℝ) / n = 0 := by
    field_simp [hn]
    ring
  have hdivfin :
      fmt.finiteSystem (BasicOp.exact BasicOp.div (0 : ℝ) n) := by
    simpa [BasicOp.exact, hzero_div] using fmt.finiteSystem_zero
  have hdiv :
      fmt.finiteRoundToEvenOp BasicOp.div (0 : ℝ) n = 0 := by
    have h :=
      fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.div) (x := (0 : ℝ)) (y := n) hdivfin
    simpa [BasicOp.exact, hzero_div] using h
  have hmulfin :
      fmt.finiteSystem (BasicOp.exact BasicOp.mul (0 : ℝ) n) := by
    simpa [BasicOp.exact] using fmt.finiteSystem_zero
  have hmul :
      fmt.finiteRoundToEvenOp BasicOp.mul (0 : ℝ) n = 0 := by
    have h :=
      fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.mul) (x := (0 : ℝ)) (y := n) hmulfin
    simpa [BasicOp.exact] using h
  rw [hdiv]
  exact hmul

/-- Exact-quotient branch of the Problem 2.10 operation trace.  If `m/n` is
already finite representable and `m` is finite representable, then the
finite round-to-even division and multiplication sequence returns `m`
exactly.  This isolates one easy part of the arbitrary-denominator route from
the genuinely hard Kahan rounding theorem for non-representable quotients. -/
theorem problem2_10_finiteRoundToEven_div_mul_exact_of_finiteSystem
    (fmt : FloatingPointFormat) {m n : ℝ} (hn : n ≠ 0)
    (hquot : fmt.finiteSystem (m / n)) (hm : fmt.finiteSystem m) :
    fmt.finiteRoundToEvenOp BasicOp.mul
        (fmt.finiteRoundToEvenOp BasicOp.div m n) n = m := by
  have hdivfin :
      fmt.finiteSystem (BasicOp.exact BasicOp.div m n) := by
    simpa [BasicOp.exact] using hquot
  have hdiv :
      fmt.finiteRoundToEvenOp BasicOp.div m n = m / n := by
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.div) (x := m) (y := n) hdivfin)
  have hmulfin :
      fmt.finiteSystem (BasicOp.exact BasicOp.mul (m / n) n) := by
    simpa [BasicOp.exact, div_mul_cancel₀ m hn] using hm
  have hmul :
      fmt.finiteRoundToEvenOp BasicOp.mul (m / n) n = m := by
    simpa [BasicOp.exact, div_mul_cancel₀ m hn] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.mul) (x := m / n) (y := n) hmulfin)
  rw [hdiv]
  exact hmul

/-- Source-shaped zero-numerator branch for Problem 2.10 in the IEEE-double
finite-selector model.  This closes the `m = 0` case of the quoted Kahan
identity for every nonzero natural denominator satisfying the displayed
allowable-denominator predicate. -/
theorem problem2_10_ieeeDouble_zero_allowable_denominator_times_denominator
    {n : ℕ} (hn : n ≠ 0) (_hnAllow : problem2_10_allowableDenominator n) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (0 : ℝ) (n : ℝ))
        (n : ℝ) = 0 := by
  have hnreal : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn
  exact problem2_10_finiteRoundToEven_zero_div_mul
    ieeeDoubleFormat (n := (n : ℝ)) hnreal

/-- Source-shaped zero-numerator branch with no separate nonzero-denominator
hypothesis: any allowable denominator is nonzero. -/
theorem problem2_10_ieeeDouble_zero_allowable_denominator_times_denominator'
    {n : ℕ} (hnAllow : problem2_10_allowableDenominator n) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (0 : ℝ) (n : ℝ))
        (n : ℝ) = 0 := by
  exact problem2_10_ieeeDouble_zero_allowable_denominator_times_denominator
    (problem2_10_allowableDenominator_ne_zero hnAllow) hnAllow

/-- IEEE-double exact-quotient branch for arbitrary allowable denominators.
This is not the full Kahan theorem: it closes the representable-quotient route
and records that the remaining arbitrary-denominator problem is exactly the
non-representable rounded-quotient case. -/
theorem problem2_10_ieeeDouble_allowable_denominator_exact_quotient_trace
    {m : ℝ} {n : ℕ}
    (hnAllow : problem2_10_allowableDenominator n)
    (hquot : ieeeDoubleFormat.finiteSystem (m / (n : ℝ)))
    (hm : ieeeDoubleFormat.finiteSystem m) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div m (n : ℝ))
        (n : ℝ) = m := by
  have hnreal : (n : ℝ) ≠ 0 := by
    exact_mod_cast problem2_10_allowableDenominator_ne_zero hnAllow
  exact problem2_10_finiteRoundToEven_div_mul_exact_of_finiteSystem
    ieeeDoubleFormat (n := (n : ℝ)) hnreal hquot hm

/-- The rounded double approximation to `1/5`, multiplied exactly by `5`,
lands just above `1`, but still closer to `1` than to the next double. -/
theorem problem2_10_ieeeDouble_rounded_oneFifth_mul_five_above_one :
    ((7205759403792794 : ℝ) * (2 : ℝ) ^ (-55 : ℤ)) * 5 =
      (1 : ℝ) + (2 : ℝ) ^ (-54 : ℤ) := by
  norm_num [zpow_neg]

/-- The rounded double approximation to `-1/5`, multiplied exactly by `5`,
is `-(1 + 2^-54)`. -/
theorem problem2_10_ieeeDouble_negative_rounded_oneFifth_mul_five_below_neg_one :
    (-((7205759403792794 : ℝ) * (2 : ℝ) ^ (-55 : ℤ))) * 5 =
      -((1 : ℝ) + (2 : ℝ) ^ (-54 : ℤ)) := by
  rw [show
      (-((7205759403792794 : ℝ) * (2 : ℝ) ^ (-55 : ℤ))) * 5 =
        -(((7205759403792794 : ℝ) * (2 : ℝ) ^ (-55 : ℤ)) * 5) by
    ring]
  rw [problem2_10_ieeeDouble_rounded_oneFifth_mul_five_above_one]

/-- The rounded double approximation to `2/5`, multiplied exactly by `5`,
lands just above `2`, but still closer to `2` than to the next double. -/
theorem problem2_10_ieeeDouble_rounded_twoFifths_mul_five_above_two :
    ((7205759403792794 : ℝ) * (2 : ℝ) ^ (-54 : ℤ)) * 5 =
      (2 : ℝ) + (2 : ℝ) ^ (-53 : ℤ) := by
  norm_num [zpow_neg]

/-- The rounded double approximation to `-2/5`, multiplied exactly by `5`,
is `-(2 + 2^-53)`. -/
theorem problem2_10_ieeeDouble_negative_rounded_twoFifths_mul_five_below_neg_two :
    (-((7205759403792794 : ℝ) * (2 : ℝ) ^ (-54 : ℤ))) * 5 =
      -((2 : ℝ) + (2 : ℝ) ^ (-53 : ℤ)) := by
  rw [show
      (-((7205759403792794 : ℝ) * (2 : ℝ) ^ (-54 : ℤ))) * 5 =
        -(((7205759403792794 : ℝ) * (2 : ℝ) ^ (-54 : ℤ)) * 5) by
    ring]
  rw [problem2_10_ieeeDouble_rounded_twoFifths_mul_five_above_two]

/-- The rounded double approximation to `3/5`, multiplied exactly by `5`,
lands just below `3`, but still closer to `3` than to the previous double. -/
theorem problem2_10_ieeeDouble_rounded_threeFifths_mul_five_below_three :
    ((5404319552844595 : ℝ) * (2 : ℝ) ^ (-53 : ℤ)) * 5 =
      (3 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) := by
  norm_num [zpow_neg]

/-- The rounded double approximation to `-3/5`, multiplied exactly by `5`,
is `-(3 - 2^-53)`. -/
theorem problem2_10_ieeeDouble_negative_rounded_threeFifths_mul_five_above_neg_three :
    (-((5404319552844595 : ℝ) * (2 : ℝ) ^ (-53 : ℤ))) * 5 =
      -((3 : ℝ) - (2 : ℝ) ^ (-53 : ℤ)) := by
  rw [show
      (-((5404319552844595 : ℝ) * (2 : ℝ) ^ (-53 : ℤ))) * 5 =
        -(((5404319552844595 : ℝ) * (2 : ℝ) ^ (-53 : ℤ)) * 5) by
    ring]
  rw [problem2_10_ieeeDouble_rounded_threeFifths_mul_five_below_three]

/-- The rounded lower approximation to `(3*2^k)/5`, multiplied exactly by
`5`, is a quarter ulp below `3*2^k`. -/
theorem problem2_10_ieeeDouble_rounded_three_mul_two_pow_fifths_mul_five_below
    {k : ℕ} :
    ((5404319552844595 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 53))) * 5 =
      (3 : ℝ) * (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 53)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 53)) * (2 : ℝ) ^ (53 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 53)) (53 : ℤ)
    have hexp : ((k : ℤ) - 53) + 53 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  rw [hpow]
  norm_num [zpow_natCast]
  ring

theorem problem2_10_ieeeDouble_negative_rounded_three_mul_two_pow_fifths_mul_five_above
    {k : ℕ} :
    (-((5404319552844595 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 53)))) * 5 =
      -((3 : ℝ) * (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 53))) := by
  rw [show
      (-((5404319552844595 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 53)))) * 5 =
        -(((5404319552844595 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 53))) * 5) by
    ring]
  rw [problem2_10_ieeeDouble_rounded_three_mul_two_pow_fifths_mul_five_below]

/-- Result-by-result generic audit for the second denominator-`5`,
power-of-two operation: after the rounded division has stored the upper
IEEE-double approximation to `(2^k)/5`, the exact product with `5` is
`2^k + 2^(k-54)`. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_fifths_mul_five_above_two_pow
    {k : ℕ} :
    ((7205759403792794 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 55))) * 5 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 54)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 55)) * (2 : ℝ) ^ (55 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 55)) (55 : ℤ)
    have hexp : ((k : ℤ) - 55) + 55 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have hpow54 :
      (2 : ℝ) ^ (((k : ℤ) - 54)) =
        (2 : ℝ) ^ (((k : ℤ) - 55)) * 2 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 55)) (1 : ℤ)
    have hexp : ((k : ℤ) - 55) + 1 = (k : ℤ) - 54 := by ring
    rw [hexp] at h
    simpa [zpow_one] using h
  rw [hpow, hpow54]
  norm_num [zpow_natCast]
  ring

/-- The generic rounded upper approximation to `-(2^k)/5`, multiplied exactly
by `5`, is just below `-2^k`. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_fifths_mul_five_below_two_pow
    {k : ℕ} :
    (-((7205759403792794 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 55)))) * 5 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 54))) := by
  rw [show
      (-((7205759403792794 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 55)))) * 5 =
        -(((7205759403792794 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 55))) * 5) by
    ring]
  rw [problem2_10_ieeeDouble_rounded_two_pow_fifths_mul_five_above_two_pow]

/-- Exact product audit for denominator `9`: after the rounded division has
stored the lower IEEE-double approximation to `(2^k)/9`, multiplying by `9`
lands at the midpoint immediately below `2^k`. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_ninths_mul_nine_midpoint
    {k : ℕ} :
    ((8006399337547548 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 56))) * 9 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 54)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 56)) * (2 : ℝ) ^ (56 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 56)) (56 : ℤ)
    have hexp : ((k : ℤ) - 56) + 56 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 54)) =
        (2 : ℝ) ^ (((k : ℤ) - 56)) * 4 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 56)) (2 : ℤ)
    have hexp : ((k : ℤ) - 56) + 2 = (k : ℤ) - 54 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 54)) =
          (2 : ℝ) ^ (((k : ℤ) - 56)) * (2 : ℝ) ^ (2 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 56)) * 4 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`9`, power-of-two second
operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_ninths_mul_nine_midpoint
    {k : ℕ} :
    (-((8006399337547548 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 56)))) * 9 =
      -((2 : ℝ) ^ k) + (2 : ℝ) ^ (((k : ℤ) - 54)) := by
  rw [show
      (-((8006399337547548 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 56)))) * 9 =
        -(((8006399337547548 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 56))) * 9) by
    ring]
  rw [problem2_10_ieeeDouble_rounded_two_pow_ninths_mul_nine_midpoint]
  ring

/-- Exact product audit for denominator `17`: after the rounded division has
stored the lower IEEE-double approximation to `(2^k)/17`, multiplying by `17`
lands one sixteenth of an ulp below `2^k`. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_seventeenths_mul_seventeen_below
    {k : ℕ} :
    ((8477364004462110 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 57))) * 17 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 56)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 57)) * (2 : ℝ) ^ (57 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 57)) (57 : ℤ)
    have hexp : ((k : ℤ) - 57) + 57 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 56)) =
        (2 : ℝ) ^ (((k : ℤ) - 57)) * 2 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 57)) (1 : ℤ)
    have hexp : ((k : ℤ) - 57) + 1 = (k : ℤ) - 56 := by ring
    rw [hexp] at h
    simpa [zpow_one] using h
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`17`, power-of-two second
operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_seventeenths_mul_seventeen_below
    {k : ℕ} :
    (-((8477364004462110 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 57)))) * 17 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 56))) := by
  rw [show
      (-((8477364004462110 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 57)))) * 17 =
        -(((8477364004462110 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 57))) * 17) by
    ring]
  rw [problem2_10_ieeeDouble_rounded_two_pow_seventeenths_mul_seventeen_below]

/-- Exact product audit for denominator `33`: after the rounded division has
stored the upper IEEE-double approximation to `(2^k)/33`, multiplying by `33`
lands one eighth of an ulp above `2^k`. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_thirtythirds_mul_thirtythree_above
    {k : ℕ} :
    ((8734253822779144 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 58))) * 33 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 55)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 58)) * (2 : ℝ) ^ (58 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 58)) (58 : ℤ)
    have hexp : ((k : ℤ) - 58) + 58 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 55)) =
        (2 : ℝ) ^ (((k : ℤ) - 58)) * 8 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 58)) (3 : ℤ)
    have hexp : ((k : ℤ) - 58) + 3 = (k : ℤ) - 55 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 55)) =
          (2 : ℝ) ^ (((k : ℤ) - 58)) * (2 : ℝ) ^ (3 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 58)) * 8 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`33`, power-of-two second
operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_thirtythirds_mul_thirtythree_above
    {k : ℕ} :
    (-((8734253822779144 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 58)))) * 33 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 55))) := by
  rw [show
      (-((8734253822779144 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 58)))) * 33 =
        -(((8734253822779144 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 58))) * 33) by
    ring]
  rw [problem2_10_ieeeDouble_rounded_two_pow_thirtythirds_mul_thirtythree_above]

/-- Exact product audit for denominator `65`: after the rounded division has
stored the upper IEEE-double approximation to `(2^k)/65`, multiplying by `65`
lands one quarter of an ulp above `2^k`. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_sixtyfifths_mul_sixtyfive_above
    {k : ℕ} :
    ((8868626958514208 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 59))) * 65 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 54)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 59)) * (2 : ℝ) ^ (59 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 59)) (59 : ℤ)
    have hexp : ((k : ℤ) - 59) + 59 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 54)) =
        (2 : ℝ) ^ (((k : ℤ) - 59)) * 32 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 59)) (5 : ℤ)
    have hexp : ((k : ℤ) - 59) + 5 = (k : ℤ) - 54 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 54)) =
          (2 : ℝ) ^ (((k : ℤ) - 59)) * (2 : ℝ) ^ (5 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 59)) * 32 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`65`, power-of-two second
operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_sixtyfifths_mul_sixtyfive_above
    {k : ℕ} :
    (-((8868626958514208 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 59)))) * 65 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 54))) := by
  rw [show
      (-((8868626958514208 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 59)))) * 65 =
        -(((8868626958514208 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 59))) * 65) by
    ring]
  rw [problem2_10_ieeeDouble_rounded_two_pow_sixtyfifths_mul_sixtyfive_above]

/-- Exact product audit for denominator `129`: after the rounded division has
stored the lower IEEE-double approximation to `(2^k)/129`, multiplying by
`129` lands one sixteenth of an ulp below `2^k`. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_onehundredtwentyninths_mul_onehundredtwentynine_below
    {k : ℕ} :
    ((8937376004704240 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 60))) * 129 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 56)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 60)) * (2 : ℝ) ^ (60 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 60)) (60 : ℤ)
    have hexp : ((k : ℤ) - 60) + 60 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 56)) =
        (2 : ℝ) ^ (((k : ℤ) - 60)) * 16 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 60)) (4 : ℤ)
    have hexp : ((k : ℤ) - 60) + 4 = (k : ℤ) - 56 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 56)) =
          (2 : ℝ) ^ (((k : ℤ) - 60)) * (2 : ℝ) ^ (4 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 60)) * 16 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`129`, power-of-two second
operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_onehundredtwentyninths_mul_onehundredtwentynine_below
    {k : ℕ} :
    (-((8937376004704240 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 60)))) * 129 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 56))) := by
  rw [show
      (-((8937376004704240 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 60)))) * 129 =
        -(((8937376004704240 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 60))) * 129) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_onehundredtwentyninths_mul_onehundredtwentynine_below]

/-- Exact product audit for denominator `257`: after the rounded division has
stored the upper IEEE-double approximation to `(2^k)/257`, multiplying by
`257` lands one sixteenth of an ulp above `2^k`. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_twohundredfiftysevenths_mul_twohundredfiftyseven_above
    {k : ℕ} :
    ((8972151786823712 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 61))) * 257 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 56)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 61)) * (2 : ℝ) ^ (61 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 61)) (61 : ℤ)
    have hexp : ((k : ℤ) - 61) + 61 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 56)) =
        (2 : ℝ) ^ (((k : ℤ) - 61)) * 32 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 61)) (5 : ℤ)
    have hexp : ((k : ℤ) - 61) + 5 = (k : ℤ) - 56 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 56)) =
          (2 : ℝ) ^ (((k : ℤ) - 61)) * (2 : ℝ) ^ (5 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 61)) * 32 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`257`, power-of-two second
operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_twohundredfiftysevenths_mul_twohundredfiftyseven_above
    {k : ℕ} :
    (-((8972151786823712 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 61)))) * 257 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 56))) := by
  rw [show
      (-((8972151786823712 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 61)))) * 257 =
        -(((8972151786823712 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 61))) * 257) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_twohundredfiftysevenths_mul_twohundredfiftyseven_above]

/-- Exact product audit for denominator `513`: after the rounded division has
stored the lower IEEE-double approximation to `(2^k)/513`, multiplying by
`513` lands at the midpoint below `2^k`. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_fivehundredthirteenths_mul_fivehundredthirteen_midpoint
    {k : ℕ} :
    ((8989641361456896 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 62))) * 513 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 54)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 62)) * (2 : ℝ) ^ (62 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 62)) (62 : ℤ)
    have hexp : ((k : ℤ) - 62) + 62 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 54)) =
        (2 : ℝ) ^ (((k : ℤ) - 62)) * 256 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 62)) (8 : ℤ)
    have hexp : ((k : ℤ) - 62) + 8 = (k : ℤ) - 54 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 54)) =
          (2 : ℝ) ^ (((k : ℤ) - 62)) * (2 : ℝ) ^ (8 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 62)) * 256 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`513`, power-of-two second
operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_fivehundredthirteenths_mul_fivehundredthirteen_midpoint
    {k : ℕ} :
    (-((8989641361456896 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 62)))) * 513 =
      -((2 : ℝ) ^ k) + (2 : ℝ) ^ (((k : ℤ) - 54)) := by
  rw [show
      (-((8989641361456896 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 62)))) * 513 =
        -(((8989641361456896 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 62))) * 513) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_fivehundredthirteenths_mul_fivehundredthirteen_midpoint]
  ring

/-- Exact product audit for denominator `1025`: after the rounded division has
stored the lower IEEE-double approximation to `(2^k)/1025`, multiplying by
`1025` lands strictly below `2^k` but closer to it than to the previous double. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_onethousandtwentyfifths_mul_onethousandtwentyfive_below
    {k : ℕ} :
    ((8998411743272952 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 63))) * 1025 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 60)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 63)) * (2 : ℝ) ^ (63 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 63)) (63 : ℤ)
    have hexp : ((k : ℤ) - 63) + 63 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 60)) =
        (2 : ℝ) ^ (((k : ℤ) - 63)) * 8 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 63)) (3 : ℤ)
    have hexp : ((k : ℤ) - 63) + 3 = (k : ℤ) - 60 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 60)) =
          (2 : ℝ) ^ (((k : ℤ) - 63)) * (2 : ℝ) ^ (3 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 63)) * 8 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`1025`, power-of-two second
operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_onethousandtwentyfifths_mul_onethousandtwentyfive_below
    {k : ℕ} :
    (-((8998411743272952 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 63)))) * 1025 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 60))) := by
  rw [show
      (-((8998411743272952 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 63)))) * 1025 =
        -(((8998411743272952 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 63))) * 1025) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_onethousandtwentyfifths_mul_onethousandtwentyfive_below]

/-- Exact product audit for denominator `2049`: after the rounded division has
stored the upper IEEE-double approximation to `(2^k)/2049`, multiplying by
`2049` lands above `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_twothousandfortyninths_mul_twothousandfortynine_above
    {k : ℕ} :
    ((9002803354665472 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 64))) * 2049 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 55)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 64)) * (2 : ℝ) ^ (64 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 64)) (64 : ℤ)
    have hexp : ((k : ℤ) - 64) + 64 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 55)) =
        (2 : ℝ) ^ (((k : ℤ) - 64)) * 512 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 64)) (9 : ℤ)
    have hexp : ((k : ℤ) - 64) + 9 = (k : ℤ) - 55 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 55)) =
          (2 : ℝ) ^ (((k : ℤ) - 64)) * (2 : ℝ) ^ (9 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 64)) * 512 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`2049`, power-of-two second
operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_twothousandfortyninths_mul_twothousandfortynine_above
    {k : ℕ} :
    (-((9002803354665472 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 64)))) * 2049 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 55))) := by
  rw [show
      (-((9002803354665472 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 64)))) * 2049 =
        -(((9002803354665472 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 64))) * 2049) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_twothousandfortyninths_mul_twothousandfortynine_above]

/-- Exact product audit for denominator `4097`: after the rounded division has
stored the upper IEEE-double approximation to `(2^k)/4097`, multiplying by
`4097` lands above `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_fourthousandninetysevenths_mul_fourthousandninetyseven_above
    {k : ℕ} :
    ((9005000768225312 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 65))) * 4097 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 60)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 65)) * (2 : ℝ) ^ (65 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 65)) (65 : ℤ)
    have hexp : ((k : ℤ) - 65) + 65 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 60)) =
        (2 : ℝ) ^ (((k : ℤ) - 65)) * 32 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 65)) (5 : ℤ)
    have hexp : ((k : ℤ) - 65) + 5 = (k : ℤ) - 60 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 60)) =
          (2 : ℝ) ^ (((k : ℤ) - 65)) * (2 : ℝ) ^ (5 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 65)) * 32 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`4097`, power-of-two second
operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_fourthousandninetysevenths_mul_fourthousandninetyseven_above
    {k : ℕ} :
    (-((9005000768225312 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 65)))) * 4097 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 60))) := by
  rw [show
      (-((9005000768225312 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 65)))) * 4097 =
        -(((9005000768225312 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 65))) * 4097) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_fourthousandninetysevenths_mul_fourthousandninetyseven_above]

/-- Exact product audit for denominator `8193`: after the rounded division has
stored the upper IEEE-double approximation to `(2^k)/8193`, multiplying by
`8193` lands above `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_eightthousandonehundredninetythirds_mul_eightthousandonehundredninetythree_above
    {k : ℕ} :
    ((9006099877314562 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 66))) * 8193 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 65)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 66)) * (2 : ℝ) ^ (66 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 66)) (66 : ℤ)
    have hexp : ((k : ℤ) - 66) + 66 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 65)) =
        (2 : ℝ) ^ (((k : ℤ) - 66)) * 2 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 66)) (1 : ℤ)
    have hexp : ((k : ℤ) - 66) + 1 = (k : ℤ) - 65 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 65)) =
          (2 : ℝ) ^ (((k : ℤ) - 66)) * (2 : ℝ) ^ (1 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 66)) * 2 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`8193`, power-of-two second
operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_eightthousandonehundredninetythirds_mul_eightthousandonehundredninetythree_above
    {k : ℕ} :
    (-((9006099877314562 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 66)))) * 8193 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 65))) := by
  rw [show
      (-((9006099877314562 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 66)))) * 8193 =
        -(((9006099877314562 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 66))) * 8193) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_eightthousandonehundredninetythirds_mul_eightthousandonehundredninetythree_above]

/-- Exact product audit for denominator `16385`: after the rounded division
has stored the lower IEEE-double approximation to `(2^k)/16385`, multiplying
by `16385` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_sixteenthousandthreehundredeightyfifths_mul_sixteenthousandthreehundredeightyfive_below
    {k : ℕ} :
    ((9006649532479488 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 67))) * 16385 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 56)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 67)) * (2 : ℝ) ^ (67 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 67)) (67 : ℤ)
    have hexp : ((k : ℤ) - 67) + 67 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 56)) =
        (2 : ℝ) ^ (((k : ℤ) - 67)) * 2048 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 67)) (11 : ℤ)
    have hexp : ((k : ℤ) - 67) + 11 = (k : ℤ) - 56 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 56)) =
          (2 : ℝ) ^ (((k : ℤ) - 67)) * (2 : ℝ) ^ (11 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 67)) * 2048 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`16385`, power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_sixteenthousandthreehundredeightyfifths_mul_sixteenthousandthreehundredeightyfive_below
    {k : ℕ} :
    (-((9006649532479488 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 67)))) * 16385 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 56))) := by
  rw [show
      (-((9006649532479488 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 67)))) * 16385 =
        -(((9006649532479488 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 67))) * 16385) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_sixteenthousandthreehundredeightyfifths_mul_sixteenthousandthreehundredeightyfive_below]

/-- Exact product audit for denominator `32769`: after the rounded division
has stored the lower IEEE-double approximation to `(2^k)/32769`, multiplying
by `32769` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_thirtytwothousandsevenhundredsixtyninths_mul_thirtytwothousandsevenhundredsixtynine_below
    {k : ℕ} :
    ((9006924385222400 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 68))) * 32769 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 60)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 68)) * (2 : ℝ) ^ (68 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 68)) (68 : ℤ)
    have hexp : ((k : ℤ) - 68) + 68 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 60)) =
        (2 : ℝ) ^ (((k : ℤ) - 68)) * 256 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 68)) (8 : ℤ)
    have hexp : ((k : ℤ) - 68) + 8 = (k : ℤ) - 60 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 60)) =
          (2 : ℝ) ^ (((k : ℤ) - 68)) * (2 : ℝ) ^ (8 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 68)) * 256 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`32769`, power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_thirtytwothousandsevenhundredsixtyninths_mul_thirtytwothousandsevenhundredsixtynine_below
    {k : ℕ} :
    (-((9006924385222400 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 68)))) * 32769 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 60))) := by
  rw [show
      (-((9006924385222400 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 68)))) * 32769 =
        -(((9006924385222400 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 68))) * 32769) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_thirtytwothousandsevenhundredsixtyninths_mul_thirtytwothousandsevenhundredsixtynine_below]

/-- Exact product audit for denominator `65537`: after the rounded division
has stored the lower IEEE-double approximation to `(2^k)/65537`, multiplying
by `65537` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_sixtyfivethousandfivehundredthirtysevenths_mul_sixtyfivethousandfivehundredthirtyseven_below
    {k : ℕ} :
    ((9007061817884640 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 69))) * 65537 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 64)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 69)) * (2 : ℝ) ^ (69 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 69)) (69 : ℤ)
    have hexp : ((k : ℤ) - 69) + 69 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 64)) =
        (2 : ℝ) ^ (((k : ℤ) - 69)) * 32 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 69)) (5 : ℤ)
    have hexp : ((k : ℤ) - 69) + 5 = (k : ℤ) - 64 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 64)) =
          (2 : ℝ) ^ (((k : ℤ) - 69)) * (2 : ℝ) ^ (5 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 69)) * 32 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`65537`, power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_sixtyfivethousandfivehundredthirtysevenths_mul_sixtyfivethousandfivehundredthirtyseven_below
    {k : ℕ} :
    (-((9007061817884640 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 69)))) * 65537 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 64))) := by
  rw [show
      (-((9007061817884640 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 69)))) * 65537 =
        -(((9007061817884640 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 69))) * 65537) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_sixtyfivethousandfivehundredthirtysevenths_mul_sixtyfivethousandfivehundredthirtyseven_below]

/-- Exact product audit for denominator `131073`: after the rounded division
has stored the lower IEEE-double approximation to `(2^k)/131073`, multiplying
by `131073` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_onehundredthirtyonethousandseventythirds_mul_onehundredthirtyonethousandseventythree_below
    {k : ℕ} :
    ((9007130535788540 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 70))) * 131073 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 68)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 70)) * (2 : ℝ) ^ (70 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 70)) (70 : ℤ)
    have hexp : ((k : ℤ) - 70) + 70 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 68)) =
        (2 : ℝ) ^ (((k : ℤ) - 70)) * 4 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 70)) (2 : ℤ)
    have hexp : ((k : ℤ) - 70) + 2 = (k : ℤ) - 68 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 68)) =
          (2 : ℝ) ^ (((k : ℤ) - 70)) * (2 : ℝ) ^ (2 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 70)) * 4 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`131073`, power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_onehundredthirtyonethousandseventythirds_mul_onehundredthirtyonethousandseventythree_below
    {k : ℕ} :
    (-((9007130535788540 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 70)))) * 131073 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 68))) := by
  rw [show
      (-((9007130535788540 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 70)))) * 131073 =
        -(((9007130535788540 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 70))) * 131073) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_onehundredthirtyonethousandseventythirds_mul_onehundredthirtyonethousandseventythree_below]

/-- Exact product audit for denominator `262145`: after the rounded division
has stored the upper IEEE-double approximation to `(2^k)/262145`, multiplying
by `262145` lands above `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_twohundredsixtytwothousandonehundredfortyfifths_mul_twohundredsixtytwothousandonehundredfortyfive_above
    {k : ℕ} :
    ((9007164895133696 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 71))) * 262145 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 54)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 71)) * (2 : ℝ) ^ (71 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 71)) (71 : ℤ)
    have hexp : ((k : ℤ) - 71) + 71 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 54)) =
        (2 : ℝ) ^ (((k : ℤ) - 71)) * 131072 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 71)) (17 : ℤ)
    have hexp : ((k : ℤ) - 71) + 17 = (k : ℤ) - 54 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 54)) =
          (2 : ℝ) ^ (((k : ℤ) - 71)) * (2 : ℝ) ^ (17 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 71)) * 131072 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`262145`, power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_twohundredsixtytwothousandonehundredfortyfifths_mul_twohundredsixtytwothousandonehundredfortyfive_above
    {k : ℕ} :
    (-((9007164895133696 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 71)))) * 262145 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 54))) := by
  rw [show
      (-((9007164895133696 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 71)))) * 262145 =
        -(((9007164895133696 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 71))) * 262145) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_twohundredsixtytwothousandonehundredfortyfifths_mul_twohundredsixtytwothousandonehundredfortyfive_above]

/-- Exact product audit for denominator `524289`: after the rounded division
has stored the upper IEEE-double approximation to `(2^k)/524289`, multiplying
by `524289` lands above `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_fivehundredtwentyfourthousandtwohundredeightyninths_mul_fivehundredtwentyfourthousandtwohundredeightynine_above
    {k : ℕ} :
    ((9007182074904576 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 72))) * 524289 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 57)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 72)) * (2 : ℝ) ^ (72 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 72)) (72 : ℤ)
    have hexp : ((k : ℤ) - 72) + 72 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 57)) =
        (2 : ℝ) ^ (((k : ℤ) - 72)) * 32768 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 72)) (15 : ℤ)
    have hexp : ((k : ℤ) - 72) + 15 = (k : ℤ) - 57 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 57)) =
          (2 : ℝ) ^ (((k : ℤ) - 72)) * (2 : ℝ) ^ (15 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 72)) * 32768 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`524289`, power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_fivehundredtwentyfourthousandtwohundredeightyninths_mul_fivehundredtwentyfourthousandtwohundredeightynine_above
    {k : ℕ} :
    (-((9007182074904576 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 72)))) * 524289 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 57))) := by
  rw [show
      (-((9007182074904576 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 72)))) * 524289 =
        -(((9007182074904576 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 72))) * 524289) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_fivehundredtwentyfourthousandtwohundredeightyninths_mul_fivehundredtwentyfourthousandtwohundredeightynine_above]

/-- Exact product audit for denominator `1048577`: after the rounded division
has stored the upper IEEE-double approximation to `(2^k)/1048577`, multiplying
by `1048577` lands above `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_onemillionfortyeightthousandfivehundredseventysevenths_mul_onemillionfortyeightthousandfivehundredseventyseven_above
    {k : ℕ} :
    ((9007190664814592 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 73))) * 1048577 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 60)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 73)) * (2 : ℝ) ^ (73 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 73)) (73 : ℤ)
    have hexp : ((k : ℤ) - 73) + 73 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 60)) =
        (2 : ℝ) ^ (((k : ℤ) - 73)) * 8192 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 73)) (13 : ℤ)
    have hexp : ((k : ℤ) - 73) + 13 = (k : ℤ) - 60 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 60)) =
          (2 : ℝ) ^ (((k : ℤ) - 73)) * (2 : ℝ) ^ (13 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 73)) * 8192 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`1048577`, power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_onemillionfortyeightthousandfivehundredseventysevenths_mul_onemillionfortyeightthousandfivehundredseventyseven_above
    {k : ℕ} :
    (-((9007190664814592 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 73)))) * 1048577 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 60))) := by
  rw [show
      (-((9007190664814592 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 73)))) * 1048577 =
        -(((9007190664814592 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 73))) * 1048577) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_onemillionfortyeightthousandfivehundredseventysevenths_mul_onemillionfortyeightthousandfivehundredseventyseven_above]

/-- Exact product audit for denominator `2097153`: after the rounded division
has stored the upper IEEE-double approximation to `(2^k)/2097153`, multiplying
by `2097153` lands above `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_twomillionninetyseventhousandonehundredfiftythirds_mul_twomillionninetyseventhousandonehundredfiftythree_above
    {k : ℕ} :
    ((9007194959775744 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 74))) * 2097153 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 63)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 74)) * (2 : ℝ) ^ (74 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 74)) (74 : ℤ)
    have hexp : ((k : ℤ) - 74) + 74 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 63)) =
        (2 : ℝ) ^ (((k : ℤ) - 74)) * 2048 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 74)) (11 : ℤ)
    have hexp : ((k : ℤ) - 74) + 11 = (k : ℤ) - 63 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 63)) =
          (2 : ℝ) ^ (((k : ℤ) - 74)) * (2 : ℝ) ^ (11 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 74)) * 2048 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`2097153`, power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_twomillionninetyseventhousandonehundredfiftythirds_mul_twomillionninetyseventhousandonehundredfiftythree_above
    {k : ℕ} :
    (-((9007194959775744 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 74)))) * 2097153 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 63))) := by
  rw [show
      (-((9007194959775744 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 74)))) * 2097153 =
        -(((9007194959775744 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 74))) * 2097153) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_twomillionninetyseventhousandonehundredfiftythirds_mul_twomillionninetyseventhousandonehundredfiftythree_above]

/-- Exact product audit for denominator `4194305`: after the rounded division
has stored the upper IEEE-double approximation to `(2^k)/4194305`, multiplying
by `4194305` lands above `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_fourmilliononehundredninetyfourthousandthreehundredfifths_mul_fourmilliononehundredninetyfourthousandthreehundredfive_above
    {k : ℕ} :
    ((9007197107257856 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 75))) * 4194305 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 66)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 75)) * (2 : ℝ) ^ (75 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 75)) (75 : ℤ)
    have hexp : ((k : ℤ) - 75) + 75 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 66)) =
        (2 : ℝ) ^ (((k : ℤ) - 75)) * 512 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 75)) (9 : ℤ)
    have hexp : ((k : ℤ) - 75) + 9 = (k : ℤ) - 66 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 66)) =
          (2 : ℝ) ^ (((k : ℤ) - 75)) * (2 : ℝ) ^ (9 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 75)) * 512 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`4194305`, power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_fourmilliononehundredninetyfourthousandthreehundredfifths_mul_fourmilliononehundredninetyfourthousandthreehundredfive_above
    {k : ℕ} :
    (-((9007197107257856 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 75)))) * 4194305 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 66))) := by
  rw [show
      (-((9007197107257856 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 75)))) * 4194305 =
        -(((9007197107257856 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 75))) * 4194305) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_fourmilliononehundredninetyfourthousandthreehundredfifths_mul_fourmilliononehundredninetyfourthousandthreehundredfive_above]

/-- Exact product audit for denominator `8388609`: after the rounded division
has stored the upper IEEE-double approximation to `(2^k)/8388609`, multiplying
by `8388609` lands above `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_eightmillionthreehundredeightyeightthousandsixhundredninths_mul_eightmillionthreehundredeightyeightthousandsixhundrednine_above
    {k : ℕ} :
    ((9007198180999296 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 76))) * 8388609 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 69)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 76)) * (2 : ℝ) ^ (76 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 76)) (76 : ℤ)
    have hexp : ((k : ℤ) - 76) + 76 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 69)) =
        (2 : ℝ) ^ (((k : ℤ) - 76)) * 128 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 76)) (7 : ℤ)
    have hexp : ((k : ℤ) - 76) + 7 = (k : ℤ) - 69 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 69)) =
          (2 : ℝ) ^ (((k : ℤ) - 76)) * (2 : ℝ) ^ (7 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 76)) * 128 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`8388609`, power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_eightmillionthreehundredeightyeightthousandsixhundredninths_mul_eightmillionthreehundredeightyeightthousandsixhundrednine_above
    {k : ℕ} :
    (-((9007198180999296 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 76)))) * 8388609 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 69))) := by
  rw [show
      (-((9007198180999296 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 76)))) * 8388609 =
        -(((9007198180999296 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 76))) * 8388609) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_eightmillionthreehundredeightyeightthousandsixhundredninths_mul_eightmillionthreehundredeightyeightthousandsixhundrednine_above]

/-- Exact product audit for denominator `16777217`: after the rounded division
has stored the upper IEEE-double approximation to `(2^k)/16777217`,
multiplying by `16777217` lands above `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeenths_mul_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeen_above
    {k : ℕ} :
    ((9007198717870112 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 77))) * 16777217 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 72)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 77)) * (2 : ℝ) ^ (77 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 77)) (77 : ℤ)
    have hexp : ((k : ℤ) - 77) + 77 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 72)) =
        (2 : ℝ) ^ (((k : ℤ) - 77)) * 32 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 77)) (5 : ℤ)
    have hexp : ((k : ℤ) - 77) + 5 = (k : ℤ) - 72 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 72)) =
          (2 : ℝ) ^ (((k : ℤ) - 77)) * (2 : ℝ) ^ (5 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 77)) * 32 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`16777217`, power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeenths_mul_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeen_above
    {k : ℕ} :
    (-((9007198717870112 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 77)))) * 16777217 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 72))) := by
  rw [show
      (-((9007198717870112 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 77)))) * 16777217 =
        -(((9007198717870112 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 77))) * 16777217) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeenths_mul_sixteenmillionsevenhundredseventyseventhousandtwohundredseventeen_above]

/-- Exact product audit for denominator `33554433`: after the rounded division
has stored the upper IEEE-double approximation to `(2^k)/33554433`,
multiplying by `33554433` lands above `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythirds_mul_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythree_above
    {k : ℕ} :
    ((9007198986305544 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 78))) * 33554433 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 75)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 78)) * (2 : ℝ) ^ (78 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 78)) (78 : ℤ)
    have hexp : ((k : ℤ) - 78) + 78 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 75)) =
        (2 : ℝ) ^ (((k : ℤ) - 78)) * 8 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 78)) (3 : ℤ)
    have hexp : ((k : ℤ) - 78) + 3 = (k : ℤ) - 75 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 75)) =
          (2 : ℝ) ^ (((k : ℤ) - 78)) * (2 : ℝ) ^ (3 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 78)) * 8 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`33554433`, power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythirds_mul_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythree_above
    {k : ℕ} :
    (-((9007198986305544 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 78)))) * 33554433 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 75))) := by
  rw [show
      (-((9007198986305544 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 78)))) * 33554433 =
        -(((9007198986305544 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 78))) * 33554433) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythirds_mul_thirtythreemillionfivehundredfiftyfourthousandfourhundredthirtythree_above]

/-- Exact product audit for denominator `67108865`: after the rounded division
has stored the upper IEEE-double approximation to `(2^k)/67108865`,
multiplying by `67108865` lands above `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_sixtysevenmilliononehundredeightthousandeighthundredsixtyfifths_mul_sixtysevenmilliononehundredeightthousandeighthundredsixtyfive_above
    {k : ℕ} :
    ((9007199120523266 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 79))) * 67108865 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 78)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 79)) * (2 : ℝ) ^ (79 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 79)) (79 : ℤ)
    have hexp : ((k : ℤ) - 79) + 79 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 78)) =
        (2 : ℝ) ^ (((k : ℤ) - 79)) * 2 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 79)) (1 : ℤ)
    have hexp : ((k : ℤ) - 79) + 1 = (k : ℤ) - 78 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 78)) =
          (2 : ℝ) ^ (((k : ℤ) - 79)) * (2 : ℝ) ^ (1 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 79)) * 2 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`67108865`, power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_sixtysevenmilliononehundredeightthousandeighthundredsixtyfifths_mul_sixtysevenmilliononehundredeightthousandeighthundredsixtyfive_above
    {k : ℕ} :
    (-((9007199120523266 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 79)))) * 67108865 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 78))) := by
  rw [show
      (-((9007199120523266 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 79)))) * 67108865 =
        -(((9007199120523266 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 79))) * 67108865) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_sixtysevenmilliononehundredeightthousandeighthundredsixtyfifths_mul_sixtysevenmilliononehundredeightthousandeighthundredsixtyfive_above]

/-- Exact product audit for denominator `134217729`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/134217729`,
multiplying by `134217729` lands at the midpoint immediately below `2^k`. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentyninths_mul_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentynine_midpoint
    {k : ℕ} :
    ((9007199187632128 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 80))) * 134217729 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 54)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 80)) * (2 : ℝ) ^ (80 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 80)) (80 : ℤ)
    have hexp : ((k : ℤ) - 80) + 80 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 54)) =
        (2 : ℝ) ^ (((k : ℤ) - 80)) * 67108864 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 80)) (26 : ℤ)
    have hexp : ((k : ℤ) - 80) + 26 = (k : ℤ) - 54 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 54)) =
          (2 : ℝ) ^ (((k : ℤ) - 80)) * (2 : ℝ) ^ (26 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 80)) * 67108864 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`134217729`, power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentyninths_mul_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentynine_midpoint
    {k : ℕ} :
    (-((9007199187632128 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 80)))) * 134217729 =
      -((2 : ℝ) ^ k) + (2 : ℝ) ^ (((k : ℤ) - 54)) := by
  rw [show
      (-((9007199187632128 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 80)))) * 134217729 =
        -(((9007199187632128 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 80))) * 134217729) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentyninths_mul_onehundredthirtyfourmilliontwohundredseventeenthousandsevenhundredtwentynine_midpoint]
  ring

/-- Exact product audit for denominator `268435457`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/268435457`,
multiplying by `268435457` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftysevenths_mul_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftyseven_below
    {k : ℕ} :
    ((9007199221186560 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 81))) * 268435457 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 56)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 81)) * (2 : ℝ) ^ (81 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 81)) (81 : ℤ)
    have hexp : ((k : ℤ) - 81) + 81 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 56)) =
        (2 : ℝ) ^ (((k : ℤ) - 81)) * 33554432 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 81)) (25 : ℤ)
    have hexp : ((k : ℤ) - 81) + 25 = (k : ℤ) - 56 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 56)) =
          (2 : ℝ) ^ (((k : ℤ) - 81)) * (2 : ℝ) ^ (25 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 81)) * 33554432 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`268435457`, power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftysevenths_mul_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftyseven_below
    {k : ℕ} :
    (-((9007199221186560 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 81)))) * 268435457 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 56))) := by
  rw [show
      (-((9007199221186560 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 81)))) * 268435457 =
        -(((9007199221186560 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 81))) * 268435457) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftysevenths_mul_twohundredsixtyeightmillionfourhundredthirtyfivethousandfourhundredfiftyseven_below]

/-- Exact product audit for denominator `536870913`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/536870913`,
multiplying by `536870913` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteenths_mul_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteen_below
    {k : ℕ} :
    ((9007199237963776 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 82))) * 536870913 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 58)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 82)) * (2 : ℝ) ^ (82 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 82)) (82 : ℤ)
    have hexp : ((k : ℤ) - 82) + 82 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 58)) =
        (2 : ℝ) ^ (((k : ℤ) - 82)) * 16777216 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 82)) (24 : ℤ)
    have hexp : ((k : ℤ) - 82) + 24 = (k : ℤ) - 58 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 58)) =
          (2 : ℝ) ^ (((k : ℤ) - 82)) * (2 : ℝ) ^ (24 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 82)) * 16777216 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`536870913`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteenths_mul_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteen_below
    {k : ℕ} :
    (-((9007199237963776 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 82)))) * 536870913 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 58))) := by
  rw [show
      (-((9007199237963776 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 82)))) * 536870913 =
        -(((9007199237963776 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 82))) * 536870913) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteenths_mul_fivehundredthirtysixmillioneighthundredseventythousandninehundredthirteen_below]

/-- Exact product audit for denominator `1073741825`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/1073741825`,
multiplying by `1073741825` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfifths_mul_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfive_below
    {k : ℕ} :
    ((9007199246352384 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 83))) * 1073741825 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 60)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 83)) * (2 : ℝ) ^ (83 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 83)) (83 : ℤ)
    have hexp : ((k : ℤ) - 83) + 83 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 60)) =
        (2 : ℝ) ^ (((k : ℤ) - 83)) * 8388608 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 83)) (23 : ℤ)
    have hexp : ((k : ℤ) - 83) + 23 = (k : ℤ) - 60 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 60)) =
          (2 : ℝ) ^ (((k : ℤ) - 83)) * (2 : ℝ) ^ (23 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 83)) * 8388608 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`1073741825`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfifths_mul_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfive_below
    {k : ℕ} :
    (-((9007199246352384 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 83)))) * 1073741825 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 60))) := by
  rw [show
      (-((9007199246352384 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 83)))) * 1073741825 =
        -(((9007199246352384 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 83))) * 1073741825) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfifths_mul_onebillionseventythreemillionsevenhundredfortyonethousandeighthundredtwentyfive_below]

/-- Exact product audit for denominator `2147483649`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/2147483649`,
multiplying by `2147483649` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortyninths_mul_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortynine_below
    {k : ℕ} :
    ((9007199250546688 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 84))) * 2147483649 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 62)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 84)) * (2 : ℝ) ^ (84 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 84)) (84 : ℤ)
    have hexp : ((k : ℤ) - 84) + 84 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 62)) =
        (2 : ℝ) ^ (((k : ℤ) - 84)) * 4194304 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 84)) (22 : ℤ)
    have hexp : ((k : ℤ) - 84) + 22 = (k : ℤ) - 62 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 62)) =
          (2 : ℝ) ^ (((k : ℤ) - 84)) * (2 : ℝ) ^ (22 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 84)) * 4194304 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`2147483649`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortyninths_mul_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortynine_below
    {k : ℕ} :
    (-((9007199250546688 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 84)))) * 2147483649 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 62))) := by
  rw [show
      (-((9007199250546688 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 84)))) * 2147483649 =
        -(((9007199250546688 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 84))) * 2147483649) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortyninths_mul_twobilliononehundredfortysevenmillionfourhundredeightythreethousandsixhundredfortynine_below]

/-- Exact product audit for denominator `4294967297`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/4294967297`,
multiplying by `4294967297` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetysevenths_mul_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetyseven_below
    {k : ℕ} :
    ((9007199252643840 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 85))) * 4294967297 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 64)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 85)) * (2 : ℝ) ^ (85 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 85)) (85 : ℤ)
    have hexp : ((k : ℤ) - 85) + 85 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 64)) =
        (2 : ℝ) ^ (((k : ℤ) - 85)) * 2097152 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 85)) (21 : ℤ)
    have hexp : ((k : ℤ) - 85) + 21 = (k : ℤ) - 64 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 64)) =
          (2 : ℝ) ^ (((k : ℤ) - 85)) * (2 : ℝ) ^ (21 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 85)) * 2097152 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`4294967297`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetysevenths_mul_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetyseven_below
    {k : ℕ} :
    (-((9007199252643840 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 85)))) * 4294967297 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 64))) := by
  rw [show
      (-((9007199252643840 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 85)))) * 4294967297 =
        -(((9007199252643840 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 85))) * 4294967297) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetysevenths_mul_fourbilliontwohundredninetyfourmillionninehundredsixtyseventhousandtwohundredninetyseven_below]

/-- Exact product audit for denominator `8589934593`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/8589934593`,
multiplying by `8589934593` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythirds_mul_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythree_below
    {k : ℕ} :
    ((9007199253692416 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 86))) * 8589934593 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 66)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 86)) * (2 : ℝ) ^ (86 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 86)) (86 : ℤ)
    have hexp : ((k : ℤ) - 86) + 86 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 66)) =
        (2 : ℝ) ^ (((k : ℤ) - 86)) * 1048576 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 86)) (20 : ℤ)
    have hexp : ((k : ℤ) - 86) + 20 = (k : ℤ) - 66 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 66)) =
          (2 : ℝ) ^ (((k : ℤ) - 86)) * (2 : ℝ) ^ (20 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 86)) * 1048576 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`8589934593`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythirds_mul_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythree_below
    {k : ℕ} :
    (-((9007199253692416 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 86)))) * 8589934593 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 66))) := by
  rw [show
      (-((9007199253692416 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 86)))) * 8589934593 =
        -(((9007199253692416 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 86))) * 8589934593) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythirds_mul_eightbillionfivehundredeightyninemillionninehundredthirtyfourthousandfivehundredninetythree_below]

/-- Exact product audit for denominator `17179869185`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/17179869185`,
multiplying by `17179869185` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfifths_mul_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfive_below
    {k : ℕ} :
    ((9007199254216704 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 87))) * 17179869185 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 68)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 87)) * (2 : ℝ) ^ (87 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 87)) (87 : ℤ)
    have hexp : ((k : ℤ) - 87) + 87 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 68)) =
        (2 : ℝ) ^ (((k : ℤ) - 87)) * 524288 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 87)) (19 : ℤ)
    have hexp : ((k : ℤ) - 87) + 19 = (k : ℤ) - 68 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 68)) =
          (2 : ℝ) ^ (((k : ℤ) - 87)) * (2 : ℝ) ^ (19 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 87)) * 524288 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`17179869185`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfifths_mul_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfive_below
    {k : ℕ} :
    (-((9007199254216704 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 87)))) * 17179869185 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 68))) := by
  rw [show
      (-((9007199254216704 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 87)))) * 17179869185 =
        -(((9007199254216704 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 87))) * 17179869185) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfifths_mul_seventeenbilliononehundredseventyninemillioneighthundredsixtyninethousandonehundredeightyfive_below]

/-- Exact product audit for denominator `34359738369`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/34359738369`,
multiplying by `34359738369` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtyninths_mul_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtynine_below
    {k : ℕ} :
    ((9007199254478848 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 88))) * 34359738369 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 70)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 88)) * (2 : ℝ) ^ (88 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 88)) (88 : ℤ)
    have hexp : ((k : ℤ) - 88) + 88 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 70)) =
        (2 : ℝ) ^ (((k : ℤ) - 88)) * 262144 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 88)) (18 : ℤ)
    have hexp : ((k : ℤ) - 88) + 18 = (k : ℤ) - 70 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 70)) =
          (2 : ℝ) ^ (((k : ℤ) - 88)) * (2 : ℝ) ^ (18 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 88)) * 262144 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`34359738369`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtyninths_mul_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtynine_below
    {k : ℕ} :
    (-((9007199254478848 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 88)))) * 34359738369 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 70))) := by
  rw [show
      (-((9007199254478848 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 88)))) * 34359738369 =
        -(((9007199254478848 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 88))) * 34359738369) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtyninths_mul_thirtyfourbillionthreehundredfiftyninemillionsevenhundredthirtyeightthousandthreehundredsixtynine_below]

/-- Exact product audit for denominator `68719476737`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/68719476737`,
multiplying by `68719476737` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtysevenths_mul_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtyseven_below
    {k : ℕ} :
    ((9007199254609920 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 89))) * 68719476737 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 72)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 89)) * (2 : ℝ) ^ (89 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 89)) (89 : ℤ)
    have hexp : ((k : ℤ) - 89) + 89 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 72)) =
        (2 : ℝ) ^ (((k : ℤ) - 89)) * 131072 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 89)) (17 : ℤ)
    have hexp : ((k : ℤ) - 89) + 17 = (k : ℤ) - 72 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 72)) =
          (2 : ℝ) ^ (((k : ℤ) - 89)) * (2 : ℝ) ^ (17 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 89)) * 131072 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`68719476737`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtysevenths_mul_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtyseven_below
    {k : ℕ} :
    (-((9007199254609920 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 89)))) * 68719476737 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 72))) := by
  rw [show
      (-((9007199254609920 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 89)))) * 68719476737 =
        -(((9007199254609920 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 89))) * 68719476737) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtysevenths_mul_sixtyeightbillionsevenhundrednineteenmillionfourhundredseventysixthousandsevenhundredthirtyseven_below]

/-- Exact product audit for denominator `137438953473`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/137438953473`,
multiplying by `137438953473` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythirds_mul_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythree_below
    {k : ℕ} :
    ((9007199254675456 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 90))) * 137438953473 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 74)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 90)) * (2 : ℝ) ^ (90 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 90)) (90 : ℤ)
    have hexp : ((k : ℤ) - 90) + 90 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 74)) =
        (2 : ℝ) ^ (((k : ℤ) - 90)) * 65536 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 90)) (16 : ℤ)
    have hexp : ((k : ℤ) - 90) + 16 = (k : ℤ) - 74 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 74)) =
          (2 : ℝ) ^ (((k : ℤ) - 90)) * (2 : ℝ) ^ (16 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 90)) * 65536 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`137438953473`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythirds_mul_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythree_below
    {k : ℕ} :
    (-((9007199254675456 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 90)))) * 137438953473 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 74))) := by
  rw [show
      (-((9007199254675456 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 90)))) * 137438953473 =
        -(((9007199254675456 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 90))) * 137438953473) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythirds_mul_onehundredthirtysevenbillionfourhundredthirtyeightmillionninehundredfiftythreethousandfourhundredseventythree_below]

/-- Exact product audit for denominator `274877906945`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/274877906945`,
multiplying by `274877906945` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfifths_mul_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfive_below
    {k : ℕ} :
    ((9007199254708224 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 91))) * 274877906945 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 76)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 91)) * (2 : ℝ) ^ (91 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 91)) (91 : ℤ)
    have hexp : ((k : ℤ) - 91) + 91 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 76)) =
        (2 : ℝ) ^ (((k : ℤ) - 91)) * 32768 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 91)) (15 : ℤ)
    have hexp : ((k : ℤ) - 91) + 15 = (k : ℤ) - 76 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 76)) =
          (2 : ℝ) ^ (((k : ℤ) - 91)) * (2 : ℝ) ^ (15 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 91)) * 32768 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`274877906945`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfifths_mul_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfive_below
    {k : ℕ} :
    (-((9007199254708224 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 91)))) * 274877906945 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 76))) := by
  rw [show
      (-((9007199254708224 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 91)))) * 274877906945 =
        -(((9007199254708224 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 91))) * 274877906945) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfifths_mul_twohundredseventyfourbillioneighthundredseventysevenmillionninehundredsixthousandninehundredfortyfive_below]

/-- Exact product audit for denominator `549755813889`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/549755813889`,
multiplying by `549755813889` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightyninths_mul_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightynine_below
    {k : ℕ} :
    ((9007199254724608 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 92))) * 549755813889 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 78)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 92)) * (2 : ℝ) ^ (92 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 92)) (92 : ℤ)
    have hexp : ((k : ℤ) - 92) + 92 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 78)) =
        (2 : ℝ) ^ (((k : ℤ) - 92)) * 16384 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 92)) (14 : ℤ)
    have hexp : ((k : ℤ) - 92) + 14 = (k : ℤ) - 78 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 78)) =
          (2 : ℝ) ^ (((k : ℤ) - 92)) * (2 : ℝ) ^ (14 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 92)) * 16384 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`549755813889`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightyninths_mul_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightynine_below
    {k : ℕ} :
    (-((9007199254724608 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 92)))) * 549755813889 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 78))) := by
  rw [show
      (-((9007199254724608 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 92)))) * 549755813889 =
        -(((9007199254724608 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 92))) * 549755813889) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightyninths_mul_fivehundredfortyninebillionsevenhundredfiftyfivemillioneighthundredthirteenthousandeighthundredeightynine_below]

/-- Exact product audit for denominator `1099511627777`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/1099511627777`,
multiplying by `1099511627777` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_plus_one_denominator_mul_two_pow_forty_plus_one_below
    {k : ℕ} :
    ((9007199254732800 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 93))) * 1099511627777 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 80)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 93)) * (2 : ℝ) ^ (93 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 93)) (93 : ℤ)
    have hexp : ((k : ℤ) - 93) + 93 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 80)) =
        (2 : ℝ) ^ (((k : ℤ) - 93)) * 8192 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 93)) (13 : ℤ)
    have hexp : ((k : ℤ) - 93) + 13 = (k : ℤ) - 80 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 80)) =
          (2 : ℝ) ^ (((k : ℤ) - 93)) * (2 : ℝ) ^ (13 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 93)) * 8192 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`1099511627777`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_forty_plus_one_denominator_mul_two_pow_forty_plus_one_below
    {k : ℕ} :
    (-((9007199254732800 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 93)))) * 1099511627777 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 80))) := by
  rw [show
      (-((9007199254732800 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 93)))) * 1099511627777 =
        -(((9007199254732800 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 93))) * 1099511627777) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_plus_one_denominator_mul_two_pow_forty_plus_one_below]

/-- Exact product audit for denominator `2199023255553`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/2199023255553`,
multiplying by `2199023255553` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_one_plus_one_denominator_mul_two_pow_forty_one_plus_one_below
    {k : ℕ} :
    ((9007199254736896 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 94))) * 2199023255553 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 82)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 94)) * (2 : ℝ) ^ (94 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 94)) (94 : ℤ)
    have hexp : ((k : ℤ) - 94) + 94 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 82)) =
        (2 : ℝ) ^ (((k : ℤ) - 94)) * 4096 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 94)) (12 : ℤ)
    have hexp : ((k : ℤ) - 94) + 12 = (k : ℤ) - 82 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 82)) =
          (2 : ℝ) ^ (((k : ℤ) - 94)) * (2 : ℝ) ^ (12 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 94)) * 4096 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`2199023255553`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_forty_one_plus_one_denominator_mul_two_pow_forty_one_plus_one_below
    {k : ℕ} :
    (-((9007199254736896 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 94)))) * 2199023255553 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 82))) := by
  rw [show
      (-((9007199254736896 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 94)))) * 2199023255553 =
        -(((9007199254736896 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 94))) * 2199023255553) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_one_plus_one_denominator_mul_two_pow_forty_one_plus_one_below]

/-- Exact product audit for denominator `4398046511105`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/4398046511105`,
multiplying by `4398046511105` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_two_plus_one_denominator_mul_two_pow_forty_two_plus_one_below
    {k : ℕ} :
    ((9007199254738944 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 95))) * 4398046511105 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 84)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 95)) * (2 : ℝ) ^ (95 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 95)) (95 : ℤ)
    have hexp : ((k : ℤ) - 95) + 95 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 84)) =
        (2 : ℝ) ^ (((k : ℤ) - 95)) * 2048 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 95)) (11 : ℤ)
    have hexp : ((k : ℤ) - 95) + 11 = (k : ℤ) - 84 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 84)) =
          (2 : ℝ) ^ (((k : ℤ) - 95)) * (2 : ℝ) ^ (11 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 95)) * 2048 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`4398046511105`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_forty_two_plus_one_denominator_mul_two_pow_forty_two_plus_one_below
    {k : ℕ} :
    (-((9007199254738944 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 95)))) * 4398046511105 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 84))) := by
  rw [show
      (-((9007199254738944 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 95)))) * 4398046511105 =
        -(((9007199254738944 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 95))) * 4398046511105) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_two_plus_one_denominator_mul_two_pow_forty_two_plus_one_below]

/-- Exact product audit for denominator `8796093022209`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/8796093022209`,
multiplying by `8796093022209` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_three_plus_one_denominator_mul_two_pow_forty_three_plus_one_below
    {k : ℕ} :
    ((9007199254739968 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 96))) * 8796093022209 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 86)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 96)) * (2 : ℝ) ^ (96 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 96)) (96 : ℤ)
    have hexp : ((k : ℤ) - 96) + 96 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 86)) =
        (2 : ℝ) ^ (((k : ℤ) - 96)) * 1024 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 96)) (10 : ℤ)
    have hexp : ((k : ℤ) - 96) + 10 = (k : ℤ) - 86 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 86)) =
          (2 : ℝ) ^ (((k : ℤ) - 96)) * (2 : ℝ) ^ (10 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 96)) * 1024 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`8796093022209`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_forty_three_plus_one_denominator_mul_two_pow_forty_three_plus_one_below
    {k : ℕ} :
    (-((9007199254739968 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 96)))) * 8796093022209 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 86))) := by
  rw [show
      (-((9007199254739968 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 96)))) * 8796093022209 =
        -(((9007199254739968 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 96))) * 8796093022209) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_three_plus_one_denominator_mul_two_pow_forty_three_plus_one_below]

/-- Exact product audit for denominator `17592186044417`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/17592186044417`,
multiplying by `17592186044417` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_four_plus_one_denominator_mul_two_pow_forty_four_plus_one_below
    {k : ℕ} :
    ((9007199254740480 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 97))) * 17592186044417 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 88)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 97)) * (2 : ℝ) ^ (97 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 97)) (97 : ℤ)
    have hexp : ((k : ℤ) - 97) + 97 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 88)) =
        (2 : ℝ) ^ (((k : ℤ) - 97)) * 512 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 97)) (9 : ℤ)
    have hexp : ((k : ℤ) - 97) + 9 = (k : ℤ) - 88 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 88)) =
          (2 : ℝ) ^ (((k : ℤ) - 97)) * (2 : ℝ) ^ (9 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 97)) * 512 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`17592186044417`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_forty_four_plus_one_denominator_mul_two_pow_forty_four_plus_one_below
    {k : ℕ} :
    (-((9007199254740480 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 97)))) * 17592186044417 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 88))) := by
  rw [show
      (-((9007199254740480 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 97)))) * 17592186044417 =
        -(((9007199254740480 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 97))) * 17592186044417) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_four_plus_one_denominator_mul_two_pow_forty_four_plus_one_below]

/-- Exact product audit for denominator `35184372088833`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/35184372088833`,
multiplying by `35184372088833` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_five_plus_one_denominator_mul_two_pow_forty_five_plus_one_below
    {k : ℕ} :
    ((9007199254740736 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 98))) * 35184372088833 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 90)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 98)) * (2 : ℝ) ^ (98 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 98)) (98 : ℤ)
    have hexp : ((k : ℤ) - 98) + 98 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 90)) =
        (2 : ℝ) ^ (((k : ℤ) - 98)) * 256 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 98)) (8 : ℤ)
    have hexp : ((k : ℤ) - 98) + 8 = (k : ℤ) - 90 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 90)) =
          (2 : ℝ) ^ (((k : ℤ) - 98)) * (2 : ℝ) ^ (8 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 98)) * 256 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`35184372088833`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_forty_five_plus_one_denominator_mul_two_pow_forty_five_plus_one_below
    {k : ℕ} :
    (-((9007199254740736 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 98)))) * 35184372088833 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 90))) := by
  rw [show
      (-((9007199254740736 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 98)))) * 35184372088833 =
        -(((9007199254740736 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 98))) * 35184372088833) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_five_plus_one_denominator_mul_two_pow_forty_five_plus_one_below]

/-- Exact product audit for denominator `70368744177665`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/70368744177665`,
multiplying by `70368744177665` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_six_plus_one_denominator_mul_two_pow_forty_six_plus_one_below
    {k : ℕ} :
    ((9007199254740864 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 99))) * 70368744177665 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 92)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 99)) * (2 : ℝ) ^ (99 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 99)) (99 : ℤ)
    have hexp : ((k : ℤ) - 99) + 99 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 92)) =
        (2 : ℝ) ^ (((k : ℤ) - 99)) * 128 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 99)) (7 : ℤ)
    have hexp : ((k : ℤ) - 99) + 7 = (k : ℤ) - 92 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 92)) =
          (2 : ℝ) ^ (((k : ℤ) - 99)) * (2 : ℝ) ^ (7 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 99)) * 128 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`70368744177665`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_forty_six_plus_one_denominator_mul_two_pow_forty_six_plus_one_below
    {k : ℕ} :
    (-((9007199254740864 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 99)))) * 70368744177665 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 92))) := by
  rw [show
      (-((9007199254740864 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 99)))) * 70368744177665 =
        -(((9007199254740864 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 99))) * 70368744177665) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_six_plus_one_denominator_mul_two_pow_forty_six_plus_one_below]

/-- Exact product audit for denominator `140737488355329`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/140737488355329`,
multiplying by `140737488355329` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_seven_plus_one_denominator_mul_two_pow_forty_seven_plus_one_below
    {k : ℕ} :
    ((9007199254740928 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 100))) * 140737488355329 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 94)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 100)) * (2 : ℝ) ^ (100 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 100)) (100 : ℤ)
    have hexp : ((k : ℤ) - 100) + 100 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 94)) =
        (2 : ℝ) ^ (((k : ℤ) - 100)) * 64 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 100)) (6 : ℤ)
    have hexp : ((k : ℤ) - 100) + 6 = (k : ℤ) - 94 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 94)) =
          (2 : ℝ) ^ (((k : ℤ) - 100)) * (2 : ℝ) ^ (6 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 100)) * 64 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`140737488355329`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_forty_seven_plus_one_denominator_mul_two_pow_forty_seven_plus_one_below
    {k : ℕ} :
    (-((9007199254740928 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 100)))) * 140737488355329 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 94))) := by
  rw [show
      (-((9007199254740928 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 100)))) * 140737488355329 =
        -(((9007199254740928 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 100))) * 140737488355329) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_seven_plus_one_denominator_mul_two_pow_forty_seven_plus_one_below]

/-- Exact product audit for denominator `281474976710657`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/281474976710657`,
multiplying by `281474976710657` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_eight_plus_one_denominator_mul_two_pow_forty_eight_plus_one_below
    {k : ℕ} :
    ((9007199254740960 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 101))) * 281474976710657 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 96)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 101)) * (2 : ℝ) ^ (101 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 101)) (101 : ℤ)
    have hexp : ((k : ℤ) - 101) + 101 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 96)) =
        (2 : ℝ) ^ (((k : ℤ) - 101)) * 32 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 101)) (5 : ℤ)
    have hexp : ((k : ℤ) - 101) + 5 = (k : ℤ) - 96 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 96)) =
          (2 : ℝ) ^ (((k : ℤ) - 101)) * (2 : ℝ) ^ (5 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 101)) * 32 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`281474976710657`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_forty_eight_plus_one_denominator_mul_two_pow_forty_eight_plus_one_below
    {k : ℕ} :
    (-((9007199254740960 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 101)))) * 281474976710657 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 96))) := by
  rw [show
      (-((9007199254740960 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 101)))) * 281474976710657 =
        -(((9007199254740960 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 101))) * 281474976710657) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_eight_plus_one_denominator_mul_two_pow_forty_eight_plus_one_below]

/-- Exact product audit for denominator `562949953421313`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/562949953421313`,
multiplying by `562949953421313` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_nine_plus_one_denominator_mul_two_pow_forty_nine_plus_one_below
    {k : ℕ} :
    ((9007199254740976 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 102))) * 562949953421313 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 98)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 102)) * (2 : ℝ) ^ (102 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 102)) (102 : ℤ)
    have hexp : ((k : ℤ) - 102) + 102 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 98)) =
        (2 : ℝ) ^ (((k : ℤ) - 102)) * 16 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 102)) (4 : ℤ)
    have hexp : ((k : ℤ) - 102) + 4 = (k : ℤ) - 98 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 98)) =
          (2 : ℝ) ^ (((k : ℤ) - 102)) * (2 : ℝ) ^ (4 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 102)) * 16 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`562949953421313`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_forty_nine_plus_one_denominator_mul_two_pow_forty_nine_plus_one_below
    {k : ℕ} :
    (-((9007199254740976 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 102)))) * 562949953421313 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 98))) := by
  rw [show
      (-((9007199254740976 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 102)))) * 562949953421313 =
        -(((9007199254740976 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 102))) * 562949953421313) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_forty_nine_plus_one_denominator_mul_two_pow_forty_nine_plus_one_below]

/-- Exact product audit for denominator `1125899906842625`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/1125899906842625`,
multiplying by `1125899906842625` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_plus_one_denominator_mul_two_pow_fifty_plus_one_below
    {k : ℕ} :
    ((9007199254740984 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 103))) * 1125899906842625 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 100)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 103)) * (2 : ℝ) ^ (103 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 103)) (103 : ℤ)
    have hexp : ((k : ℤ) - 103) + 103 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 100)) =
        (2 : ℝ) ^ (((k : ℤ) - 103)) * 8 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 103)) (3 : ℤ)
    have hexp : ((k : ℤ) - 103) + 3 = (k : ℤ) - 100 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 100)) =
          (2 : ℝ) ^ (((k : ℤ) - 103)) * (2 : ℝ) ^ (3 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 103)) * 8 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`1125899906842625`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_fifty_plus_one_denominator_mul_two_pow_fifty_plus_one_below
    {k : ℕ} :
    (-((9007199254740984 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 103)))) * 1125899906842625 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 100))) := by
  rw [show
      (-((9007199254740984 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 103)))) * 1125899906842625 =
        -(((9007199254740984 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 103))) * 1125899906842625) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_plus_one_denominator_mul_two_pow_fifty_plus_one_below]

/-- Exact product audit for denominator `2251799813685249`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/2251799813685249`,
multiplying by `2251799813685249` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_one_plus_one_denominator_mul_two_pow_fifty_one_plus_one_below
    {k : ℕ} :
    ((9007199254740988 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 104))) * 2251799813685249 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 102)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 104)) * (2 : ℝ) ^ (104 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 104)) (104 : ℤ)
    have hexp : ((k : ℤ) - 104) + 104 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 102)) =
        (2 : ℝ) ^ (((k : ℤ) - 104)) * 4 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 104)) (2 : ℤ)
    have hexp : ((k : ℤ) - 104) + 2 = (k : ℤ) - 102 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 102)) =
          (2 : ℝ) ^ (((k : ℤ) - 104)) * (2 : ℝ) ^ (2 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 104)) * 4 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`2251799813685249`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_fifty_one_plus_one_denominator_mul_two_pow_fifty_one_plus_one_below
    {k : ℕ} :
    (-((9007199254740988 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 104)))) * 2251799813685249 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 102))) := by
  rw [show
      (-((9007199254740988 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 104)))) * 2251799813685249 =
        -(((9007199254740988 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 104))) * 2251799813685249) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_one_plus_one_denominator_mul_two_pow_fifty_one_plus_one_below]

/-- Exact product audit for denominator `4503599627370497`: after the rounded
division has stored the lower IEEE-double approximation to `(2^k)/4503599627370497`,
multiplying by `4503599627370497` lands below `2^k` but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_two_plus_one_denominator_mul_two_pow_fifty_two_plus_one_below
    {k : ℕ} :
    ((9007199254740990 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 105))) * 4503599627370497 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 104)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 105)) * (2 : ℝ) ^ (105 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 105)) (105 : ℤ)
    have hexp : ((k : ℤ) - 105) + 105 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 104)) =
        (2 : ℝ) ^ (((k : ℤ) - 105)) * 2 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 105)) (1 : ℤ)
    have hexp : ((k : ℤ) - 105) + 1 = (k : ℤ) - 104 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 104)) =
          (2 : ℝ) ^ (((k : ℤ) - 105)) * (2 : ℝ) ^ (1 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 105)) * 2 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`4503599627370497`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_fifty_two_plus_one_denominator_mul_two_pow_fifty_two_plus_one_below
    {k : ℕ} :
    (-((9007199254740990 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 105)))) * 4503599627370497 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 104))) := by
  rw [show
      (-((9007199254740990 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 105)))) * 4503599627370497 =
        -(((9007199254740990 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 105))) * 4503599627370497) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_two_plus_one_denominator_mul_two_pow_fifty_two_plus_one_below]

/-- Exact product audit for denominator `9007199254740993`: after the rounded
division has stored the lower IEEE-double approximation to
`(2^k)/9007199254740993`, multiplying by `9007199254740993` lands below `2^k`
but still rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_three_plus_one_denominator_mul_two_pow_fifty_three_plus_one_below
    {k : ℕ} :
    ((9007199254740991 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 106))) * 9007199254740993 =
      (2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 106)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 106)) * (2 : ℝ) ^ (106 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 106)) (106 : ℤ)
    have hexp : ((k : ℤ) - 106) + 106 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  rw [hpow]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`9007199254740993`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_fifty_three_plus_one_denominator_mul_two_pow_fifty_three_plus_one_below
    {k : ℕ} :
    (-((9007199254740991 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 106)))) * 9007199254740993 =
      -((2 : ℝ) ^ k - (2 : ℝ) ^ (((k : ℤ) - 106))) := by
  rw [show
      (-((9007199254740991 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 106)))) * 9007199254740993 =
        -(((9007199254740991 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 106))) * 9007199254740993) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_three_plus_one_denominator_mul_two_pow_fifty_three_plus_one_below]

/-- Exact product audit for denominator `18014398509481985`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/18014398509481985`, multiplying by `18014398509481985` lands one
quarter ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_four_plus_one_denominator_mul_two_pow_fifty_four_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 107))) * 18014398509481985 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 54)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 107)) * (2 : ℝ) ^ (107 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 107)) (107 : ℤ)
    have hexp : ((k : ℤ) - 107) + 107 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 54)) =
        (2 : ℝ) ^ (((k : ℤ) - 107)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 107)) (53 : ℤ)
    have hexp : ((k : ℤ) - 107) + 53 = (k : ℤ) - 54 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 54)) =
          (2 : ℝ) ^ (((k : ℤ) - 107)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 107)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`18014398509481985`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_fifty_four_plus_one_denominator_mul_two_pow_fifty_four_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 107)))) * 18014398509481985 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 54))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 107)))) * 18014398509481985 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 107))) * 18014398509481985) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_four_plus_one_denominator_mul_two_pow_fifty_four_plus_one_above]

/-- Exact product audit for denominator `36028797018963969`: after the rounded
division has stored the upper IEEE-double approximation to
`(2^k)/36028797018963969`, multiplying by `36028797018963969` lands one
eighth ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_five_plus_one_denominator_mul_two_pow_fifty_five_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 108))) * 36028797018963969 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 55)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 108)) * (2 : ℝ) ^ (108 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 108)) (108 : ℤ)
    have hexp : ((k : ℤ) - 108) + 108 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 55)) =
        (2 : ℝ) ^ (((k : ℤ) - 108)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 108)) (53 : ℤ)
    have hexp : ((k : ℤ) - 108) + 53 = (k : ℤ) - 55 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 55)) =
          (2 : ℝ) ^ (((k : ℤ) - 108)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 108)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`36028797018963969`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_fifty_five_plus_one_denominator_mul_two_pow_fifty_five_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 108)))) * 36028797018963969 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 55))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 108)))) * 36028797018963969 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 108))) * 36028797018963969) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_five_plus_one_denominator_mul_two_pow_fifty_five_plus_one_above]

/-- Exact product audit for denominator `72057594037927937`: after the rounded
division has stored the upper IEEE-double approximation to
`(2^k)/72057594037927937`, multiplying by `72057594037927937` lands one
sixteenth ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_six_plus_one_denominator_mul_two_pow_fifty_six_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 109))) * 72057594037927937 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 56)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 109)) * (2 : ℝ) ^ (109 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 109)) (109 : ℤ)
    have hexp : ((k : ℤ) - 109) + 109 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 56)) =
        (2 : ℝ) ^ (((k : ℤ) - 109)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 109)) (53 : ℤ)
    have hexp : ((k : ℤ) - 109) + 53 = (k : ℤ) - 56 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 56)) =
          (2 : ℝ) ^ (((k : ℤ) - 109)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 109)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`72057594037927937`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_fifty_six_plus_one_denominator_mul_two_pow_fifty_six_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 109)))) * 72057594037927937 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 56))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 109)))) * 72057594037927937 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 109))) * 72057594037927937) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_six_plus_one_denominator_mul_two_pow_fifty_six_plus_one_above]

/-- Exact product audit for denominator `144115188075855873`: after the rounded
division has stored the upper IEEE-double approximation to
`(2^k)/144115188075855873`, multiplying by `144115188075855873` lands one
thirtysecond ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_seven_plus_one_denominator_mul_two_pow_fifty_seven_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 110))) * 144115188075855873 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 57)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 110)) * (2 : ℝ) ^ (110 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 110)) (110 : ℤ)
    have hexp : ((k : ℤ) - 110) + 110 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 57)) =
        (2 : ℝ) ^ (((k : ℤ) - 110)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 110)) (53 : ℤ)
    have hexp : ((k : ℤ) - 110) + 53 = (k : ℤ) - 57 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 57)) =
          (2 : ℝ) ^ (((k : ℤ) - 110)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 110)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`144115188075855873`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_fifty_seven_plus_one_denominator_mul_two_pow_fifty_seven_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 110)))) * 144115188075855873 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 57))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 110)))) * 144115188075855873 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 110))) * 144115188075855873) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_seven_plus_one_denominator_mul_two_pow_fifty_seven_plus_one_above]

/-- Exact product audit for denominator `288230376151711745`: after the rounded
division has stored the upper IEEE-double approximation to
`(2^k)/288230376151711745`, multiplying by `288230376151711745` lands one
sixty-fourth ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_eight_plus_one_denominator_mul_two_pow_fifty_eight_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 111))) * 288230376151711745 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 58)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 111)) * (2 : ℝ) ^ (111 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 111)) (111 : ℤ)
    have hexp : ((k : ℤ) - 111) + 111 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 58)) =
        (2 : ℝ) ^ (((k : ℤ) - 111)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 111)) (53 : ℤ)
    have hexp : ((k : ℤ) - 111) + 53 = (k : ℤ) - 58 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 58)) =
          (2 : ℝ) ^ (((k : ℤ) - 111)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 111)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`288230376151711745`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_fifty_eight_plus_one_denominator_mul_two_pow_fifty_eight_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 111)))) * 288230376151711745 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 58))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 111)))) * 288230376151711745 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 111))) * 288230376151711745) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_eight_plus_one_denominator_mul_two_pow_fifty_eight_plus_one_above]

/-- Exact product audit for denominator `576460752303423489`: after the rounded
division has stored the upper IEEE-double approximation to
`(2^k)/576460752303423489`, multiplying by `576460752303423489` lands one
128th ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_nine_plus_one_denominator_mul_two_pow_fifty_nine_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 112))) * 576460752303423489 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 59)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 112)) * (2 : ℝ) ^ (112 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 112)) (112 : ℤ)
    have hexp : ((k : ℤ) - 112) + 112 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 59)) =
        (2 : ℝ) ^ (((k : ℤ) - 112)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 112)) (53 : ℤ)
    have hexp : ((k : ℤ) - 112) + 53 = (k : ℤ) - 59 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 59)) =
          (2 : ℝ) ^ (((k : ℤ) - 112)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 112)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`576460752303423489`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_fifty_nine_plus_one_denominator_mul_two_pow_fifty_nine_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 112)))) * 576460752303423489 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 59))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 112)))) * 576460752303423489 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 112))) * 576460752303423489) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_fifty_nine_plus_one_denominator_mul_two_pow_fifty_nine_plus_one_above]

/-- Exact product audit for denominator `1152921504606846977`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/1152921504606846977`, multiplying by `1152921504606846977` lands one
256th ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_plus_one_denominator_mul_two_pow_sixty_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 113))) * 1152921504606846977 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 60)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 113)) * (2 : ℝ) ^ (113 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 113)) (113 : ℤ)
    have hexp : ((k : ℤ) - 113) + 113 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 60)) =
        (2 : ℝ) ^ (((k : ℤ) - 113)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 113)) (53 : ℤ)
    have hexp : ((k : ℤ) - 113) + 53 = (k : ℤ) - 60 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 60)) =
          (2 : ℝ) ^ (((k : ℤ) - 113)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 113)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`1152921504606846977`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_sixty_plus_one_denominator_mul_two_pow_sixty_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 113)))) * 1152921504606846977 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 60))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 113)))) * 1152921504606846977 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 113))) * 1152921504606846977) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_plus_one_denominator_mul_two_pow_sixty_plus_one_above]

/-- Exact product audit for denominator `2305843009213693953`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/2305843009213693953`, multiplying by `2305843009213693953` lands one
512th ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_one_plus_one_denominator_mul_two_pow_sixty_one_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 114))) * 2305843009213693953 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 61)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 114)) * (2 : ℝ) ^ (114 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 114)) (114 : ℤ)
    have hexp : ((k : ℤ) - 114) + 114 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 61)) =
        (2 : ℝ) ^ (((k : ℤ) - 114)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 114)) (53 : ℤ)
    have hexp : ((k : ℤ) - 114) + 53 = (k : ℤ) - 61 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 61)) =
          (2 : ℝ) ^ (((k : ℤ) - 114)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 114)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`2305843009213693953`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_sixty_one_plus_one_denominator_mul_two_pow_sixty_one_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 114)))) * 2305843009213693953 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 61))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 114)))) * 2305843009213693953 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 114))) * 2305843009213693953) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_one_plus_one_denominator_mul_two_pow_sixty_one_plus_one_above]

/-- Exact product audit for denominator `4611686018427387905`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/4611686018427387905`, multiplying by `4611686018427387905` lands one
1024th ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_two_plus_one_denominator_mul_two_pow_sixty_two_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 115))) * 4611686018427387905 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 62)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 115)) * (2 : ℝ) ^ (115 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 115)) (115 : ℤ)
    have hexp : ((k : ℤ) - 115) + 115 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 62)) =
        (2 : ℝ) ^ (((k : ℤ) - 115)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 115)) (53 : ℤ)
    have hexp : ((k : ℤ) - 115) + 53 = (k : ℤ) - 62 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 62)) =
          (2 : ℝ) ^ (((k : ℤ) - 115)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 115)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`4611686018427387905`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_sixty_two_plus_one_denominator_mul_two_pow_sixty_two_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 115)))) * 4611686018427387905 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 62))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 115)))) * 4611686018427387905 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 115))) * 4611686018427387905) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_two_plus_one_denominator_mul_two_pow_sixty_two_plus_one_above]

/-- Exact product audit for denominator `9223372036854775809`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/9223372036854775809`, multiplying by `9223372036854775809` lands one
2048th ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_three_plus_one_denominator_mul_two_pow_sixty_three_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 116))) * 9223372036854775809 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 63)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 116)) * (2 : ℝ) ^ (116 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 116)) (116 : ℤ)
    have hexp : ((k : ℤ) - 116) + 116 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 63)) =
        (2 : ℝ) ^ (((k : ℤ) - 116)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 116)) (53 : ℤ)
    have hexp : ((k : ℤ) - 116) + 53 = (k : ℤ) - 63 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 63)) =
          (2 : ℝ) ^ (((k : ℤ) - 116)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 116)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`9223372036854775809`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_sixty_three_plus_one_denominator_mul_two_pow_sixty_three_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 116)))) * 9223372036854775809 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 63))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 116)))) * 9223372036854775809 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 116))) * 9223372036854775809) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_three_plus_one_denominator_mul_two_pow_sixty_three_plus_one_above]

/-- Exact product audit for denominator `18446744073709551617`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/18446744073709551617`, multiplying by `18446744073709551617` lands one
4096th ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_four_plus_one_denominator_mul_two_pow_sixty_four_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 117))) * 18446744073709551617 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 64)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 117)) * (2 : ℝ) ^ (117 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 117)) (117 : ℤ)
    have hexp : ((k : ℤ) - 117) + 117 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 64)) =
        (2 : ℝ) ^ (((k : ℤ) - 117)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 117)) (53 : ℤ)
    have hexp : ((k : ℤ) - 117) + 53 = (k : ℤ) - 64 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 64)) =
          (2 : ℝ) ^ (((k : ℤ) - 117)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 117)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`18446744073709551617`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_sixty_four_plus_one_denominator_mul_two_pow_sixty_four_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 117)))) * 18446744073709551617 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 64))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 117)))) * 18446744073709551617 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 117))) * 18446744073709551617) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_four_plus_one_denominator_mul_two_pow_sixty_four_plus_one_above]

/-- Exact product audit for denominator `36893488147419103233`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/36893488147419103233`, multiplying by `36893488147419103233` lands one
8192nd ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_five_plus_one_denominator_mul_two_pow_sixty_five_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 118))) * 36893488147419103233 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 65)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 118)) * (2 : ℝ) ^ (118 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 118)) (118 : ℤ)
    have hexp : ((k : ℤ) - 118) + 118 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 65)) =
        (2 : ℝ) ^ (((k : ℤ) - 118)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 118)) (53 : ℤ)
    have hexp : ((k : ℤ) - 118) + 53 = (k : ℤ) - 65 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 65)) =
          (2 : ℝ) ^ (((k : ℤ) - 118)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 118)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`36893488147419103233`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_sixty_five_plus_one_denominator_mul_two_pow_sixty_five_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 118)))) * 36893488147419103233 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 65))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 118)))) * 36893488147419103233 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 118))) * 36893488147419103233) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_five_plus_one_denominator_mul_two_pow_sixty_five_plus_one_above]

/-- Exact product audit for denominator `73786976294838206465`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/73786976294838206465`, multiplying by `73786976294838206465` lands one
16384th ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_six_plus_one_denominator_mul_two_pow_sixty_six_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 119))) * 73786976294838206465 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 66)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 119)) * (2 : ℝ) ^ (119 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 119)) (119 : ℤ)
    have hexp : ((k : ℤ) - 119) + 119 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 66)) =
        (2 : ℝ) ^ (((k : ℤ) - 119)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 119)) (53 : ℤ)
    have hexp : ((k : ℤ) - 119) + 53 = (k : ℤ) - 66 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 66)) =
          (2 : ℝ) ^ (((k : ℤ) - 119)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 119)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`73786976294838206465`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_sixty_six_plus_one_denominator_mul_two_pow_sixty_six_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 119)))) * 73786976294838206465 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 66))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 119)))) * 73786976294838206465 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 119))) * 73786976294838206465) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_six_plus_one_denominator_mul_two_pow_sixty_six_plus_one_above]

/-- Exact product audit for denominator `147573952589676412929`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/147573952589676412929`, multiplying by `147573952589676412929` lands one
32768th ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_seven_plus_one_denominator_mul_two_pow_sixty_seven_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 120))) * 147573952589676412929 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 67)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 120)) * (2 : ℝ) ^ (120 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 120)) (120 : ℤ)
    have hexp : ((k : ℤ) - 120) + 120 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 67)) =
        (2 : ℝ) ^ (((k : ℤ) - 120)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 120)) (53 : ℤ)
    have hexp : ((k : ℤ) - 120) + 53 = (k : ℤ) - 67 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 67)) =
          (2 : ℝ) ^ (((k : ℤ) - 120)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 120)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`147573952589676412929`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_sixty_seven_plus_one_denominator_mul_two_pow_sixty_seven_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 120)))) * 147573952589676412929 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 67))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 120)))) * 147573952589676412929 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 120))) * 147573952589676412929) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_seven_plus_one_denominator_mul_two_pow_sixty_seven_plus_one_above]

/-- Exact product audit for denominator `295147905179352825857`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/295147905179352825857`, multiplying by `295147905179352825857` lands one
65536th ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_eight_plus_one_denominator_mul_two_pow_sixty_eight_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 121))) * 295147905179352825857 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 68)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 121)) * (2 : ℝ) ^ (121 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 121)) (121 : ℤ)
    have hexp : ((k : ℤ) - 121) + 121 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 68)) =
        (2 : ℝ) ^ (((k : ℤ) - 121)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 121)) (53 : ℤ)
    have hexp : ((k : ℤ) - 121) + 53 = (k : ℤ) - 68 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 68)) =
          (2 : ℝ) ^ (((k : ℤ) - 121)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 121)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`295147905179352825857`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_sixty_eight_plus_one_denominator_mul_two_pow_sixty_eight_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 121)))) * 295147905179352825857 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 68))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 121)))) * 295147905179352825857 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 121))) * 295147905179352825857) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_eight_plus_one_denominator_mul_two_pow_sixty_eight_plus_one_above]

/-- Exact product audit for denominator `590295810358705651713`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/590295810358705651713`, multiplying by `590295810358705651713` lands one
131072nd ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_nine_plus_one_denominator_mul_two_pow_sixty_nine_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 122))) * 590295810358705651713 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 69)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 122)) * (2 : ℝ) ^ (122 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 122)) (122 : ℤ)
    have hexp : ((k : ℤ) - 122) + 122 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 69)) =
        (2 : ℝ) ^ (((k : ℤ) - 122)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 122)) (53 : ℤ)
    have hexp : ((k : ℤ) - 122) + 53 = (k : ℤ) - 69 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 69)) =
          (2 : ℝ) ^ (((k : ℤ) - 122)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 122)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`590295810358705651713`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_sixty_nine_plus_one_denominator_mul_two_pow_sixty_nine_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 122)))) * 590295810358705651713 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 69))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 122)))) * 590295810358705651713 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 122))) * 590295810358705651713) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_sixty_nine_plus_one_denominator_mul_two_pow_sixty_nine_plus_one_above]

/-- Exact product audit for denominator `1180591620717411303425`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/1180591620717411303425`, multiplying by `1180591620717411303425` lands
one 262144th ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_seventy_plus_one_denominator_mul_two_pow_seventy_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 123))) * 1180591620717411303425 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 70)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 123)) * (2 : ℝ) ^ (123 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 123)) (123 : ℤ)
    have hexp : ((k : ℤ) - 123) + 123 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 70)) =
        (2 : ℝ) ^ (((k : ℤ) - 123)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 123)) (53 : ℤ)
    have hexp : ((k : ℤ) - 123) + 53 = (k : ℤ) - 70 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 70)) =
          (2 : ℝ) ^ (((k : ℤ) - 123)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 123)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`1180591620717411303425`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_seventy_plus_one_denominator_mul_two_pow_seventy_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 123)))) * 1180591620717411303425 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 70))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 123)))) * 1180591620717411303425 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 123))) * 1180591620717411303425) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_seventy_plus_one_denominator_mul_two_pow_seventy_plus_one_above]

/-- Exact product audit for denominator `2361183241434822606849`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/2361183241434822606849`, multiplying by `2361183241434822606849` lands
one 524288th ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_seventy_one_plus_one_denominator_mul_two_pow_seventy_one_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 124))) * 2361183241434822606849 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 71)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 124)) * (2 : ℝ) ^ (124 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 124)) (124 : ℤ)
    have hexp : ((k : ℤ) - 124) + 124 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 71)) =
        (2 : ℝ) ^ (((k : ℤ) - 124)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 124)) (53 : ℤ)
    have hexp : ((k : ℤ) - 124) + 53 = (k : ℤ) - 71 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 71)) =
          (2 : ℝ) ^ (((k : ℤ) - 124)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 124)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`2361183241434822606849`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_seventy_one_plus_one_denominator_mul_two_pow_seventy_one_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 124)))) * 2361183241434822606849 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 71))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 124)))) * 2361183241434822606849 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 124))) * 2361183241434822606849) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_seventy_one_plus_one_denominator_mul_two_pow_seventy_one_plus_one_above]

/-- Exact product audit for denominator `4722366482869645213697`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/4722366482869645213697`, multiplying by `4722366482869645213697` lands
one 1048576th ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_seventy_two_plus_one_denominator_mul_two_pow_seventy_two_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 125))) * 4722366482869645213697 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 72)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 125)) * (2 : ℝ) ^ (125 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 125)) (125 : ℤ)
    have hexp : ((k : ℤ) - 125) + 125 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 72)) =
        (2 : ℝ) ^ (((k : ℤ) - 125)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 125)) (53 : ℤ)
    have hexp : ((k : ℤ) - 125) + 53 = (k : ℤ) - 72 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 72)) =
          (2 : ℝ) ^ (((k : ℤ) - 125)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 125)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`4722366482869645213697`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_seventy_two_plus_one_denominator_mul_two_pow_seventy_two_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 125)))) * 4722366482869645213697 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 72))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 125)))) * 4722366482869645213697 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 125))) * 4722366482869645213697) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_seventy_two_plus_one_denominator_mul_two_pow_seventy_two_plus_one_above]

/-- Exact product audit for denominator `9444732965739290427393`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/9444732965739290427393`, multiplying by `9444732965739290427393` lands
one 2097152nd ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_seventy_three_plus_one_denominator_mul_two_pow_seventy_three_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 126))) * 9444732965739290427393 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 73)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 126)) * (2 : ℝ) ^ (126 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 126)) (126 : ℤ)
    have hexp : ((k : ℤ) - 126) + 126 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 73)) =
        (2 : ℝ) ^ (((k : ℤ) - 126)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 126)) (53 : ℤ)
    have hexp : ((k : ℤ) - 126) + 53 = (k : ℤ) - 73 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 73)) =
          (2 : ℝ) ^ (((k : ℤ) - 126)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 126)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`9444732965739290427393`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_seventy_three_plus_one_denominator_mul_two_pow_seventy_three_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 126)))) * 9444732965739290427393 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 73))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 126)))) * 9444732965739290427393 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 126))) * 9444732965739290427393) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_seventy_three_plus_one_denominator_mul_two_pow_seventy_three_plus_one_above]

/-- Exact product audit for denominator `18889465931478580854785`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/18889465931478580854785`, multiplying by `18889465931478580854785` lands
one 4194304th ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_seventy_four_plus_one_denominator_mul_two_pow_seventy_four_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 127))) * 18889465931478580854785 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 74)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 127)) * (2 : ℝ) ^ (127 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 127)) (127 : ℤ)
    have hexp : ((k : ℤ) - 127) + 127 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 74)) =
        (2 : ℝ) ^ (((k : ℤ) - 127)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 127)) (53 : ℤ)
    have hexp : ((k : ℤ) - 127) + 53 = (k : ℤ) - 74 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 74)) =
          (2 : ℝ) ^ (((k : ℤ) - 127)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 127)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`18889465931478580854785`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_seventy_four_plus_one_denominator_mul_two_pow_seventy_four_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 127)))) * 18889465931478580854785 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 74))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 127)))) * 18889465931478580854785 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 127))) * 18889465931478580854785) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_seventy_four_plus_one_denominator_mul_two_pow_seventy_four_plus_one_above]

/-- Exact product audit for denominator `37778931862957161709569`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/37778931862957161709569`, multiplying by `37778931862957161709569` lands
one 8388608th ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_seventy_five_plus_one_denominator_mul_two_pow_seventy_five_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 128))) * 37778931862957161709569 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 75)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 128)) * (2 : ℝ) ^ (128 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 128)) (128 : ℤ)
    have hexp : ((k : ℤ) - 128) + 128 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 75)) =
        (2 : ℝ) ^ (((k : ℤ) - 128)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 128)) (53 : ℤ)
    have hexp : ((k : ℤ) - 128) + 53 = (k : ℤ) - 75 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 75)) =
          (2 : ℝ) ^ (((k : ℤ) - 128)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 128)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`37778931862957161709569`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_seventy_five_plus_one_denominator_mul_two_pow_seventy_five_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 128)))) * 37778931862957161709569 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 75))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 128)))) * 37778931862957161709569 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 128))) * 37778931862957161709569) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_seventy_five_plus_one_denominator_mul_two_pow_seventy_five_plus_one_above]

/-- Exact product audit for denominator `75557863725914323419137`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/75557863725914323419137`, multiplying by `75557863725914323419137` lands
one 16777216th ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_seventy_six_plus_one_denominator_mul_two_pow_seventy_six_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 129))) * 75557863725914323419137 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 76)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 129)) * (2 : ℝ) ^ (129 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 129)) (129 : ℤ)
    have hexp : ((k : ℤ) - 129) + 129 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 76)) =
        (2 : ℝ) ^ (((k : ℤ) - 129)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 129)) (53 : ℤ)
    have hexp : ((k : ℤ) - 129) + 53 = (k : ℤ) - 76 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 76)) =
          (2 : ℝ) ^ (((k : ℤ) - 129)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 129)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`75557863725914323419137`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_seventy_six_plus_one_denominator_mul_two_pow_seventy_six_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 129)))) * 75557863725914323419137 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 76))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 129)))) * 75557863725914323419137 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 129))) * 75557863725914323419137) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_seventy_six_plus_one_denominator_mul_two_pow_seventy_six_plus_one_above]

/-- Exact product audit for denominator `151115727451828646838273`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/151115727451828646838273`, multiplying by `151115727451828646838273`
lands one 33554432nd ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_seventy_seven_plus_one_denominator_mul_two_pow_seventy_seven_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 130))) * 151115727451828646838273 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 77)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 130)) * (2 : ℝ) ^ (130 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 130)) (130 : ℤ)
    have hexp : ((k : ℤ) - 130) + 130 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 77)) =
        (2 : ℝ) ^ (((k : ℤ) - 130)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 130)) (53 : ℤ)
    have hexp : ((k : ℤ) - 130) + 53 = (k : ℤ) - 77 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 77)) =
          (2 : ℝ) ^ (((k : ℤ) - 130)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 130)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`151115727451828646838273`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_seventy_seven_plus_one_denominator_mul_two_pow_seventy_seven_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 130)))) * 151115727451828646838273 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 77))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 130)))) * 151115727451828646838273 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 130))) * 151115727451828646838273) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_seventy_seven_plus_one_denominator_mul_two_pow_seventy_seven_plus_one_above]

/-- Exact product audit for denominator `302231454903657293676545`: after the
rounded division has stored the upper IEEE-double approximation to
`(2^k)/302231454903657293676545`, multiplying by `302231454903657293676545`
lands one 67108864th ulp above `2^k` and then rounds back to it. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_two_pow_seventy_eight_plus_one_denominator_mul_two_pow_seventy_eight_plus_one_above
    {k : ℕ} :
    ((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 131))) * 302231454903657293676545 =
      (2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 78)) := by
  have hpow :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (((k : ℤ) - 131)) * (2 : ℝ) ^ (131 : ℤ) := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 131)) (131 : ℤ)
    have hexp : ((k : ℤ) - 131) + 131 = (k : ℤ) := by ring
    rw [hexp] at h
    simpa [zpow_natCast] using h
  have htail :
      (2 : ℝ) ^ (((k : ℤ) - 78)) =
        (2 : ℝ) ^ (((k : ℤ) - 131)) * 9007199254740992 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 131)) (53 : ℤ)
    have hexp : ((k : ℤ) - 131) + 53 = (k : ℤ) - 78 := by ring
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k : ℤ) - 78)) =
          (2 : ℝ) ^ (((k : ℤ) - 131)) * (2 : ℝ) ^ (53 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 131)) * 9007199254740992 := by
        norm_num [zpow_natCast]
  rw [hpow, htail]
  norm_num [zpow_natCast]
  ring

/-- Exact product audit for the signed denominator-`302231454903657293676545`,
power-of-two second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_two_pow_seventy_eight_plus_one_denominator_mul_two_pow_seventy_eight_plus_one_above
    {k : ℕ} :
    (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 131)))) * 302231454903657293676545 =
      -((2 : ℝ) ^ k + (2 : ℝ) ^ (((k : ℤ) - 78))) := by
  rw [show
      (-((9007199254740992 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 131)))) * 302231454903657293676545 =
        -(((9007199254740992 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 131))) * 302231454903657293676545) by
    ring]
  rw [
    problem2_10_ieeeDouble_rounded_two_pow_two_pow_seventy_eight_plus_one_denominator_mul_two_pow_seventy_eight_plus_one_above]

/-- Exact product audit for denominator `18`: after the rounded division
has reused the denominator-`9` quotient, multiplying by `18` lands at the
midpoint immediately below `2^(k+1)`. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_succ_eighteenths_mul_eighteen_midpoint
    {k : ℕ} :
    ((8006399337547548 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 56))) * 18 =
      (2 : ℝ) ^ (k + 1) - (2 : ℝ) ^ (((k + 1 : ℤ) - 54)) := by
  have hnine :=
    problem2_10_ieeeDouble_rounded_two_pow_ninths_mul_nine_midpoint (k := k)
  have htail :
      (2 : ℝ) ^ (((k + 1 : ℤ) - 54)) =
        (2 : ℝ) ^ (((k : ℤ) - 54)) * 2 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 54)) (1 : ℤ)
    have hexp : ((k : ℤ) - 54) + 1 = ((k + 1 : ℤ) - 54) := by omega
    rw [hexp] at h
    simpa [zpow_one] using h
  have hpow : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by
    rw [pow_succ]
  rw [show
      ((8006399337547548 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 56))) * 18 =
        (((8006399337547548 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 56))) * 9) * 2 by
    ring]
  rw [hnine, hpow, htail]
  ring

/-- Exact product audit for the signed denominator-`18`, shifted power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_succ_eighteenths_mul_eighteen_midpoint
    {k : ℕ} :
    (-((8006399337547548 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 56)))) * 18 =
      -((2 : ℝ) ^ (k + 1)) + (2 : ℝ) ^ (((k + 1 : ℤ) - 54)) := by
  rw [show
      (-((8006399337547548 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 56)))) * 18 =
        -(((8006399337547548 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 56))) * 18) by
    ring]
  rw [problem2_10_ieeeDouble_rounded_two_pow_succ_eighteenths_mul_eighteen_midpoint]
  ring

/-- Exact product audit for denominator `6`: after the rounded division
has reused the denominator-`3` quotient, multiplying by `6` lands at the
midpoint immediately below `2^(k+1)`. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_succ_sixths_mul_six_midpoint
    {k : ℕ} :
    ((6004799503160661 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 54))) * 6 =
      (2 : ℝ) ^ (k + 1) - (2 : ℝ) ^ (((k + 1 : ℤ) - 54)) := by
  have hthree :=
    problem2_10_ieeeDouble_rounded_two_pow_thirds_mul_three_midpoint (k := k)
  have htail :
      (2 : ℝ) ^ (((k + 1 : ℤ) - 54)) =
        (2 : ℝ) ^ (((k : ℤ) - 54)) * 2 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 54)) (1 : ℤ)
    have hexp : ((k : ℤ) - 54) + 1 = ((k + 1 : ℤ) - 54) := by omega
    rw [hexp] at h
    simpa [zpow_one] using h
  have hpow : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by
    rw [pow_succ]
  rw [show
      ((6004799503160661 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 54))) * 6 =
        (((6004799503160661 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 54))) * 3) * 2 by
    ring]
  rw [hthree, hpow, htail]
  ring

/-- Exact product audit for the signed denominator-`6`, power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_succ_sixths_mul_six_midpoint
    {k : ℕ} :
    (-((6004799503160661 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 54)))) * 6 =
      -((2 : ℝ) ^ (k + 1)) + (2 : ℝ) ^ (((k + 1 : ℤ) - 54)) := by
  rw [show
      (-((6004799503160661 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 54)))) * 6 =
        -(((6004799503160661 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 54))) * 6) by
    ring]
  rw [problem2_10_ieeeDouble_rounded_two_pow_succ_sixths_mul_six_midpoint]
  ring

/-- Exact product audit for denominator `10`: after the rounded division
has reused the denominator-`5` quotient, multiplying by `10` lands one
quarter ulp above `2^(k+1)`. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_succ_tenths_mul_ten_above
    {k : ℕ} :
    ((7205759403792794 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 55))) * 10 =
      (2 : ℝ) ^ (k + 1) + (2 : ℝ) ^ (((k + 1 : ℤ) - 54)) := by
  have hfive :=
    problem2_10_ieeeDouble_rounded_two_pow_fifths_mul_five_above_two_pow
      (k := k)
  have htail :
      (2 : ℝ) ^ (((k + 1 : ℤ) - 54)) =
        (2 : ℝ) ^ (((k : ℤ) - 54)) * 2 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 54)) (1 : ℤ)
    have hexp : ((k : ℤ) - 54) + 1 = ((k + 1 : ℤ) - 54) := by omega
    rw [hexp] at h
    simpa [zpow_one] using h
  have hpow : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by
    rw [pow_succ]
  rw [show
      ((7205759403792794 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 55))) * 10 =
        (((7205759403792794 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 55))) * 5) * 2 by
    ring]
  rw [hfive, hpow, htail]
  ring

/-- Exact product audit for the signed denominator-`10`, shifted power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_succ_tenths_mul_ten_below
    {k : ℕ} :
    (-((7205759403792794 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 55)))) * 10 =
      -((2 : ℝ) ^ (k + 1) + (2 : ℝ) ^ (((k + 1 : ℤ) - 54))) := by
  rw [show
      (-((7205759403792794 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 55)))) * 10 =
        -(((7205759403792794 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 55))) * 10) by
    ring]
  rw [problem2_10_ieeeDouble_rounded_two_pow_succ_tenths_mul_ten_above]

/-- Exact product audit for denominator `12`: after the rounded division
has reused the denominator-`3` quotient, multiplying by `12` lands at the
midpoint immediately below `2^(k+2)`. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_add_two_twelfths_mul_twelve_midpoint
    {k : ℕ} :
    ((6004799503160661 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 54))) * 12 =
      (2 : ℝ) ^ (k + 2) - (2 : ℝ) ^ (((k + 2 : ℤ) - 54)) := by
  have hthree :=
    problem2_10_ieeeDouble_rounded_two_pow_thirds_mul_three_midpoint (k := k)
  have htail :
      (2 : ℝ) ^ (((k + 2 : ℤ) - 54)) =
        (2 : ℝ) ^ (((k : ℤ) - 54)) * 4 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 54)) (2 : ℤ)
    have hexp : ((k : ℤ) - 54) + 2 = ((k + 2 : ℤ) - 54) := by omega
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k + 2 : ℤ) - 54)) =
          (2 : ℝ) ^ (((k : ℤ) - 54)) * (2 : ℝ) ^ (2 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 54)) * 4 := by
        norm_num [zpow_natCast]
  have hpow : (2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ k * 4 := by
    rw [pow_add]
    norm_num
  rw [show
      ((6004799503160661 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 54))) * 12 =
        (((6004799503160661 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 54))) * 3) * 4 by
    ring]
  rw [hthree, hpow, htail]
  ring

/-- Exact product audit for the signed denominator-`12`, shifted power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_add_two_twelfths_mul_twelve_midpoint
    {k : ℕ} :
    (-((6004799503160661 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 54)))) * 12 =
      -((2 : ℝ) ^ (k + 2)) + (2 : ℝ) ^ (((k + 2 : ℤ) - 54)) := by
  rw [show
      (-((6004799503160661 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 54)))) * 12 =
        -(((6004799503160661 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 54))) * 12) by
    ring]
  rw [problem2_10_ieeeDouble_rounded_two_pow_add_two_twelfths_mul_twelve_midpoint]
  ring

/-- Exact product audit for denominator `20`: after the rounded division
has reused the denominator-`5` quotient, multiplying by `20` lands one
quarter ulp above `2^(k+2)`. -/
theorem problem2_10_ieeeDouble_rounded_two_pow_add_two_twentieths_mul_twenty_above
    {k : ℕ} :
    ((7205759403792794 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 55))) * 20 =
      (2 : ℝ) ^ (k + 2) + (2 : ℝ) ^ (((k + 2 : ℤ) - 54)) := by
  have hfive :=
    problem2_10_ieeeDouble_rounded_two_pow_fifths_mul_five_above_two_pow
      (k := k)
  have htail :
      (2 : ℝ) ^ (((k + 2 : ℤ) - 54)) =
        (2 : ℝ) ^ (((k : ℤ) - 54)) * 4 := by
    have h :=
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (((k : ℤ) - 54)) (2 : ℤ)
    have hexp : ((k : ℤ) - 54) + 2 = ((k + 2 : ℤ) - 54) := by omega
    rw [hexp] at h
    calc
      (2 : ℝ) ^ (((k + 2 : ℤ) - 54)) =
          (2 : ℝ) ^ (((k : ℤ) - 54)) * (2 : ℝ) ^ (2 : ℤ) := h
      _ = (2 : ℝ) ^ (((k : ℤ) - 54)) * 4 := by
        norm_num [zpow_natCast]
  have hpow : (2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ k * 4 := by
    rw [pow_add]
    norm_num
  rw [show
      ((7205759403792794 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 55))) * 20 =
        (((7205759403792794 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 55))) * 5) * 4 by
    ring]
  rw [hfive, hpow, htail]
  ring

/-- Exact product audit for the signed denominator-`20`, shifted power-of-two
second operation. -/
theorem problem2_10_ieeeDouble_negative_rounded_two_pow_add_two_twentieths_mul_twenty_below
    {k : ℕ} :
    (-((7205759403792794 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 55)))) * 20 =
      -((2 : ℝ) ^ (k + 2) + (2 : ℝ) ^ (((k + 2 : ℤ) - 54))) := by
  rw [show
      (-((7205759403792794 : ℝ) * (2 : ℝ) ^ (((k : ℤ) - 55)))) * 20 =
        -(((7205759403792794 : ℝ) *
          (2 : ℝ) ^ (((k : ℤ) - 55))) * 20) by
    ring]
  rw [problem2_10_ieeeDouble_rounded_two_pow_add_two_twentieths_mul_twenty_above]

/-- After the rounded `1/6` division, exact multiplication by `6` lands at
the midpoint immediately below `1`. -/
theorem problem2_10_ieeeDouble_rounded_oneSixth_mul_six_midpoint :
    ((6004799503160661 : ℝ) * (2 : ℝ) ^ (-55 : ℤ)) * 6 =
      (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) := by
  norm_num [zpow_neg]

/-- Signed second-operation audit for `m = -1`, `n = 6`. -/
theorem problem2_10_ieeeDouble_negative_rounded_oneSixth_mul_six_midpoint :
    (-((6004799503160661 : ℝ) * (2 : ℝ) ^ (-55 : ℤ))) * 6 =
      -(1 : ℝ) + (2 : ℝ) ^ (-54 : ℤ) := by
  norm_num [zpow_neg]

/-- Signed final rounding fact for the `m = -1`, `n = 6` midpoint. -/
theorem problem2_10_ieeeDouble_negative_midpoint_above_one_rounds_to_neg_one :
    ieeeDoubleFormat.finiteRoundToEven
        (-(1 : ℝ) + (2 : ℝ) ^ (-54 : ℤ)) = (-1 : ℝ) := by
  have harg :
      (-(1 : ℝ) + (2 : ℝ) ^ (-54 : ℤ)) =
        -((1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ)) := by ring
  rw [harg]
  rw [ieeeDoubleFormat.finiteRoundToEven_neg]
  · rw [problem2_9_double_rounds_extended_midpoint_to_one]
  · norm_num [evenMantissa, ieeeDoubleFormat]
  · norm_num [ieeeDoubleFormat]

/-- After the rounded `1/10` division, exact multiplication by `10` lands at
`1 + 2^-54`, the same final-rounding cell as the `1/5` trace. -/
theorem problem2_10_ieeeDouble_rounded_oneTenth_mul_ten_above_one :
    ((7205759403792794 : ℝ) * (2 : ℝ) ^ (-56 : ℤ)) * 10 =
      (1 : ℝ) + (2 : ℝ) ^ (-54 : ℤ) := by
  norm_num [zpow_neg]

/-- Signed second-operation audit for `m = -1`, `n = 10`. -/
theorem problem2_10_ieeeDouble_negative_rounded_oneTenth_mul_ten_below_neg_one :
    (-((7205759403792794 : ℝ) * (2 : ℝ) ^ (-56 : ℤ))) * 10 =
      -((1 : ℝ) + (2 : ℝ) ^ (-54 : ℤ)) := by
  rw [show
      (-((7205759403792794 : ℝ) * (2 : ℝ) ^ (-56 : ℤ))) * 10 =
        -(((7205759403792794 : ℝ) * (2 : ℝ) ^ (-56 : ℤ)) * 10) by
    ring]
  rw [problem2_10_ieeeDouble_rounded_oneTenth_mul_ten_above_one]

/-- The rounded double approximation to `1/3`, multiplied exactly by `3`,
is the midpoint below `1`. -/
theorem problem2_10_ieeeDouble_rounded_oneThird_mul_three_midpoint :
    ((6004799503160661 : ℝ) * (2 : ℝ) ^ (-54 : ℤ)) * 3 =
      (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) := by
  norm_num [zpow_neg]

/-- Problem 2.10 example, second rounding fact: the midpoint below `1` ties to
the even endpoint `1`. -/
theorem problem2_10_ieeeDouble_midpoint_below_one_rounds_to_one :
    ieeeDoubleFormat.finiteRoundToEven
        ((1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ)) = (1 : ℝ) :=
  problem2_9_double_rounds_extended_midpoint_to_one

/-- The rounded double approximation to `2/3`, multiplied exactly by `3`,
is the midpoint below `2`. -/
theorem problem2_10_ieeeDouble_rounded_twoThirds_mul_three_midpoint :
    ((6004799503160661 : ℝ) * (2 : ℝ) ^ (-53 : ℤ)) * 3 =
      (2 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) := by
  norm_num [zpow_neg]

/-- The rounded double approximation to `-1/3`, multiplied exactly by `3`,
is the midpoint above `-1`. -/
theorem problem2_10_ieeeDouble_negative_rounded_oneThird_mul_three_midpoint :
    (-((6004799503160661 : ℝ) * (2 : ℝ) ^ (-54 : ℤ))) * 3 =
      -(1 : ℝ) + (2 : ℝ) ^ (-54 : ℤ) := by
  norm_num [zpow_neg]

/-- Signed second rounding fact: the midpoint above `-1` ties to the even
endpoint `-1`. -/
theorem problem2_10_ieeeDouble_negative_midpoint_above_neg_one_rounds_to_neg_one :
    ieeeDoubleFormat.finiteRoundToEven
        (-(1 : ℝ) + (2 : ℝ) ^ (-54 : ℤ)) = (-1 : ℝ) := by
  have harg :
      (-(1 : ℝ) + (2 : ℝ) ^ (-54 : ℤ)) =
        -((1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ)) := by ring
  rw [harg]
  rw [ieeeDoubleFormat.finiteRoundToEven_neg]
  · rw [problem2_10_ieeeDouble_midpoint_below_one_rounds_to_one]
  · norm_num [evenMantissa, ieeeDoubleFormat]
  · norm_num [ieeeDoubleFormat]

/-- The rounded double approximation to `-2/3`, multiplied exactly by `3`,
is the midpoint above `-2`. -/
theorem problem2_10_ieeeDouble_negative_rounded_twoThirds_mul_three_midpoint :
    (-((6004799503160661 : ℝ) * (2 : ℝ) ^ (-53 : ℤ))) * 3 =
      -(2 : ℝ) + (2 : ℝ) ^ (-53 : ℤ) := by
  norm_num [zpow_neg]

/-- The rounded double approximation to `4/3`, multiplied exactly by `3`,
is the midpoint below `4`. -/
theorem problem2_10_ieeeDouble_rounded_fourThirds_mul_three_midpoint :
    ((6004799503160661 : ℝ) * (2 : ℝ) ^ (-52 : ℤ)) * 3 =
      (4 : ℝ) - (2 : ℝ) ^ (-52 : ℤ) := by
  norm_num [zpow_neg]

/-- The rounded double approximation to `-4/3`, multiplied exactly by `3`,
is the midpoint above `-4`. -/
theorem problem2_10_ieeeDouble_negative_rounded_fourThirds_mul_three_midpoint :
    (-((6004799503160661 : ℝ) * (2 : ℝ) ^ (-52 : ℤ))) * 3 =
      -(4 : ℝ) + (2 : ℝ) ^ (-52 : ℤ) := by
  norm_num [zpow_neg]

/-- The rounded double approximation to `8/3`, multiplied exactly by `3`,
is the midpoint below `8`. -/
theorem problem2_10_ieeeDouble_rounded_eightThirds_mul_three_midpoint :
    ((6004799503160661 : ℝ) * (2 : ℝ) ^ (-51 : ℤ)) * 3 =
      (8 : ℝ) - (2 : ℝ) ^ (-51 : ℤ) := by
  norm_num [zpow_neg]

/-- The rounded double approximation to `-8/3`, multiplied exactly by `3`,
is the midpoint above `-8`. -/
theorem problem2_10_ieeeDouble_negative_rounded_eightThirds_mul_three_midpoint :
    (-((6004799503160661 : ℝ) * (2 : ℝ) ^ (-51 : ℤ))) * 3 =
      -(8 : ℝ) + (2 : ℝ) ^ (-51 : ℤ) := by
  norm_num [zpow_neg]

/-- The rounded double approximation to `16/3`, multiplied exactly by `3`,
is the midpoint below `16`. -/
theorem problem2_10_ieeeDouble_rounded_sixteenThirds_mul_three_midpoint :
    ((6004799503160661 : ℝ) * (2 : ℝ) ^ (-50 : ℤ)) * 3 =
      (16 : ℝ) - (2 : ℝ) ^ (-50 : ℤ) := by
  norm_num [zpow_neg]

/-- The rounded double approximation to `-16/3`, multiplied exactly by `3`,
is the midpoint above `-16`. -/
theorem problem2_10_ieeeDouble_negative_rounded_sixteenThirds_mul_three_midpoint :
    (-((6004799503160661 : ℝ) * (2 : ℝ) ^ (-50 : ℤ))) * 3 =
      -(16 : ℝ) + (2 : ℝ) ^ (-50 : ℤ) := by
  norm_num [zpow_neg]

/-- The rounded double approximation to `32/3`, multiplied exactly by `3`,
is the midpoint below `32`. -/
theorem problem2_10_ieeeDouble_rounded_thirtytwoThirds_mul_three_midpoint :
    ((6004799503160661 : ℝ) * (2 : ℝ) ^ (-49 : ℤ)) * 3 =
      (32 : ℝ) - (2 : ℝ) ^ (-49 : ℤ) := by
  norm_num [zpow_neg]

/-- The rounded double approximation to `-32/3`, multiplied exactly by `3`,
is the midpoint above `-32`. -/
theorem problem2_10_ieeeDouble_negative_rounded_thirtytwoThirds_mul_three_midpoint :
    (-((6004799503160661 : ℝ) * (2 : ℝ) ^ (-49 : ℤ))) * 3 =
      -(32 : ℝ) + (2 : ℝ) ^ (-49 : ℤ) := by
  norm_num [zpow_neg]

end FloatingPointFormat
end NumStability

end
