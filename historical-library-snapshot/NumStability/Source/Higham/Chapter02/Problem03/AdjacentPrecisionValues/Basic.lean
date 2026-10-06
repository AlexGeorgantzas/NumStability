import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results

/-!
# Chapter02 Problem03 AdjacentPrecisionValues Basic

Canonical destination for material split out of
`NumStability.Analysis.Problem2_3` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

namespace FloatingPointFormat

/-- Mantissa refinement factor from IEEE single precision (`t = 24`) to IEEE
double precision (`t = 53`) in a fixed binary binade. -/
def problem2_3_singleToDoubleMantissaScale : ℕ :=
  2 ^ 29

/-- The double mantissas strictly between adjacent same-exponent single
mantissas after scaling by `2^29`. -/
def problem2_3_sameExponentInteriorDoubleMantissas (m : ℕ) : Finset ℕ :=
  Finset.Icc (m * problem2_3_singleToDoubleMantissaScale + 1)
    ((m + 1) * problem2_3_singleToDoubleMantissaScale - 1)

theorem problem2_3_sameExponentInteriorDoubleMantissas_card (m : ℕ) :
    (problem2_3_sameExponentInteriorDoubleMantissas m).card = 2 ^ 29 - 1 := by
  rw [problem2_3_sameExponentInteriorDoubleMantissas, Nat.card_Icc]
  simp [problem2_3_singleToDoubleMantissaScale]
  omega

theorem problem2_3_sameExponentInteriorDoubleMantissas_mem_iff
    {m n : ℕ} :
    n ∈ problem2_3_sameExponentInteriorDoubleMantissas m ↔
      m * problem2_3_singleToDoubleMantissaScale < n ∧
        n < (m + 1) * problem2_3_singleToDoubleMantissaScale := by
  rw [problem2_3_sameExponentInteriorDoubleMantissas, Finset.mem_Icc]
  constructor
  · intro h
    constructor
    · exact Nat.lt_of_succ_le h.1
    · omega
  · intro h
    constructor
    · exact Nat.succ_le_of_lt h.1
    · omega

theorem problem2_3_ieeeSingle_exponentInRange_ieeeDouble
    {e : ℤ} (he : ieeeSingleFormat.exponentInRange e) :
    ieeeDoubleFormat.exponentInRange e := by
  norm_num [ieeeSingleFormat, ieeeDoubleFormat, exponentInRange] at he ⊢
  omega

theorem problem2_3_sameExponentInteriorDoubleMantissa_normalized
    {m r : ℕ}
    (hm : ieeeSingleFormat.normalizedMantissa m)
    (hr : r < problem2_3_singleToDoubleMantissaScale) :
    ieeeDoubleFormat.normalizedMantissa
      (m * problem2_3_singleToDoubleMantissaScale + r) := by
  norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
    ieeeDoubleFormat, normalizedMantissa, mantissaInRange, minNormalMantissa]
    at hm hr ⊢
  omega

theorem problem2_3_sameExponentInteriorDoubleMantissa_normalized_of_mem
    {m n : ℕ}
    (hm : ieeeSingleFormat.normalizedMantissa m)
    (hn : n ∈ problem2_3_sameExponentInteriorDoubleMantissas m) :
    ieeeDoubleFormat.normalizedMantissa n := by
  have hbounds :=
    (problem2_3_sameExponentInteriorDoubleMantissas_mem_iff).mp hn
  norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
    ieeeDoubleFormat, normalizedMantissa, mantissaInRange, minNormalMantissa]
    at hm hbounds ⊢
  omega

set_option maxRecDepth 10000 in
theorem problem2_3_ieeeDouble_minNormalMagnitude_lt_ieeeSingle_normalized_false
    {m : ℕ} {e : ℤ}
    (hm : ieeeSingleFormat.normalizedMantissa m)
    (he : ieeeSingleFormat.exponentInRange e) :
    ieeeDoubleFormat.minNormalMagnitude <
      ieeeSingleFormat.normalizedValue false m e := by
  have hemin : (-126 : ℤ) ≤ e := by
    norm_num [ieeeSingleFormat, exponentInRange] at he
    omega
  have hpow :
      ieeeDoubleFormat.minNormalMagnitude < (2 : ℝ) ^ (e - 1) := by
    have hlt :
        (2 : ℝ) ^ (-1022 : ℤ) < (2 : ℝ) ^ (e - 1) :=
      zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2)
        (by omega : (-1022 : ℤ) < e - 1)
    simpa [ieeeDoubleFormat, minNormalMagnitude, betaR] using hlt
  have hleft :
      (2 : ℝ) ^ (e - 1) ≤
        ieeeSingleFormat.normalizedValue false m e := by
    simpa [ieeeSingleFormat, betaR] using
      (ieeeSingleFormat.normalizedValue_false_lower_power
        (m := m) (e := e) hm)
  exact lt_of_lt_of_le hpow hleft

theorem problem2_3_ieeeSingle_normalized_true_lt_neg_ieeeDouble_minNormalMagnitude
    {m : ℕ} {e : ℤ}
    (hm : ieeeSingleFormat.normalizedMantissa m)
    (he : ieeeSingleFormat.exponentInRange e) :
    ieeeSingleFormat.normalizedValue true m e <
      -ieeeDoubleFormat.minNormalMagnitude := by
  have hpos :=
    problem2_3_ieeeDouble_minNormalMagnitude_lt_ieeeSingle_normalized_false
      (m := m) (e := e) hm he
  rw [ieeeSingleFormat.normalizedValue_true_eq_neg_false]
  linarith

/-- The double mantissas strictly between the largest single mantissa at
exponent `e` and the smallest single mantissa at exponent `e + 1`. -/
def problem2_3_boundaryInteriorDoubleMantissas : Finset ℕ :=
  Finset.Icc
    (ieeeSingleFormat.maxNormalMantissa *
        problem2_3_singleToDoubleMantissaScale + 1)
    ieeeDoubleFormat.maxNormalMantissa

theorem problem2_3_boundaryInteriorDoubleMantissas_card :
    problem2_3_boundaryInteriorDoubleMantissas.card = 2 ^ 29 - 1 := by
  rw [problem2_3_boundaryInteriorDoubleMantissas, Nat.card_Icc]
  norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
    ieeeDoubleFormat, maxNormalMantissa]

theorem problem2_3_boundaryInteriorDoubleMantissas_mem_iff
    {n : ℕ} :
    n ∈ problem2_3_boundaryInteriorDoubleMantissas ↔
      ieeeSingleFormat.maxNormalMantissa *
          problem2_3_singleToDoubleMantissaScale < n ∧
        n < 2 ^ 53 := by
  rw [problem2_3_boundaryInteriorDoubleMantissas, Finset.mem_Icc]
  norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
    ieeeDoubleFormat, maxNormalMantissa]
  omega

theorem problem2_3_boundaryInteriorDoubleMantissa_normalized
    {r : ℕ}
    (hr : r < problem2_3_singleToDoubleMantissaScale) :
    ieeeDoubleFormat.normalizedMantissa
      (ieeeSingleFormat.maxNormalMantissa *
        problem2_3_singleToDoubleMantissaScale + r) := by
  norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
    ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
    minNormalMantissa, maxNormalMantissa] at hr ⊢
  omega

theorem problem2_3_boundaryInteriorDoubleMantissa_normalized_of_mem
    {n : ℕ}
    (hn : n ∈ problem2_3_boundaryInteriorDoubleMantissas) :
    ieeeDoubleFormat.normalizedMantissa n := by
  have hbounds :=
    (problem2_3_boundaryInteriorDoubleMantissas_mem_iff).mp hn
  norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
    ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
    minNormalMantissa, maxNormalMantissa] at hbounds ⊢
  omega

/-- The double mantissas strictly between the first two positive IEEE-single
subnormal numbers, represented at double exponent `-148`. -/
def problem2_3_smallestSubnormalInteriorDoubleMantissas : Finset ℕ :=
  Finset.Icc (2 ^ 52 + 1) (2 ^ 53 - 1)

theorem problem2_3_smallestSubnormalInteriorDoubleMantissas_card :
    problem2_3_smallestSubnormalInteriorDoubleMantissas.card = 2 ^ 52 - 1 := by
  rw [problem2_3_smallestSubnormalInteriorDoubleMantissas, Nat.card_Icc]
  norm_num

theorem problem2_3_smallestSubnormalInteriorDoubleMantissas_mem_iff
    {n : ℕ} :
    n ∈ problem2_3_smallestSubnormalInteriorDoubleMantissas ↔
      2 ^ 52 < n ∧ n < 2 ^ 53 := by
  rw [problem2_3_smallestSubnormalInteriorDoubleMantissas, Finset.mem_Icc]
  omega

theorem problem2_3_ieeeSingle_one_subnormalMantissa :
    ieeeSingleFormat.subnormalMantissa 1 := by
  norm_num [ieeeSingleFormat, subnormalMantissa, minNormalMantissa]

theorem problem2_3_ieeeSingle_two_subnormalMantissa :
    ieeeSingleFormat.subnormalMantissa 2 := by
  norm_num [ieeeSingleFormat, subnormalMantissa, minNormalMantissa]

theorem problem2_3_smallestSubnormalInteriorDoubleMantissa_normalized
    {r : ℕ}
    (hr : r < 2 ^ 52) :
    ieeeDoubleFormat.normalizedMantissa (2 ^ 52 + r) := by
  norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
    minNormalMantissa] at hr ⊢
  omega

/-- The double-mantissa refinement factor for a positive single-subnormal grid
step whose left mantissa lies in the dyadic block indexed by `s`. -/
def problem2_3_subnormalBlockScale (s : ℕ) : ℕ :=
  2 ^ (52 - s)

theorem problem2_3_ieeeSingle_subnormalMantissa_of_block
    {s m : ℕ}
    (hs : s ≤ 22)
    (hmlo : 2 ^ s ≤ m)
    (hmhi : m + 1 ≤ 2 ^ (s + 1)) :
    ieeeSingleFormat.subnormalMantissa m := by
  have hpow_pos : 0 < 2 ^ s :=
    pow_pos (by norm_num : (0 : ℕ) < 2) s
  have hmpos : 0 < m := lt_of_lt_of_le hpow_pos hmlo
  have hpow_le : 2 ^ (s + 1) ≤ 2 ^ 23 :=
    pow_le_pow_right₀ (by norm_num : (0 : ℕ) < 2) (by omega : s + 1 ≤ 23)
  have hm_lt : m < 2 ^ 23 :=
    lt_of_lt_of_le (Nat.lt_of_succ_le hmhi) hpow_le
  constructor
  · exact hmpos
  · simpa [ieeeSingleFormat, minNormalMantissa] using hm_lt

theorem problem2_3_exists_subnormalBlock_of_ieeeSingle_subnormalMantissa
    {m : ℕ}
    (hm : ieeeSingleFormat.subnormalMantissa m) :
    ∃ s : ℕ, s ≤ 22 ∧ 2 ^ s ≤ m ∧ m + 1 ≤ 2 ^ (s + 1) := by
  let s := Nat.log 2 m
  have hm_ne : m ≠ 0 := Nat.ne_of_gt hm.1
  have hm_lt : m < 2 ^ 23 := by
    simpa [ieeeSingleFormat, minNormalMantissa] using hm.2
  have hslo : 2 ^ s ≤ m := by
    exact (Nat.le_log_iff_pow_le Nat.one_lt_two hm_ne).mp (le_refl s)
  have hm_lt_next : m < 2 ^ (s + 1) := by
    simpa [s] using Nat.lt_pow_succ_log_self Nat.one_lt_two m
  have hmhi : m + 1 ≤ 2 ^ (s + 1) :=
    Nat.succ_le_of_lt hm_lt_next
  have hs_lt : s < 23 := by
    simpa [s] using Nat.log_lt_of_lt_pow hm_ne hm_lt
  exact ⟨s, by omega, hslo, hmhi⟩

theorem problem2_3_ieeeDouble_minNormalMagnitude_lt_ieeeSingle_subnormal_false
    {m : ℕ}
    (hm : ieeeSingleFormat.subnormalMantissa m) :
    ieeeDoubleFormat.minNormalMagnitude <
      ieeeSingleFormat.subnormalValue false m := by
  have hmin_lt_one :
      ieeeDoubleFormat.minNormalMagnitude <
        ieeeSingleFormat.subnormalValue false 1 := by
    have hpow :
        (2 : ℝ) ^ (-1022 : ℤ) < (2 : ℝ) ^ (-149 : ℤ) :=
      zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2)
        (by norm_num : (-1022 : ℤ) < -149)
    simpa [ieeeDoubleFormat, ieeeSingleFormat, minNormalMagnitude,
      subnormalValue, signValue, betaR] using hpow
  have hone_le :
      ieeeSingleFormat.subnormalValue false 1 ≤
        ieeeSingleFormat.subnormalValue false m :=
    ieeeSingleFormat.subnormalValue_false_one_le_of_subnormalMantissa hm
  exact lt_of_lt_of_le hmin_lt_one hone_le

theorem problem2_3_ieeeSingle_subnormal_true_lt_neg_ieeeDouble_minNormalMagnitude
    {m : ℕ}
    (hm : ieeeSingleFormat.subnormalMantissa m) :
    ieeeSingleFormat.subnormalValue true m <
      -ieeeDoubleFormat.minNormalMagnitude := by
  have hpos :=
    problem2_3_ieeeDouble_minNormalMagnitude_lt_ieeeSingle_subnormal_false
      (m := m) hm
  rw [show ieeeSingleFormat.subnormalValue true m =
      -ieeeSingleFormat.subnormalValue false m by
        exact ieeeSingleFormat.subnormalValue_not_eq_neg false m]
  linarith

/-- The double mantissas strictly between the single-subnormal grid points
`m * 2^-149` and `(m+1) * 2^-149`, represented in the double binade selected
by `s`. -/
def problem2_3_subnormalBlockInteriorDoubleMantissas
    (s m : ℕ) : Finset ℕ :=
  Finset.Icc (m * problem2_3_subnormalBlockScale s + 1)
    ((m + 1) * problem2_3_subnormalBlockScale s - 1)

theorem problem2_3_subnormalBlockInteriorDoubleMantissas_card
    (s m : ℕ) :
    (problem2_3_subnormalBlockInteriorDoubleMantissas s m).card =
      problem2_3_subnormalBlockScale s - 1 := by
  rw [problem2_3_subnormalBlockInteriorDoubleMantissas, Nat.card_Icc]
  have hsucc :
      (m + 1) * problem2_3_subnormalBlockScale s =
        m * problem2_3_subnormalBlockScale s +
          problem2_3_subnormalBlockScale s := by
    ring
  rw [hsucc]
  have hscale_pos : 0 < problem2_3_subnormalBlockScale s := by
    simp [problem2_3_subnormalBlockScale]
  omega

theorem problem2_3_subnormalBlockInteriorDoubleMantissas_mem_iff
    {s m n : ℕ} :
    n ∈ problem2_3_subnormalBlockInteriorDoubleMantissas s m ↔
      m * problem2_3_subnormalBlockScale s < n ∧
        n < (m + 1) * problem2_3_subnormalBlockScale s := by
  rw [problem2_3_subnormalBlockInteriorDoubleMantissas, Finset.mem_Icc]
  constructor
  · intro h
    constructor
    · exact Nat.lt_of_succ_le h.1
    · omega
  · intro h
    constructor
    · exact Nat.succ_le_of_lt h.1
    · omega

/-- Problem 2.3 first positive subnormal branch.  Between the first two
positive IEEE-single subnormal values, the interior IEEE-double values already
have cardinality `2^52 - 1`, not the normalized `2^29 - 1` count. -/
theorem problem2_3_ieeeDouble_between_first_two_ieeeSingle_subnormals
    {r : ℕ}
    (hrlo : 0 < r)
    (hrhi : r < 2 ^ 52) :
    ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.normalizedValue false (2 ^ 52 + r) (-148 : ℤ)) ∧
      ieeeSingleFormat.subnormalValue false 1 <
        ieeeDoubleFormat.normalizedValue false (2 ^ 52 + r) (-148 : ℤ) ∧
      ieeeDoubleFormat.normalizedValue false (2 ^ 52 + r) (-148 : ℤ) <
        ieeeSingleFormat.subnormalValue false 2 := by
  have heD : ieeeDoubleFormat.exponentInRange (-148 : ℤ) := by
    norm_num [ieeeDoubleFormat, exponentInRange]
  have hmD : ieeeDoubleFormat.normalizedMantissa (2 ^ 52 + r) :=
    problem2_3_smallestSubnormalInteriorDoubleMantissa_normalized hrhi
  constructor
  · exact Or.inr (Or.inl ⟨false, 2 ^ 52 + r, (-148 : ℤ), hmD, heD, rfl⟩)
  · constructor
    · have hn : 2 ^ 52 < 2 ^ 52 + r :=
        Nat.lt_add_of_pos_right hrlo
      have hcoeff :
          ((2 ^ 52 : ℕ) : ℝ) < ((2 ^ 52 + r : ℕ) : ℝ) := by
        exact_mod_cast hn
      have hscale_pos : 0 < (2 : ℝ) ^ ((-148 : ℤ) - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul := mul_lt_mul_of_pos_right hcoeff hscale_pos
      simp [ieeeSingleFormat, ieeeDoubleFormat, subnormalValue, normalizedValue,
        signValue, betaR]
      norm_num at hmul ⊢
      simpa [mul_assoc] using hmul
    · have hn : 2 ^ 52 + r < 2 ^ 53 := by
        norm_num at hrhi ⊢
        omega
      have hcoeff :
          ((2 ^ 52 + r : ℕ) : ℝ) < (2 : ℝ) ^ (53 : ℤ) := by
        norm_num at hn ⊢
        exact_mod_cast hn
      have hscale_pos : 0 < (2 : ℝ) ^ ((-148 : ℤ) - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul := mul_lt_mul_of_pos_right hcoeff hscale_pos
      simp [ieeeSingleFormat, ieeeDoubleFormat, subnormalValue, normalizedValue,
        signValue, betaR]
      norm_num at hmul ⊢
      simpa [mul_assoc] using hmul

/-- Branch-family data for Problem 2.3 adjacent nonzero IEEE-single gaps.

The constructors correspond to the same-exponent normalized, exponent-boundary
normalized, and dyadic-block subnormal branches formalized above.  This is a
single formulation for the proved branch family; it deliberately does not yet
claim that every finite IEEE-double value between arbitrary adjacent nonzero
single endpoints has been globally classified. -/
inductive Problem2_3IeeeSingleAdjacentGap where
  | sameExponent (negative : Bool) (m : ℕ) (e : ℤ)
      (hm : ieeeSingleFormat.normalizedMantissa m)
      (hmnext : ieeeSingleFormat.normalizedMantissa (m + 1))
      (he : ieeeSingleFormat.exponentInRange e)
  | boundary (negative : Bool) (e : ℤ)
      (he : ieeeSingleFormat.exponentInRange e)
      (heNext : ieeeSingleFormat.exponentInRange (e + 1))
  | subnormalBlock (negative : Bool) (s m : ℕ)
      (hs : s ≤ 22)
      (hmlo : 2 ^ s ≤ m)
      (hmhi : m + 1 ≤ 2 ^ (s + 1))

/-- The listed interior double mantissas for a Problem 2.3 branch gap. -/
def problem2_3_adjacentSingleGapInteriorDoubleMantissas :
    Problem2_3IeeeSingleAdjacentGap → Finset ℕ
  | .sameExponent _ m _ _ _ _ =>
      problem2_3_sameExponentInteriorDoubleMantissas m
  | .boundary _ _ _ _ =>
      problem2_3_boundaryInteriorDoubleMantissas
  | .subnormalBlock _ s m _ _ _ =>
      problem2_3_subnormalBlockInteriorDoubleMantissas s m

/-- The branch-dependent interior count for a Problem 2.3 adjacent single gap. -/
def problem2_3_adjacentSingleGapInteriorCount :
    Problem2_3IeeeSingleAdjacentGap → ℕ
  | .sameExponent _ _ _ _ _ _ => 2 ^ 29 - 1
  | .boundary _ _ _ _ => 2 ^ 29 - 1
  | .subnormalBlock _ s _ _ _ _ => problem2_3_subnormalBlockScale s - 1

/-- The left endpoint of the ordered signed single gap. -/
def problem2_3_adjacentSingleGapLeftValue :
    Problem2_3IeeeSingleAdjacentGap → ℝ
  | .sameExponent false m e _ _ _ =>
      ieeeSingleFormat.normalizedValue false m e
  | .sameExponent true m e _ _ _ =>
      ieeeSingleFormat.normalizedValue true (m + 1) e
  | .boundary false e _ _ =>
      ieeeSingleFormat.normalizedValue false ieeeSingleFormat.maxNormalMantissa e
  | .boundary true e _ _ =>
      ieeeSingleFormat.normalizedValue true
        ieeeSingleFormat.minNormalMantissa (e + 1)
  | .subnormalBlock false _ m _ _ _ =>
      ieeeSingleFormat.subnormalValue false m
  | .subnormalBlock true _ m _ _ _ =>
      ieeeSingleFormat.subnormalValue true (m + 1)

/-- The right endpoint of the ordered signed single gap. -/
def problem2_3_adjacentSingleGapRightValue :
    Problem2_3IeeeSingleAdjacentGap → ℝ
  | .sameExponent false m e _ _ _ =>
      ieeeSingleFormat.normalizedValue false (m + 1) e
  | .sameExponent true m e _ _ _ =>
      ieeeSingleFormat.normalizedValue true m e
  | .boundary false e _ _ =>
      ieeeSingleFormat.normalizedValue false
        ieeeSingleFormat.minNormalMantissa (e + 1)
  | .boundary true e _ _ =>
      ieeeSingleFormat.normalizedValue true ieeeSingleFormat.maxNormalMantissa e
  | .subnormalBlock false _ m _ _ _ =>
      ieeeSingleFormat.subnormalValue false (m + 1)
  | .subnormalBlock true _ m _ _ _ =>
      ieeeSingleFormat.subnormalValue true m

theorem problem2_3_exists_adjacentSingleGap_of_ieeeSingle_subnormalMantissa
    (negative : Bool) {m : ℕ}
    (hm : ieeeSingleFormat.subnormalMantissa m) :
    ∃ g : Problem2_3IeeeSingleAdjacentGap,
      problem2_3_adjacentSingleGapLeftValue g =
        (if negative then ieeeSingleFormat.subnormalValue true (m + 1)
          else ieeeSingleFormat.subnormalValue false m) ∧
      problem2_3_adjacentSingleGapRightValue g =
        (if negative then ieeeSingleFormat.subnormalValue true m
          else ieeeSingleFormat.subnormalValue false (m + 1)) := by
  rcases problem2_3_exists_subnormalBlock_of_ieeeSingle_subnormalMantissa hm
    with ⟨s, hs, hmlo, hmhi⟩
  refine ⟨.subnormalBlock negative s m hs hmlo hmhi, ?_, ?_⟩
  · cases negative <;> rfl
  · cases negative <;> rfl

/-- The double value associated with a candidate mantissa in a Problem 2.3 gap. -/
def problem2_3_adjacentSingleGapDoubleValue
    (g : Problem2_3IeeeSingleAdjacentGap) (n : ℕ) : ℝ :=
  match g with
  | .sameExponent negative _ e _ _ _ =>
      ieeeDoubleFormat.normalizedValue negative n e
  | .boundary negative e _ _ =>
      ieeeDoubleFormat.normalizedValue negative n e
  | .subnormalBlock negative s _ _ _ _ =>
      ieeeDoubleFormat.normalizedValue negative n ((s : ℤ) - 148)

theorem problem2_3_adjacentSingleGapInteriorDoubleMantissas_card
    (g : Problem2_3IeeeSingleAdjacentGap) :
    (problem2_3_adjacentSingleGapInteriorDoubleMantissas g).card =
      problem2_3_adjacentSingleGapInteriorCount g := by
  cases g with
  | sameExponent negative m e hm hmnext he =>
      exact problem2_3_sameExponentInteriorDoubleMantissas_card m
  | boundary negative e he heNext =>
      exact problem2_3_boundaryInteriorDoubleMantissas_card
  | subnormalBlock negative s m hs hmlo hmhi =>
      exact problem2_3_subnormalBlockInteriorDoubleMantissas_card s m

end FloatingPointFormat
end NumStability

end
