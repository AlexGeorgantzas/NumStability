import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Algorithms.Summation.Compensated.Kahan.Finite
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter04.Equation08.ReturnedSum

namespace NumStability

/-!
# A finite binary family testing Higham (4.8)--(4.9)

This module turns the four-input returned-Kahan trace from
`CompensatedSum` into a family of genuine finite, binary,
round-to-nearest-even formats whose precision tends to infinity.
-/

/-- Precision `k + 5`, with enough exponent range for the four-input trace. -/
def highamCh4KahanFiniteFamilyFormat (k : Nat) : FloatingPointFormat where
  beta := 2
  t := k + 5
  emin := 3
  emax := (k + 9 : Nat)
  beta_ge_two := by norm_num
  t_pos := by omega
  emin_le_emax := by omega

/-- The scale `p = 2^(k+5)` attached to the `k`th family member. -/
noncomputable def highamCh4KahanFiniteFamilyP (k : Nat) : Real :=
  (2 ^ (k + 5) : Nat)

theorem highamCh4KahanFiniteFamilyP_pos (k : Nat) :
    0 < highamCh4KahanFiniteFamilyP k := by
  rw [highamCh4KahanFiniteFamilyP]
  exact_mod_cast (Nat.pow_pos (by norm_num : 0 < (2 : Nat)) :
    0 < (2 : Nat) ^ (k + 5))

theorem highamCh4KahanFiniteFamilyP_ge_32 (k : Nat) :
    32 <= highamCh4KahanFiniteFamilyP k := by
  rw [highamCh4KahanFiniteFamilyP]
  have hpos : (0 : Nat) < 2 ^ k := Nat.pow_pos (by norm_num)
  have h : (1 : Nat) <= 2 ^ k := by omega
  exact_mod_cast (show (32 : Nat) <= 2 ^ (k + 5) by
    rw [pow_add]
    norm_num
    omega)

theorem highamCh4KahanFiniteFamilyP_eq (k : Nat) :
    highamCh4KahanFiniteFamilyP k =
      32 * ((2 ^ k : Nat) : Real) := by
  norm_num [highamCh4KahanFiniteFamilyP, Nat.cast_pow, pow_add]
  ring

theorem highamCh4KahanFiniteFamily_minNormalMantissa (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).minNormalMantissa =
      16 * 2 ^ k := by
  simp [highamCh4KahanFiniteFamilyFormat,
    FloatingPointFormat.minNormalMantissa, pow_add]
  ring

theorem highamCh4KahanFiniteFamily_maxNormalMantissa (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).maxNormalMantissa =
      32 * 2 ^ k - 1 := by
  simp [highamCh4KahanFiniteFamilyFormat,
    FloatingPointFormat.maxNormalMantissa, pow_add]
  ring_nf

private theorem highamCh4KahanFiniteFamily_twoPow_pos (k : Nat) :
    0 < (2 : Nat) ^ k := Nat.pow_pos (by norm_num)

private theorem highamCh4KahanFiniteFamily_normalizedMantissa_of_bounds
    (k m : Nat) (hlo : 16 * 2 ^ k <= m) (hi : m < 32 * 2 ^ k) :
    (highamCh4KahanFiniteFamilyFormat k).normalizedMantissa m := by
  rw [FloatingPointFormat.normalizedMantissa,
    highamCh4KahanFiniteFamily_minNormalMantissa]
  refine And.intro hlo ?_
  simpa [FloatingPointFormat.mantissaInRange,
    highamCh4KahanFiniteFamilyFormat, pow_add,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hi

private theorem highamCh4KahanFiniteFamily_normalizedMantissa_22 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).normalizedMantissa
      (22 * 2 ^ k) := by
  rw [FloatingPointFormat.normalizedMantissa,
    highamCh4KahanFiniteFamily_minNormalMantissa]
  simp [FloatingPointFormat.mantissaInRange,
    highamCh4KahanFiniteFamilyFormat, pow_add]
  have h := highamCh4KahanFiniteFamily_twoPow_pos k
  omega

private theorem highamCh4KahanFiniteFamily_normalizedMantissa_16_add_one
    (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).normalizedMantissa
      (16 * 2 ^ k + 1) := by
  apply highamCh4KahanFiniteFamily_normalizedMantissa_of_bounds
  · omega
  · have h := highamCh4KahanFiniteFamily_twoPow_pos k
    omega

private theorem highamCh4KahanFiniteFamily_normalizedMantissa_16_add
    (k d : Nat) (hd : d <= 7) :
    (highamCh4KahanFiniteFamilyFormat k).normalizedMantissa
      (16 * 2 ^ k + d) := by
  apply highamCh4KahanFiniteFamily_normalizedMantissa_of_bounds
  · omega
  · have h := highamCh4KahanFiniteFamily_twoPow_pos k
    omega

private theorem highamCh4KahanFiniteFamily_normalizedMantissa_20_add
    (k d : Nat) (hd : d <= 2) :
    (highamCh4KahanFiniteFamilyFormat k).normalizedMantissa
      (20 * 2 ^ k + d) := by
  apply highamCh4KahanFiniteFamily_normalizedMantissa_of_bounds
  · have h := highamCh4KahanFiniteFamily_twoPow_pos k
    omega
  · have h := highamCh4KahanFiniteFamily_twoPow_pos k
    omega

private theorem highamCh4KahanFiniteFamily_normalizedMantissa_max (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).normalizedMantissa
      (32 * 2 ^ k - 1) := by
  simpa [highamCh4KahanFiniteFamily_maxNormalMantissa] using
    (highamCh4KahanFiniteFamilyFormat k).maxNormalMantissa_normalized

private theorem highamCh4KahanFiniteFamily_exponentInRange_3 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).exponentInRange (3 : Int) := by
  simp [FloatingPointFormat.exponentInRange,
    highamCh4KahanFiniteFamilyFormat]
  omega

private theorem highamCh4KahanFiniteFamily_exponentInRange_4 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).exponentInRange (4 : Int) := by
  simp [FloatingPointFormat.exponentInRange,
    highamCh4KahanFiniteFamilyFormat]
  omega

private theorem highamCh4KahanFiniteFamily_exponentInRange_5 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).exponentInRange (5 : Int) := by
  simp [FloatingPointFormat.exponentInRange,
    highamCh4KahanFiniteFamilyFormat]
  omega

private theorem highamCh4KahanFiniteFamily_exponentInRange_7 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).exponentInRange
      ((k + 7 : Nat) : Int) := by
  simp [FloatingPointFormat.exponentInRange,
    highamCh4KahanFiniteFamilyFormat]
  omega

private theorem highamCh4KahanFiniteFamily_exponentInRange_8 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).exponentInRange
      ((k + 8 : Nat) : Int) := by
  simp [FloatingPointFormat.exponentInRange,
    highamCh4KahanFiniteFamilyFormat]
  omega

private theorem highamCh4KahanFiniteFamily_exponentInRange_9 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).exponentInRange
      ((k + 9 : Nat) : Int) := by
  simp [FloatingPointFormat.exponentInRange,
    highamCh4KahanFiniteFamilyFormat]
  omega

private theorem highamCh4KahanFiniteFamily_normalizedSystem_of_value
    (k : Nat) (negative : Bool) (m : Nat) (e : Int)
    (hm : (highamCh4KahanFiniteFamilyFormat k).normalizedMantissa m)
    (he : (highamCh4KahanFiniteFamilyFormat k).exponentInRange e) :
    (highamCh4KahanFiniteFamilyFormat k).normalizedSystem
      ((highamCh4KahanFiniteFamilyFormat k).normalizedValue negative m e) := by
  exact Exists.intro negative
    (Exists.intro m (Exists.intro e (And.intro hm (And.intro he rfl))))

private theorem highamCh4KahanFiniteFamily_finiteSystem_of_value
    (k : Nat) (negative : Bool) (m : Nat) (e : Int)
    (hm : (highamCh4KahanFiniteFamilyFormat k).normalizedMantissa m)
    (he : (highamCh4KahanFiniteFamilyFormat k).exponentInRange e) :
    (highamCh4KahanFiniteFamilyFormat k).finiteSystem
      ((highamCh4KahanFiniteFamilyFormat k).normalizedValue negative m e) := by
  exact Or.inr (Or.inl
    (highamCh4KahanFiniteFamily_normalizedSystem_of_value k negative m e hm he))

private theorem highamCh4KahanFiniteFamily_normalizedValue_22 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).normalizedValue
      false (22 * 2 ^ k) (5 : Int) = 22 := by
  have hexp : (5 : Int) - ((k + 5 : Nat) : Int) = -(k : Int) := by omega
  rw [FloatingPointFormat.normalizedValue]
  simp only [highamCh4KahanFiniteFamilyFormat,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, if_false,
    one_mul, hexp, zpow_neg]
  norm_num [Nat.cast_mul, Nat.cast_pow]

private theorem highamCh4KahanFiniteFamily_normalizedValue_16_add_one
    (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).normalizedValue
      false (16 * 2 ^ k + 1) ((k + 7 : Nat) : Int) =
      2 * highamCh4KahanFiniteFamilyP k + 4 := by
  have hexp : ((k + 7 : Nat) : Int) - ((k + 5 : Nat) : Int) = 2 := by omega
  rw [FloatingPointFormat.normalizedValue]
  simp only [highamCh4KahanFiniteFamilyFormat,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR,
    hexp]
  norm_num [highamCh4KahanFiniteFamilyP, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, pow_add]
  ring

private theorem highamCh4KahanFiniteFamily_normalizedValue_exp7
    (k m : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).normalizedValue
      false m ((k + 7 : Nat) : Int) = 4 * (m : Real) := by
  have hexp : ((k + 7 : Nat) : Int) - ((k + 5 : Nat) : Int) = 2 := by omega
  rw [FloatingPointFormat.normalizedValue]
  simp [highamCh4KahanFiniteFamilyFormat,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, hexp]
  ring

private theorem highamCh4KahanFiniteFamily_normalizedValue_exp8
    (k m : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).normalizedValue
      false m ((k + 8 : Nat) : Int) = 8 * (m : Real) := by
  have hexp : ((k + 8 : Nat) : Int) - ((k + 5 : Nat) : Int) = 3 := by omega
  rw [FloatingPointFormat.normalizedValue]
  simp [highamCh4KahanFiniteFamilyFormat,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, hexp]
  ring

private theorem highamCh4KahanFiniteFamily_normalizedValue_exp9
    (k m : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).normalizedValue
      false m ((k + 9 : Nat) : Int) = 16 * (m : Real) := by
  have hexp : ((k + 9 : Nat) : Int) - ((k + 5 : Nat) : Int) = 4 := by omega
  rw [FloatingPointFormat.normalizedValue]
  simp [highamCh4KahanFiniteFamilyFormat,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, hexp]
  ring

private theorem highamCh4KahanFiniteFamily_normalizedValue_exp7_16_add
    (k d : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).normalizedValue false
      (16 * 2 ^ k + d) ((k + 7 : Nat) : Int) =
      2 * highamCh4KahanFiniteFamilyP k + 4 * d := by
  rw [highamCh4KahanFiniteFamily_normalizedValue_exp7,
    highamCh4KahanFiniteFamilyP_eq]
  norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  ring

private theorem highamCh4KahanFiniteFamily_normalizedValue_exp8_max
    (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).normalizedValue false
      (32 * 2 ^ k - 1) ((k + 8 : Nat) : Int) =
      8 * highamCh4KahanFiniteFamilyP k - 8 := by
  rw [highamCh4KahanFiniteFamily_normalizedValue_exp8,
    highamCh4KahanFiniteFamilyP_eq]
  have hpow := highamCh4KahanFiniteFamily_twoPow_pos k
  rw [Nat.cast_sub (by omega : 1 <= 32 * 2 ^ k)]
  norm_num [Nat.cast_mul, Nat.cast_pow]
  ring

private theorem highamCh4KahanFiniteFamily_normalizedValue_exp9_16_add
    (k d : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).normalizedValue false
      (16 * 2 ^ k + d) ((k + 9 : Nat) : Int) =
      8 * highamCh4KahanFiniteFamilyP k + 16 * d := by
  rw [highamCh4KahanFiniteFamily_normalizedValue_exp9,
    highamCh4KahanFiniteFamilyP_eq]
  norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  ring

private theorem highamCh4KahanFiniteFamily_normalizedValue_exp9_20_add
    (k d : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).normalizedValue false
      (20 * 2 ^ k + d) ((k + 9 : Nat) : Int) =
      10 * highamCh4KahanFiniteFamilyP k + 16 * d := by
  rw [highamCh4KahanFiniteFamily_normalizedValue_exp9,
    highamCh4KahanFiniteFamilyP_eq]
  norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  ring

private theorem highamCh4KahanFiniteFamily_normalizedValue_4 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).normalizedValue
      false (16 * 2 ^ k) (3 : Int) = 4 := by
  have hexp : (3 : Int) - ((k + 5 : Nat) : Int) = -(k : Int) - 2 := by omega
  rw [FloatingPointFormat.normalizedValue]
  simp only [highamCh4KahanFiniteFamilyFormat,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, hexp]
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  have hneg : (-(k : Int) - 2) = -((k + 2 : Nat) : Int) := by omega
  rw [hneg, zpow_neg]
  rw [zpow_natCast, pow_add]
  norm_num [Nat.cast_mul, Nat.cast_pow]
  field_simp
  norm_num

private theorem highamCh4KahanFiniteFamily_normalizedValue_8 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).normalizedValue
      false (16 * 2 ^ k) (4 : Int) = 8 := by
  have hexp : (4 : Int) - ((k + 5 : Nat) : Int) = -(k : Int) - 1 := by omega
  rw [FloatingPointFormat.normalizedValue]
  simp only [highamCh4KahanFiniteFamilyFormat,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR, hexp]
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  have hneg : (-(k : Int) - 1) = -((k + 1 : Nat) : Int) := by omega
  rw [hneg, zpow_neg]
  rw [zpow_natCast, pow_add]
  norm_num [Nat.cast_mul, Nat.cast_pow]
  field_simp
  norm_num

private theorem highamCh4KahanFiniteFamily_finiteNormalRange_between
    {fmt : FloatingPointFormat} {left x right : Real}
    (hleft : fmt.normalizedSystem left)
    (hright : fmt.normalizedSystem right)
    (hleftPos : 0 < left)
    (hbetween : left < x ∧ x < right) :
    fmt.finiteNormalRange x := by
  have hleftRange := fmt.normalizedSystem_finiteNormalRange hleft
  have hrightRange := fmt.normalizedSystem_finiteNormalRange hright
  have hxPos : 0 < x := lt_trans hleftPos hbetween.1
  have hrightPos : 0 < right := lt_trans hxPos hbetween.2
  rw [FloatingPointFormat.finiteNormalRange, abs_of_pos hxPos]
  constructor
  · calc
      fmt.minNormalMagnitude <= |left| := hleftRange.1
      _ = left := abs_of_pos hleftPos
      _ <= x := le_of_lt hbetween.1
  · calc
      x <= right := le_of_lt hbetween.2
      _ = |right| := (abs_of_pos hrightPos).symm
      _ <= fmt.maxFiniteMagnitude := hrightRange.2

private theorem highamCh4KahanFiniteFamily_sameExponentTie_left_even
    (k : Nat) {x left right : Real} {m : Nat} {e : Int}
    (hm : (highamCh4KahanFiniteFamilyFormat k).normalizedMantissa m)
    (hm1 : (highamCh4KahanFiniteFamilyFormat k).normalizedMantissa (m + 1))
    (he : (highamCh4KahanFiniteFamilyFormat k).exponentInRange e)
    (hleft : left =
      (highamCh4KahanFiniteFamilyFormat k).normalizedValue false m e)
    (hright : right =
      (highamCh4KahanFiniteFamilyFormat k).normalizedValue false (m + 1) e)
    (hleftPos : 0 < left)
    (hstrict : left < x ∧ x < right)
    (htie : |x - left| = |x - right|)
    (heven : FloatingPointFormat.evenMantissa m) :
    (highamCh4KahanFiniteFamilyFormat k).finiteRoundToEven x = left := by
  let fmt := highamCh4KahanFiniteFamilyFormat k
  have hstruct : fmt.sameExponentAdjacentNormalized left right := by
    exact Exists.intro false (Exists.intro m (Exists.intro e
      (And.intro hm (And.intro hm1 (Or.inl (And.intro hleft hright))))))
  have hadj : fmt.realOrderAdjacentNormalized left right :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hleftNorm : fmt.normalizedSystem left := by
    simpa [hleft] using
      highamCh4KahanFiniteFamily_normalizedSystem_of_value k false m e hm he
  have hrightNorm : fmt.normalizedSystem right := by
    simpa [hright] using
      highamCh4KahanFiniteFamily_normalizedSystem_of_value
        k false (m + 1) e hm1 he
  have hrange : fmt.finiteNormalRange x :=
    highamCh4KahanFiniteFamily_finiteNormalRange_between
      hleftNorm hrightNorm hleftPos hstrict
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hrange
  exact
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
      hpolicy hadj hstrict hm hleft htie heven

private theorem highamCh4KahanFiniteFamily_sameExponentTie_right_odd
    (k : Nat) {x left right : Real} {m : Nat} {e : Int}
    (hm : (highamCh4KahanFiniteFamilyFormat k).normalizedMantissa m)
    (hm1 : (highamCh4KahanFiniteFamilyFormat k).normalizedMantissa (m + 1))
    (he : (highamCh4KahanFiniteFamilyFormat k).exponentInRange e)
    (hleft : left =
      (highamCh4KahanFiniteFamilyFormat k).normalizedValue false m e)
    (hright : right =
      (highamCh4KahanFiniteFamilyFormat k).normalizedValue false (m + 1) e)
    (hleftPos : 0 < left)
    (hstrict : left < x ∧ x < right)
    (htie : |x - left| = |x - right|)
    (hodd : ¬ FloatingPointFormat.evenMantissa m) :
    (highamCh4KahanFiniteFamilyFormat k).finiteRoundToEven x = right := by
  let fmt := highamCh4KahanFiniteFamilyFormat k
  have hstruct : fmt.sameExponentAdjacentNormalized left right := by
    exact Exists.intro false (Exists.intro m (Exists.intro e
      (And.intro hm (And.intro hm1 (Or.inl (And.intro hleft hright))))))
  have hadj : fmt.realOrderAdjacentNormalized left right :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hleftNorm : fmt.normalizedSystem left := by
    simpa [hleft] using
      highamCh4KahanFiniteFamily_normalizedSystem_of_value k false m e hm he
  have hrightNorm : fmt.normalizedSystem right := by
    simpa [hright] using
      highamCh4KahanFiniteFamily_normalizedSystem_of_value
        k false (m + 1) e hm1 he
  have hrange : fmt.finiteNormalRange x :=
    highamCh4KahanFiniteFamily_finiteNormalRange_between
      hleftNorm hrightNorm hleftPos hstrict
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hrange
  exact
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hm hleft htie hodd

private theorem highamCh4KahanFiniteFamily_boundaryTie_right_odd
    (k : Nat) {x left right : Real} {e : Int}
    (he : (highamCh4KahanFiniteFamilyFormat k).exponentInRange e)
    (he1 : (highamCh4KahanFiniteFamilyFormat k).exponentInRange (e + 1))
    (hleft : left =
      (highamCh4KahanFiniteFamilyFormat k).normalizedValue false
        (highamCh4KahanFiniteFamilyFormat k).maxNormalMantissa e)
    (hright : right =
      (highamCh4KahanFiniteFamilyFormat k).normalizedValue false
        (highamCh4KahanFiniteFamilyFormat k).minNormalMantissa (e + 1))
    (hleftPos : 0 < left)
    (hstrict : left < x ∧ x < right)
    (htie : |x - left| = |x - right|)
    (hodd : ¬ FloatingPointFormat.evenMantissa
      (highamCh4KahanFiniteFamilyFormat k).maxNormalMantissa) :
    (highamCh4KahanFiniteFamilyFormat k).finiteRoundToEven x = right := by
  let fmt := highamCh4KahanFiniteFamilyFormat k
  have hm : fmt.normalizedMantissa fmt.maxNormalMantissa :=
    fmt.maxNormalMantissa_normalized
  have hmin : fmt.normalizedMantissa fmt.minNormalMantissa :=
    fmt.minNormalMantissa_normalized
  have hboundary : fmt.boundaryAdjacentNormalized left right := by
    exact Exists.intro false (Exists.intro e (Or.inl (And.intro hleft hright)))
  have hadj : fmt.realOrderAdjacentNormalized left right :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hleftNorm : fmt.normalizedSystem left := by
    simpa [hleft] using
      highamCh4KahanFiniteFamily_normalizedSystem_of_value
        k false fmt.maxNormalMantissa e hm he
  have hrightNorm : fmt.normalizedSystem right := by
    simpa [hright] using
      highamCh4KahanFiniteFamily_normalizedSystem_of_value
        k false fmt.minNormalMantissa (e + 1) hmin he1
  have hrange : fmt.finiteNormalRange x :=
    highamCh4KahanFiniteFamily_finiteNormalRange_between
      hleftNorm hrightNorm hleftPos hstrict
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hrange
  exact
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hm hleft htie hodd

/-- The second stored-sum tie rounds toward the even lower endpoint. -/
theorem highamCh4KahanFiniteFamily_round_twoP_add_26 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteRoundToEven
        (2 * highamCh4KahanFiniteFamilyP k + 26) =
      2 * highamCh4KahanFiniteFamilyP k + 24 := by
  apply highamCh4KahanFiniteFamily_sameExponentTie_left_even k
    (m := 16 * 2 ^ k + 6) (e := ((k + 7 : Nat) : Int))
    (left := 2 * highamCh4KahanFiniteFamilyP k + 24)
    (right := 2 * highamCh4KahanFiniteFamilyP k + 28)
  · exact highamCh4KahanFiniteFamily_normalizedMantissa_16_add k 6 (by omega)
  · simpa [Nat.add_assoc] using
      highamCh4KahanFiniteFamily_normalizedMantissa_16_add k 7 (by omega)
  · exact highamCh4KahanFiniteFamily_exponentInRange_7 k
  · convert (highamCh4KahanFiniteFamily_normalizedValue_exp7_16_add k 6).symm using 1 <;>
      norm_num
  · convert (highamCh4KahanFiniteFamily_normalizedValue_exp7_16_add k 7).symm using 1 <;>
      norm_num
  · nlinarith [highamCh4KahanFiniteFamilyP_pos k]
  · constructor <;> norm_num
  · ring_nf
    rw [abs_neg]
    congr 1
  · simp [FloatingPointFormat.evenMantissa, Nat.add_mod, Nat.mul_mod]

/-- The compensation subtraction tie rounds to `2p`. -/
theorem highamCh4KahanFiniteFamily_round_twoP_add_2 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteRoundToEven
        (2 * highamCh4KahanFiniteFamilyP k + 2) =
      2 * highamCh4KahanFiniteFamilyP k := by
  apply highamCh4KahanFiniteFamily_sameExponentTie_left_even k
    (m := 16 * 2 ^ k) (e := ((k + 7 : Nat) : Int))
    (left := 2 * highamCh4KahanFiniteFamilyP k)
    (right := 2 * highamCh4KahanFiniteFamilyP k + 4)
  · simpa using highamCh4KahanFiniteFamily_normalizedMantissa_16_add k 0 (by omega)
  · simpa using highamCh4KahanFiniteFamily_normalizedMantissa_16_add k 1 (by omega)
  · exact highamCh4KahanFiniteFamily_exponentInRange_7 k
  · convert (highamCh4KahanFiniteFamily_normalizedValue_exp7_16_add k 0).symm using 1 <;>
      norm_num
  · convert (highamCh4KahanFiniteFamily_normalizedValue_exp7_16_add k 1).symm using 1 <;>
      norm_num
  · nlinarith [highamCh4KahanFiniteFamilyP_pos k]
  · constructor <;> norm_num
  · ring_nf
    rw [abs_neg]
  · simp [FloatingPointFormat.evenMantissa, Nat.add_mod, Nat.mul_mod]

/-- The third corrected input is the midpoint between the largest mantissa at
one exponent and the even smallest mantissa at the next exponent. -/
theorem highamCh4KahanFiniteFamily_round_eightP_sub_4 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteRoundToEven
        (8 * highamCh4KahanFiniteFamilyP k - 4) =
      8 * highamCh4KahanFiniteFamilyP k := by
  apply highamCh4KahanFiniteFamily_boundaryTie_right_odd k
    (e := ((k + 8 : Nat) : Int))
    (left := 8 * highamCh4KahanFiniteFamilyP k - 8)
    (right := 8 * highamCh4KahanFiniteFamilyP k)
  · exact highamCh4KahanFiniteFamily_exponentInRange_8 k
  · convert highamCh4KahanFiniteFamily_exponentInRange_9 k using 1 <;> omega
  · rw [highamCh4KahanFiniteFamily_maxNormalMantissa]
    exact (highamCh4KahanFiniteFamily_normalizedValue_exp8_max k).symm
  · rw [highamCh4KahanFiniteFamily_minNormalMantissa]
    convert (highamCh4KahanFiniteFamily_normalizedValue_exp9_16_add k 0).symm using 1 <;>
      norm_num
  · nlinarith [highamCh4KahanFiniteFamilyP_ge_32 k]
  · constructor <;> norm_num
  · ring_nf
    rw [abs_neg]
    congr 1
  · rw [highamCh4KahanFiniteFamily_maxNormalMantissa]
    unfold FloatingPointFormat.evenMantissa
    have hpow := highamCh4KahanFiniteFamily_twoPow_pos k
    omega

/-- The third stored-sum tie rounds toward the even successor. -/
theorem highamCh4KahanFiniteFamily_round_tenP_add_24 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteRoundToEven
        (10 * highamCh4KahanFiniteFamilyP k + 24) =
      10 * highamCh4KahanFiniteFamilyP k + 32 := by
  apply highamCh4KahanFiniteFamily_sameExponentTie_right_odd k
    (m := 20 * 2 ^ k + 1) (e := ((k + 9 : Nat) : Int))
    (left := 10 * highamCh4KahanFiniteFamilyP k + 16)
    (right := 10 * highamCh4KahanFiniteFamilyP k + 32)
  · exact highamCh4KahanFiniteFamily_normalizedMantissa_20_add k 1 (by omega)
  · simpa [Nat.add_assoc] using
      highamCh4KahanFiniteFamily_normalizedMantissa_20_add k 2 (by omega)
  · exact highamCh4KahanFiniteFamily_exponentInRange_9 k
  · convert (highamCh4KahanFiniteFamily_normalizedValue_exp9_20_add k 1).symm using 1 <;>
      norm_num
  · convert (highamCh4KahanFiniteFamily_normalizedValue_exp9_20_add k 2).symm using 1 <;>
      norm_num
  · nlinarith [highamCh4KahanFiniteFamilyP_pos k]
  · constructor <;> norm_num
  · ring_nf
    rw [abs_neg]
    congr 1
  · unfold FloatingPointFormat.evenMantissa
    simp [Nat.add_mod, Nat.mul_mod]

/-- The third compensation subtraction tie rounds to `8p`. -/
theorem highamCh4KahanFiniteFamily_round_eightP_add_8 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteRoundToEven
        (8 * highamCh4KahanFiniteFamilyP k + 8) =
      8 * highamCh4KahanFiniteFamilyP k := by
  apply highamCh4KahanFiniteFamily_sameExponentTie_left_even k
    (m := 16 * 2 ^ k) (e := ((k + 9 : Nat) : Int))
    (left := 8 * highamCh4KahanFiniteFamilyP k)
    (right := 8 * highamCh4KahanFiniteFamilyP k + 16)
  · simpa using highamCh4KahanFiniteFamily_normalizedMantissa_16_add k 0 (by omega)
  · simpa using highamCh4KahanFiniteFamily_normalizedMantissa_16_add k 1 (by omega)
  · exact highamCh4KahanFiniteFamily_exponentInRange_9 k
  · convert (highamCh4KahanFiniteFamily_normalizedValue_exp9_16_add k 0).symm using 1 <;>
      norm_num
  · convert (highamCh4KahanFiniteFamily_normalizedValue_exp9_16_add k 1).symm using 1 <;>
      norm_num
  · nlinarith [highamCh4KahanFiniteFamilyP_pos k]
  · constructor <;> norm_num
  · ring_nf
    norm_num
  · simp [FloatingPointFormat.evenMantissa, Nat.add_mod, Nat.mul_mod]

private theorem highamCh4KahanFiniteFamily_finiteSystem_zero (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteSystem (0 : Real) :=
  Or.inl rfl

private theorem highamCh4KahanFiniteFamily_finiteSystem_22 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteSystem (22 : Real) := by
  have h := highamCh4KahanFiniteFamily_finiteSystem_of_value k false
    (22 * 2 ^ k) (5 : Int)
    (highamCh4KahanFiniteFamily_normalizedMantissa_22 k)
    (highamCh4KahanFiniteFamily_exponentInRange_5 k)
  simpa [highamCh4KahanFiniteFamily_normalizedValue_22] using h

private theorem highamCh4KahanFiniteFamily_finiteSystem_neg22 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteSystem (-22 : Real) :=
  (highamCh4KahanFiniteFamilyFormat k).finiteSystem_neg
    (highamCh4KahanFiniteFamily_finiteSystem_22 k)

private theorem highamCh4KahanFiniteFamily_finiteSystem_4 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteSystem (4 : Real) := by
  have hm : (highamCh4KahanFiniteFamilyFormat k).normalizedMantissa
      (16 * 2 ^ k) := by
    simpa using highamCh4KahanFiniteFamily_normalizedMantissa_16_add k 0 (by omega)
  have h := highamCh4KahanFiniteFamily_finiteSystem_of_value k false
    (16 * 2 ^ k) (3 : Int) hm
    (highamCh4KahanFiniteFamily_exponentInRange_3 k)
  simpa [highamCh4KahanFiniteFamily_normalizedValue_4] using h

private theorem highamCh4KahanFiniteFamily_finiteSystem_neg4 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteSystem (-4 : Real) :=
  (highamCh4KahanFiniteFamilyFormat k).finiteSystem_neg
    (highamCh4KahanFiniteFamily_finiteSystem_4 k)

private theorem highamCh4KahanFiniteFamily_finiteSystem_8 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteSystem (8 : Real) := by
  have hm : (highamCh4KahanFiniteFamilyFormat k).normalizedMantissa
      (16 * 2 ^ k) := by
    simpa using highamCh4KahanFiniteFamily_normalizedMantissa_16_add k 0 (by omega)
  have h := highamCh4KahanFiniteFamily_finiteSystem_of_value k false
    (16 * 2 ^ k) (4 : Int) hm
    (highamCh4KahanFiniteFamily_exponentInRange_4 k)
  simpa [highamCh4KahanFiniteFamily_normalizedValue_8] using h

private theorem highamCh4KahanFiniteFamily_finiteSystem_twoP_add_4 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteSystem
      (2 * highamCh4KahanFiniteFamilyP k + 4) := by
  have h := highamCh4KahanFiniteFamily_finiteSystem_of_value k false
    (16 * 2 ^ k + 1) ((k + 7 : Nat) : Int)
    (highamCh4KahanFiniteFamily_normalizedMantissa_16_add k 1 (by omega))
    (highamCh4KahanFiniteFamily_exponentInRange_7 k)
  rw [highamCh4KahanFiniteFamily_normalizedValue_exp7_16_add] at h
  norm_num at h ⊢
  exact h

private theorem highamCh4KahanFiniteFamily_finiteSystem_neg_twoP_add_4 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteSystem
      (-(2 * highamCh4KahanFiniteFamilyP k + 4)) :=
  (highamCh4KahanFiniteFamilyFormat k).finiteSystem_neg
    (highamCh4KahanFiniteFamily_finiteSystem_twoP_add_4 k)

private theorem highamCh4KahanFiniteFamily_finiteSystem_twoP (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteSystem
      (2 * highamCh4KahanFiniteFamilyP k) := by
  have h := highamCh4KahanFiniteFamily_finiteSystem_of_value k false
    (16 * 2 ^ k) ((k + 7 : Nat) : Int)
    (by simpa using highamCh4KahanFiniteFamily_normalizedMantissa_16_add k 0 (by omega))
    (highamCh4KahanFiniteFamily_exponentInRange_7 k)
  convert h using 1
  simpa using (highamCh4KahanFiniteFamily_normalizedValue_exp7_16_add k 0).symm

private theorem highamCh4KahanFiniteFamily_finiteSystem_eightP_sub_8 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteSystem
      (8 * highamCh4KahanFiniteFamilyP k - 8) := by
  have h := highamCh4KahanFiniteFamily_finiteSystem_of_value k false
    (32 * 2 ^ k - 1) ((k + 8 : Nat) : Int)
    (highamCh4KahanFiniteFamily_normalizedMantissa_max k)
    (highamCh4KahanFiniteFamily_exponentInRange_8 k)
  rw [highamCh4KahanFiniteFamily_normalizedValue_exp8_max] at h
  exact h

private theorem highamCh4KahanFiniteFamily_finiteSystem_neg_eightP_sub_8 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteSystem
      (-(8 * highamCh4KahanFiniteFamilyP k - 8)) :=
  (highamCh4KahanFiniteFamilyFormat k).finiteSystem_neg
    (highamCh4KahanFiniteFamily_finiteSystem_eightP_sub_8 k)

private theorem highamCh4KahanFiniteFamily_finiteSystem_eightP (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteSystem
      (8 * highamCh4KahanFiniteFamilyP k) := by
  have h := highamCh4KahanFiniteFamily_finiteSystem_of_value k false
    (16 * 2 ^ k) ((k + 9 : Nat) : Int)
    (by simpa using highamCh4KahanFiniteFamily_normalizedMantissa_16_add k 0 (by omega))
    (highamCh4KahanFiniteFamily_exponentInRange_9 k)
  convert h using 1
  simpa using (highamCh4KahanFiniteFamily_normalizedValue_exp9_16_add k 0).symm

private theorem highamCh4KahanFiniteFamily_finiteSystem_tenP_add_32 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteSystem
      (10 * highamCh4KahanFiniteFamilyP k + 32) := by
  have h := highamCh4KahanFiniteFamily_finiteSystem_of_value k false
    (20 * 2 ^ k + 2) ((k + 9 : Nat) : Int)
    (highamCh4KahanFiniteFamily_normalizedMantissa_20_add k 2 (by omega))
    (highamCh4KahanFiniteFamily_exponentInRange_9 k)
  rw [highamCh4KahanFiniteFamily_normalizedValue_exp9_20_add] at h
  norm_num at h ⊢
  exact h

private theorem highamCh4KahanFiniteFamily_finiteSystem_neg_tenP_add_32 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteSystem
      (-(10 * highamCh4KahanFiniteFamilyP k + 32)) :=
  (highamCh4KahanFiniteFamilyFormat k).finiteSystem_neg
    (highamCh4KahanFiniteFamily_finiteSystem_tenP_add_32 k)

private theorem highamCh4KahanFiniteFamily_finiteRoundToEvenOp_eq
    (k : Nat) {op : BasicOp} {x y z : Real}
    (hz : BasicOp.exact op x y = z)
    (hfin : (highamCh4KahanFiniteFamilyFormat k).finiteSystem z) :
    (highamCh4KahanFiniteFamilyFormat k).finiteRoundToEvenOp op x y = z := by
  have hfin' : (highamCh4KahanFiniteFamilyFormat k).finiteSystem
      (BasicOp.exact op x y) := by simpa [hz] using hfin
  simpa [hz] using
    (highamCh4KahanFiniteFamilyFormat k).finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := op) (x := x) (y := y) hfin'

private theorem highamCh4KahanFiniteFamily_round_neg
    (k : Nat) (x : Real) :
    (highamCh4KahanFiniteFamilyFormat k).finiteRoundToEven (-x) =
      -(highamCh4KahanFiniteFamilyFormat k).finiteRoundToEven x := by
  exact (highamCh4KahanFiniteFamilyFormat k).finiteRoundToEven_neg
    (by simp [highamCh4KahanFiniteFamilyFormat,
      FloatingPointFormat.evenMantissa])
    (by simp [highamCh4KahanFiniteFamilyFormat]) x

private theorem highamCh4KahanFiniteFamily_round_neg_twoP_add_26 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteRoundToEven
        (-(2 * highamCh4KahanFiniteFamilyP k + 26)) =
      -(2 * highamCh4KahanFiniteFamilyP k + 24) := by
  simpa [highamCh4KahanFiniteFamily_round_twoP_add_26] using
    highamCh4KahanFiniteFamily_round_neg k
      (2 * highamCh4KahanFiniteFamilyP k + 26)

private theorem highamCh4KahanFiniteFamily_round_neg_eightP_sub_4 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteRoundToEven
        (-(8 * highamCh4KahanFiniteFamilyP k - 4)) =
      -(8 * highamCh4KahanFiniteFamilyP k) := by
  simpa [highamCh4KahanFiniteFamily_round_eightP_sub_4] using
    highamCh4KahanFiniteFamily_round_neg k
      (8 * highamCh4KahanFiniteFamilyP k - 4)

private theorem highamCh4KahanFiniteFamily_round_neg_tenP_add_24 (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).finiteRoundToEven
        (-(10 * highamCh4KahanFiniteFamilyP k + 24)) =
      -(10 * highamCh4KahanFiniteFamilyP k + 32) := by
  simpa [highamCh4KahanFiniteFamily_round_tenP_add_24] using
    highamCh4KahanFiniteFamily_round_neg k
      (10 * highamCh4KahanFiniteFamilyP k + 24)

/-- Every operation in the four-input returned-Kahan trace is realized by the
`k`th finite binary round-to-nearest-even format. -/
theorem highamCh4KahanFiniteFamily_rounding (k : Nat) :
    HighamCh4KahanReturnedCounterexampleRounding
      (highamCh4KahanFiniteFamilyFormat k)
      (highamCh4KahanFiniteFamilyP k) := by
  let p := highamCh4KahanFiniteFamilyP k
  let fmt := highamCh4KahanFiniteFamilyFormat k
  refine
    { y1 := ?_, s1 := ?_, q1 := ?_, e1 := ?_,
      y2 := ?_, s2 := ?_, q2 := ?_, e2 := ?_,
      y3 := ?_, s3 := ?_, q3 := ?_, e3 := ?_,
      y4 := ?_, s4 := ?_, q4 := ?_, e4 := ?_ }
  · apply highamCh4KahanFiniteFamily_finiteRoundToEvenOp_eq k
    · norm_num [BasicOp.exact, highamCh4KahanReturnedCounterexampleX1]
    · exact highamCh4KahanFiniteFamily_finiteSystem_neg22 k
  · apply highamCh4KahanFiniteFamily_finiteRoundToEvenOp_eq k
    · norm_num [BasicOp.exact, highamCh4KahanReturnedCounterexampleX1]
    · exact highamCh4KahanFiniteFamily_finiteSystem_neg22 k
  · apply highamCh4KahanFiniteFamily_finiteRoundToEvenOp_eq k
    · norm_num [BasicOp.exact, highamCh4KahanReturnedCounterexampleX1]
    · exact highamCh4KahanFiniteFamily_finiteSystem_22 k
  · apply highamCh4KahanFiniteFamily_finiteRoundToEvenOp_eq k
    · norm_num [BasicOp.exact, highamCh4KahanReturnedCounterexampleX1]
    · exact highamCh4KahanFiniteFamily_finiteSystem_zero k
  · apply highamCh4KahanFiniteFamily_finiteRoundToEvenOp_eq k
    · simp [BasicOp.exact, highamCh4KahanReturnedCounterexampleX2]
    · simpa [highamCh4KahanReturnedCounterexampleX2] using
        highamCh4KahanFiniteFamily_finiteSystem_neg_twoP_add_4 k
  · change fmt.finiteRoundToEven
      (BasicOp.exact BasicOp.add
        highamCh4KahanReturnedCounterexampleX1
        (highamCh4KahanReturnedCounterexampleX2 p)) =
      highamCh4KahanReturnedCounterexampleS2 p
    simp only [fmt, p, BasicOp.exact,
      highamCh4KahanReturnedCounterexampleX1,
      highamCh4KahanReturnedCounterexampleX2,
      highamCh4KahanReturnedCounterexampleS2]
    convert highamCh4KahanFiniteFamily_round_neg_twoP_add_26 k using 1 <;>
      ring_nf <;> simp [Nat.rawCast] <;> rfl
  · change fmt.finiteRoundToEven
      (BasicOp.exact BasicOp.sub
        highamCh4KahanReturnedCounterexampleX1
        (highamCh4KahanReturnedCounterexampleS2 p)) = 2 * p
    simp only [fmt, p, BasicOp.exact,
      highamCh4KahanReturnedCounterexampleX1,
      highamCh4KahanReturnedCounterexampleS2]
    convert highamCh4KahanFiniteFamily_round_twoP_add_2 k using 1 <;>
      ring_nf <;> simp [Nat.rawCast] <;> rfl
  · apply highamCh4KahanFiniteFamily_finiteRoundToEvenOp_eq k
    · simp [BasicOp.exact, p,
        highamCh4KahanReturnedCounterexampleX2]
    · exact highamCh4KahanFiniteFamily_finiteSystem_neg4 k
  · change fmt.finiteRoundToEven
      (BasicOp.exact BasicOp.add
        (highamCh4KahanReturnedCounterexampleX3 p) (-4)) =
      highamCh4KahanReturnedCounterexampleY3 p
    simp only [fmt, p, BasicOp.exact,
      highamCh4KahanReturnedCounterexampleX3,
      highamCh4KahanReturnedCounterexampleY3]
    convert highamCh4KahanFiniteFamily_round_neg_eightP_sub_4 k using 1 <;>
      ring_nf <;> simp [Nat.rawCast] <;> rfl
  · change fmt.finiteRoundToEven
      (BasicOp.exact BasicOp.add
        (highamCh4KahanReturnedCounterexampleS2 p)
        (highamCh4KahanReturnedCounterexampleY3 p)) =
      highamCh4KahanReturnedCounterexampleS3 p
    simp only [fmt, p, BasicOp.exact,
      highamCh4KahanReturnedCounterexampleS2,
      highamCh4KahanReturnedCounterexampleY3,
      highamCh4KahanReturnedCounterexampleS3]
    convert highamCh4KahanFiniteFamily_round_neg_tenP_add_24 k using 1 <;>
      ring_nf <;> simp [Nat.rawCast] <;> rfl
  · change fmt.finiteRoundToEven
      (BasicOp.exact BasicOp.sub
        (highamCh4KahanReturnedCounterexampleS2 p)
        (highamCh4KahanReturnedCounterexampleS3 p)) = 8 * p
    simp only [fmt, p, BasicOp.exact,
      highamCh4KahanReturnedCounterexampleS2,
      highamCh4KahanReturnedCounterexampleS3]
    convert highamCh4KahanFiniteFamily_round_eightP_add_8 k using 1 <;>
      ring_nf <;> simp [Nat.rawCast] <;> rfl
  · apply highamCh4KahanFiniteFamily_finiteRoundToEvenOp_eq k
    · simp [BasicOp.exact, p,
        highamCh4KahanReturnedCounterexampleY3]
    · exact highamCh4KahanFiniteFamily_finiteSystem_zero k
  · apply highamCh4KahanFiniteFamily_finiteRoundToEvenOp_eq k
    · norm_num [BasicOp.exact, highamCh4KahanReturnedCounterexampleX4]
    · exact highamCh4KahanFiniteFamily_finiteSystem_8 k
  · change fmt.finiteRoundToEven
      (BasicOp.exact BasicOp.add
        (highamCh4KahanReturnedCounterexampleS3 p)
        highamCh4KahanReturnedCounterexampleX4) =
      highamCh4KahanReturnedCounterexampleS3 p
    simp only [fmt, p, BasicOp.exact,
      highamCh4KahanReturnedCounterexampleS3,
      highamCh4KahanReturnedCounterexampleX4]
    convert highamCh4KahanFiniteFamily_round_neg_tenP_add_24 k using 1 <;>
      ring_nf <;> simp [Nat.rawCast] <;> rfl
  · apply highamCh4KahanFiniteFamily_finiteRoundToEvenOp_eq k
    · simp [BasicOp.exact]
    · exact highamCh4KahanFiniteFamily_finiteSystem_zero k
  · apply highamCh4KahanFiniteFamily_finiteRoundToEvenOp_eq k
    · norm_num [BasicOp.exact, highamCh4KahanReturnedCounterexampleX4]
    · exact highamCh4KahanFiniteFamily_finiteSystem_8 k

/-- In the `k`th family member, Higham's unit roundoff is exactly `1/p`. -/
theorem highamCh4KahanFiniteFamily_unitRoundoff (k : Nat) :
    (highamCh4KahanFiniteFamilyFormat k).unitRoundoff =
      1 / highamCh4KahanFiniteFamilyP k := by
  have hexp : (1 : Int) - ((k + 5 : Nat) : Int) =
      -((k + 4 : Nat) : Int) := by omega
  rw [FloatingPointFormat.unitRoundoff,
    FloatingPointFormat.machineEpsilon]
  simp only [highamCh4KahanFiniteFamilyFormat,
    FloatingPointFormat.betaR, hexp, zpow_neg, zpow_natCast]
  rw [highamCh4KahanFiniteFamilyP_eq, pow_add]
  norm_num [Nat.cast_pow]
  field_simp
  ring

private theorem highamCh4KahanFiniteFamily_budget_lt_for_large_p
    (C p : Real) (hp : 100 * (|C| + 1) < p) :
    2 * (1 / p) + C * (1 / p) ^ 2 < 22 / (10 * p + 26) := by
  have ha : 0 <= |C| := abs_nonneg C
  have hCle : C <= |C| := le_abs_self C
  have hp0 : 0 < p := by nlinarith
  have hp1 : 1 < p := by nlinarith
  have hden : 0 < 10 * p + 26 := by nlinarith
  have hpSq : 0 < p ^ 2 := sq_pos_of_pos hp0
  have hCp : C * p <= |C| * p :=
    mul_le_mul_of_nonneg_right hCle (le_of_lt hp0)
  have hmajorOne :
      (52 + 10 * C) * p + 26 * C <=
        52 * p + 10 * |C| * p + 26 * |C| := by
    nlinarith
  have hap : 0 <= |C| * p := mul_nonneg ha (le_of_lt hp0)
  have hmajorTwo :
      52 * p + 10 * |C| * p + 26 * |C| <
        100 * (|C| + 1) * p := by
    nlinarith
  have hlargeSq : 100 * (|C| + 1) * p < p * p :=
    mul_lt_mul_of_pos_right hp hp0
  have hlinear : (52 + 10 * C) * p + 26 * C < p ^ 2 := by
    calc
      (52 + 10 * C) * p + 26 * C <=
          52 * p + 10 * |C| * p + 26 * |C| := hmajorOne
      _ < 100 * (|C| + 1) * p := hmajorTwo
      _ < p * p := hlargeSq
      _ = p ^ 2 := by ring
  have hcross : (2 * p + C) * (10 * p + 26) < 22 * p ^ 2 := by
    nlinarith
  have hbudget :
      2 * (1 / p) + C * (1 / p) ^ 2 = (2 * p + C) / p ^ 2 := by
    field_simp
  rw [hbudget]
  exact (div_lt_div_iff₀ hpSq hden).2 hcross

private theorem highamCh4KahanFiniteFamily_exists_large_p (C : Real) :
    Exists fun k : Nat =>
      100 * (|C| + 1) < highamCh4KahanFiniteFamilyP k := by
  obtain ⟨k, hk⟩ :=
    pow_unbounded_of_one_lt (100 * (|C| + 1))
      (by norm_num : (1 : Real) < 2)
  refine Exists.intro k ?_
  rw [highamCh4KahanFiniteFamilyP_eq]
  norm_num [Nat.cast_pow]
  have hpow : 0 < (2 : Real) ^ k := pow_pos (by norm_num) k
  nlinarith

/-- Finite-arithmetic discrepancy for Higham (4.8): no precision-independent
second-order coefficient `C` can repair the printed leading-`2u`
componentwise source bound for the ordinary returned Kahan sum. -/
theorem highamCh4_equation48_finiteFamily_no_fixed_secondOrderConstant
    (C : Real) :
    Exists fun k : Nat =>
      Not (Exists fun
        mu : HighamCh4KahanReturnedCounterexampleWeight =>
          highamCh4KahanReturnedCounterexampleSourceRepresentation
            (highamCh4KahanFiniteFamilyFormat k)
            (highamCh4KahanFiniteFamilyP k)
            (2 * (highamCh4KahanFiniteFamilyFormat k).unitRoundoff +
              C * (highamCh4KahanFiniteFamilyFormat k).unitRoundoff ^ 2)
            mu) := by
  obtain ⟨k, hk⟩ := highamCh4KahanFiniteFamily_exists_large_p C
  refine Exists.intro k ?_
  apply highamCh4KahanReturnedCounterexample_no_source_bound_of_lt
    (highamCh4KahanFiniteFamilyFormat k)
    (by nlinarith [highamCh4KahanFiniteFamilyP_ge_32 k])
    (highamCh4KahanFiniteFamily_rounding k)
  rw [highamCh4KahanFiniteFamily_unitRoundoff]
  exact highamCh4KahanFiniteFamily_budget_lt_for_large_p
    C (highamCh4KahanFiniteFamilyP k) hk

/-- Finite-arithmetic discrepancy for Higham (4.9): the same family violates
the absolute forward bound with leading term `2u` and every fixed
second-order coefficient `C`. -/
theorem highamCh4_equation49_finiteFamily_no_fixed_secondOrderConstant
    (C : Real) :
    Exists fun k : Nat =>
      (2 * (highamCh4KahanFiniteFamilyFormat k).unitRoundoff +
          C * (highamCh4KahanFiniteFamilyFormat k).unitRoundoff ^ 2) *
          Finset.univ.sum (fun i : Fin 4 =>
            |highamCh4KahanReturnedCounterexampleInput
              (highamCh4KahanFiniteFamilyP k) i|) <
        |finiteKahanSum (highamCh4KahanFiniteFamilyFormat k) 4
            (highamCh4KahanReturnedCounterexampleInput
              (highamCh4KahanFiniteFamilyP k)) -
          Finset.univ.sum (fun i : Fin 4 =>
            highamCh4KahanReturnedCounterexampleInput
              (highamCh4KahanFiniteFamilyP k) i)| := by
  obtain ⟨k, hk⟩ := highamCh4KahanFiniteFamily_exists_large_p C
  refine Exists.intro k ?_
  let p := highamCh4KahanFiniteFamilyP k
  let fmt := highamCh4KahanFiniteFamilyFormat k
  have hp : 1 <= p := by
    dsimp [p]
    nlinarith [highamCh4KahanFiniteFamilyP_ge_32 k]
  have hbudget := highamCh4KahanFiniteFamily_budget_lt_for_large_p C p hk
  have hden : 0 < 10 * p + 26 := by nlinarith
  have hproduct :
      (2 * (1 / p) + C * (1 / p) ^ 2) * (10 * p + 26) < 22 :=
    (lt_div_iff₀ hden).1 hbudget
  have hreturned :=
    highamCh4KahanReturnedCounterexampleSum_eq_of_rounding fmt
      (highamCh4KahanFiniteFamily_rounding k)
  have hexact := highamCh4KahanReturnedCounterexample_exactSum p
  have habs := highamCh4KahanReturnedCounterexample_absSum p hp
  rw [highamCh4KahanFiniteFamily_unitRoundoff]
  change
    (2 * (1 / p) + C * (1 / p) ^ 2) *
        Finset.univ.sum (fun i : Fin 4 =>
          |highamCh4KahanReturnedCounterexampleInput p i|) <
      |finiteKahanSum fmt 4
          (highamCh4KahanReturnedCounterexampleInput p) -
        Finset.univ.sum (fun i : Fin 4 =>
          highamCh4KahanReturnedCounterexampleInput p i)|
  rw [hreturned, hexact, habs]
  have herr :
      |highamCh4KahanReturnedCounterexampleS3 p - (-(10 * p + 10))| =
        22 := by
    simp [highamCh4KahanReturnedCounterexampleS3]
    ring_nf
  rw [herr]
  exact hproduct

end NumStability
