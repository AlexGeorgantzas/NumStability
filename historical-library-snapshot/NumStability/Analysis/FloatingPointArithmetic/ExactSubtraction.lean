import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.IeeeOperations
import NumStability.Analysis.FloatingPointArithmetic.IeeeValue
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.FloatingPointArithmetic.RoundToEvenLocalError
import NumStability.Analysis.FloatingPointArithmetic.Rounding

namespace NumStability

/-!
# Exact subtraction

Reusable exact-subtraction predicates and proofs for finite floating-point
formats. The Higham Chapter 2 source entry point imports this module.
-/

noncomputable section

namespace FloatingPointFormat

/-- Higham Theorem 2.4's exponent side condition for Ferguson exact
subtraction, expressed with explicit normalized exponent representations for
`x`, `y`, and `x-y`.  The representation of `x-y` also records the
"does not underflow or overflow" side condition at the finite-format level. -/
def fergusonExponentCondition
    (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  ∃ ex ey ez : ℤ,
    fmt.normalizedExponentRepresentation x ex ∧
    fmt.normalizedExponentRepresentation y ey ∧
    fmt.normalizedExponentRepresentation (x - y) ez ∧
    ez < min ex ey
/-- Source-shaped inclusive version of Higham Theorem 2.4's exponent side
condition, matching the printed `e(x-y) <= min(e(x), e(y))`.  The older strict
predicate above is kept for the digit-branch Ferguson proof, where the
stronger hypothesis is used to expose the dropped leading guard digit. -/
def fergusonExponentConditionLe
    (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  ∃ ex ey ez : ℤ,
    fmt.normalizedExponentRepresentation x ex ∧
    fmt.normalizedExponentRepresentation y ey ∧
    fmt.normalizedExponentRepresentation (x - y) ez ∧
    ez ≤ min ex ey
/-- Magnitude/exponent form of Higham Theorem 2.4's printed condition.

For a nonunderflowing nonzero result, `e(x-y) ≤ min(e(x),e(y))` is
equivalent to the strict magnitude bound
`|x-y| < beta ^ min(e(x),e(y))`.  Unlike `fergusonExponentConditionLe`, this
predicate carries normalized exponent representations only for the two source
operands: it does not assume that `x-y` is representable. -/
def fergusonMagnitudeExponentConditionLe
    (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  ∃ ex ey : ℤ,
    fmt.normalizedExponentRepresentation x ex ∧
    fmt.normalizedExponentRepresentation y ey ∧
    |x - y| < fmt.betaR ^ min ex ey
theorem fergusonMagnitudeExponentConditionLe_left_normalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonMagnitudeExponentConditionLe x y) :
    fmt.normalizedSystem x := by
  rcases h with ⟨_ex, _ey, hx, _hy, _hmag⟩
  exact fmt.normalizedExponentRepresentation_normalizedSystem hx
theorem fergusonMagnitudeExponentConditionLe_right_normalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonMagnitudeExponentConditionLe x y) :
    fmt.normalizedSystem y := by
  rcases h with ⟨_ex, _ey, _hx, hy, _hmag⟩
  exact fmt.normalizedExponentRepresentation_normalizedSystem hy
theorem fergusonExponentCondition_left_normalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentCondition x y) :
    fmt.normalizedSystem x := by
  rcases h with ⟨_ex, _ey, _ez, hx, _hy, _hz, _hcond⟩
  exact fmt.normalizedExponentRepresentation_normalizedSystem hx
theorem fergusonExponentCondition_right_normalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentCondition x y) :
    fmt.normalizedSystem y := by
  rcases h with ⟨_ex, _ey, _ez, _hx, hy, _hz, _hcond⟩
  exact fmt.normalizedExponentRepresentation_normalizedSystem hy
theorem fergusonExponentCondition_sub_normalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentCondition x y) :
    fmt.normalizedSystem (x - y) := by
  rcases h with ⟨_ex, _ey, _ez, _hx, _hy, hz, _hcond⟩
  exact fmt.normalizedExponentRepresentation_normalizedSystem hz
theorem fergusonExponentConditionLe_left_normalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentConditionLe x y) :
    fmt.normalizedSystem x := by
  rcases h with ⟨_ex, _ey, _ez, hx, _hy, _hz, _hcond⟩
  exact fmt.normalizedExponentRepresentation_normalizedSystem hx
theorem fergusonExponentConditionLe_right_normalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentConditionLe x y) :
    fmt.normalizedSystem y := by
  rcases h with ⟨_ex, _ey, _ez, _hx, hy, _hz, _hcond⟩
  exact fmt.normalizedExponentRepresentation_normalizedSystem hy
theorem fergusonExponentConditionLe_sub_normalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentConditionLe x y) :
    fmt.normalizedSystem (x - y) := by
  rcases h with ⟨_ex, _ey, _ez, _hx, _hy, hz, _hcond⟩
  exact fmt.normalizedExponentRepresentation_normalizedSystem hz
/-- Guard-digit exact-subtraction model for Higham Theorem 2.4.  This is an
interface, not yet a constructive digit algorithm: any subtraction routine
satisfying it computes `x-y` exactly under the Ferguson exponent condition. -/
def guardDigitSubtractionModel
    (fmt : FloatingPointFormat) (flSub : ℝ → ℝ → ℝ) : Prop :=
  ∀ {x y : ℝ}, fmt.fergusonExponentCondition x y → flSub x y = x - y
theorem guardDigitSubtractionModel_exact_of_fergusonCondition
    {fmt : FloatingPointFormat} {flSub : ℝ → ℝ → ℝ} {x y : ℝ}
    (hmodel : fmt.guardDigitSubtractionModel flSub)
    (hcond : fmt.fergusonExponentCondition x y) :
    flSub x y = x - y :=
  hmodel hcond
/-- Higham Theorem 2.5's Sterbenz ratio condition. -/
def sterbenzRatioCondition (_fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  y / 2 < x ∧ x < 2 * y
/-- Source-shaped inclusive version of Higham Theorem 2.5's Sterbenz ratio
condition, matching the printed `y/2 <= x <= 2*y`. -/
def sterbenzRatioConditionLe (_fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  y / 2 ≤ x ∧ x ≤ 2 * y
theorem sterbenzRatioCondition_y_pos
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sterbenzRatioCondition x y) :
    0 < y := by
  rcases h with ⟨hlo, hhi⟩
  linarith
theorem sterbenzRatioCondition_x_pos
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sterbenzRatioCondition x y) :
    0 < x := by
  rcases h with ⟨hlo, hhi⟩
  have hy : 0 < y := by
    linarith
  linarith
theorem sterbenzRatioCondition_symm
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sterbenzRatioCondition x y) :
    fmt.sterbenzRatioCondition y x := by
  rcases h with ⟨hlo, hhi⟩
  constructor <;> linarith
theorem sterbenzRatioCondition_abs_sub_lt_left
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sterbenzRatioCondition x y) :
    |x - y| < x := by
  rcases h with ⟨hlo, hhi⟩
  have hy : 0 < y := by
    linarith
  exact abs_lt.mpr ⟨by linarith, by linarith⟩
theorem sterbenzRatioCondition_abs_sub_lt_right
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sterbenzRatioCondition x y) :
    |x - y| < y := by
  rcases h with ⟨hlo, hhi⟩
  have hx : 0 < x := by
    linarith
  exact abs_lt.mpr ⟨by linarith, by linarith⟩
theorem sterbenzRatioCondition_abs_sub_lt_min
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sterbenzRatioCondition x y) :
    |x - y| < min x y :=
  lt_min (fmt.sterbenzRatioCondition_abs_sub_lt_left h)
    (fmt.sterbenzRatioCondition_abs_sub_lt_right h)
/-- A one-digit decimal format used to keep the Sterbenz/Ferguson bridge honest:
Sterbenz's ratio hypothesis is not, in general bases, the same thing as
Ferguson's cancellation exponent hypothesis. -/
def decimalSingleDigitFormat : FloatingPointFormat where
  beta := 10
  t := 1
  emin := 1
  emax := 1
  beta_ge_two := by norm_num
  t_pos := by norm_num
  emin_le_emax := by norm_num
theorem decimalSingleDigitFormat_normalizedExponentRepresentation_four :
    decimalSingleDigitFormat.normalizedExponentRepresentation (4 : ℝ) 1 := by
  refine ⟨false, 4, ?_, ?_, ?_⟩
  · norm_num [decimalSingleDigitFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [decimalSingleDigitFormat, exponentInRange]
  · norm_num [decimalSingleDigitFormat, normalizedValue, signValue, betaR]
theorem decimalSingleDigitFormat_normalizedExponentRepresentation_five :
    decimalSingleDigitFormat.normalizedExponentRepresentation (5 : ℝ) 1 := by
  refine ⟨false, 5, ?_, ?_, ?_⟩
  · norm_num [decimalSingleDigitFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [decimalSingleDigitFormat, exponentInRange]
  · norm_num [decimalSingleDigitFormat, normalizedValue, signValue, betaR]
theorem decimalSingleDigitFormat_normalizedExponentRepresentation_nine :
    decimalSingleDigitFormat.normalizedExponentRepresentation (9 : ℝ) 1 := by
  refine ⟨false, 9, ?_, ?_, ?_⟩
  · norm_num [decimalSingleDigitFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [decimalSingleDigitFormat, exponentInRange]
  · norm_num [decimalSingleDigitFormat, normalizedValue, signValue, betaR]
theorem decimalSingleDigitFormat_sterbenzRatioCondition_nine_five :
    decimalSingleDigitFormat.sterbenzRatioCondition (9 : ℝ) 5 := by
  norm_num [sterbenzRatioCondition]
theorem decimalSingleDigitFormat_not_fergusonExponentCondition_nine_five :
    ¬ decimalSingleDigitFormat.fergusonExponentCondition (9 : ℝ) 5 := by
  intro h
  rcases h with ⟨ex, ey, ez, hx, hy, hz, hcond⟩
  rcases hx with ⟨_negX, _mx, _hmx, hex, _hx⟩
  rcases hy with ⟨_negY, _my, _hmy, hey, _hy⟩
  rcases hz with ⟨_negZ, _mz, _hmz, hez, _hz⟩
  norm_num [decimalSingleDigitFormat, exponentInRange] at hex hey hez
  omega
theorem decimalSingleDigitFormat_sterbenzRatio_not_ferguson :
    decimalSingleDigitFormat.sterbenzRatioCondition (9 : ℝ) 5 ∧
      decimalSingleDigitFormat.normalizedSystem (9 : ℝ) ∧
      decimalSingleDigitFormat.normalizedSystem (5 : ℝ) ∧
      decimalSingleDigitFormat.normalizedSystem ((9 : ℝ) - 5) ∧
      ¬ decimalSingleDigitFormat.fergusonExponentCondition (9 : ℝ) 5 := by
  refine ⟨decimalSingleDigitFormat_sterbenzRatioCondition_nine_five, ?_, ?_, ?_, ?_⟩
  · exact decimalSingleDigitFormat.normalizedExponentRepresentation_normalizedSystem
      decimalSingleDigitFormat_normalizedExponentRepresentation_nine
  · exact decimalSingleDigitFormat.normalizedExponentRepresentation_normalizedSystem
      decimalSingleDigitFormat_normalizedExponentRepresentation_five
  · norm_num
    exact decimalSingleDigitFormat.normalizedExponentRepresentation_normalizedSystem
      decimalSingleDigitFormat_normalizedExponentRepresentation_four
  · exact decimalSingleDigitFormat_not_fergusonExponentCondition_nine_five
/-- Current bridge surface for Sterbenz: the ratio condition plus an explicit
Ferguson exponent condition.  The decimal counterexample above shows that
Sterbenz cannot be closed by proving the ratio condition implies Ferguson's
exponent condition in general bases; the remaining finite-format theorem work is
a direct Sterbenz representability/exact-subtraction proof. -/
def sterbenzFergusonBridgeCondition
    (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  fmt.sterbenzRatioCondition x y ∧ fmt.fergusonExponentCondition x y
theorem sterbenzFergusonBridgeCondition_ratio
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sterbenzFergusonBridgeCondition x y) :
    fmt.sterbenzRatioCondition x y :=
  h.1
theorem sterbenzFergusonBridgeCondition_ferguson
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sterbenzFergusonBridgeCondition x y) :
    fmt.fergusonExponentCondition x y :=
  h.2
theorem guardDigitSubtractionModel_exact_of_sterbenzBridge
    {fmt : FloatingPointFormat} {flSub : ℝ → ℝ → ℝ} {x y : ℝ}
    (hmodel : fmt.guardDigitSubtractionModel flSub)
    (hbridge : fmt.sterbenzFergusonBridgeCondition x y) :
    flSub x y = x - y :=
  hmodel hbridge.2
/-- The older representation-form inclusive Ferguson condition implies the
new magnitude/exponent condition.  This bridge is one-way because the latter
deliberately does not assume a representation of the subtraction result. -/
theorem fergusonExponentConditionLe_fergusonMagnitudeExponentConditionLe
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentConditionLe x y) :
    fmt.fergusonMagnitudeExponentConditionLe x y := by
  rcases h with ⟨ex, ey, ez, hx, hy, hz, hle⟩
  refine ⟨ex, ey, hx, hy, ?_⟩
  exact lt_of_lt_of_le
    (fmt.normalizedExponentRepresentation_abs_lt_beta_pow hz)
    (fmt.betaR_zpow_le_zpow_of_le hle)
theorem fergusonExponentCondition_sub_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentCondition x y) :
    ¬ fmt.finiteUnderflowRange (x - y) :=
  fmt.normalizedSystem_not_finiteUnderflowRange
    (fmt.fergusonExponentCondition_sub_normalized h)
theorem fergusonExponentCondition_sub_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentCondition x y) :
    ¬ fmt.finiteOverflowRange (x - y) :=
  fmt.normalizedSystem_not_finiteOverflowRange
    (fmt.fergusonExponentCondition_sub_normalized h)
theorem normalizedValue_sub_fergusonCondition_sign_eq
    {fmt : FloatingPointFormat} {negativeX negativeY : Bool}
    {mx my : ℕ} {ex ey ez : ℤ}
    (hmx : fmt.normalizedMantissa mx)
    (hmy : fmt.normalizedMantissa my)
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negativeX mx ex -
        fmt.normalizedValue negativeY my ey) ez)
    (hcond : ez < min ex ey) :
    negativeX = negativeY := by
  let z :=
    fmt.normalizedValue negativeX mx ex -
      fmt.normalizedValue negativeY my ey
  have hz_upper : |z| < fmt.betaR ^ ez := by
    simpa [z] using fmt.normalizedExponentRepresentation_abs_lt_beta_pow hz
  have hlt_ex : ez < ex := lt_of_lt_of_le hcond (min_le_left ex ey)
  have hz_lt_ex_lower : |z| < fmt.betaR ^ (ex - 1) :=
    lt_of_lt_of_le hz_upper
      (fmt.betaR_zpow_le_zpow_of_le (by omega : ez ≤ ex - 1))
  cases negativeX <;> cases negativeY
  · rfl
  · exfalso
    have hxpos := fmt.normalizedValue_false_pos (m := mx) (e := ex) hmx
    have hyneg := fmt.normalizedValue_true_neg (m := my) (e := ey) hmy
    have hle : |fmt.normalizedValue false mx ex| ≤
        |fmt.normalizedValue false mx ex -
          fmt.normalizedValue true my ey| := by
      rw [abs_of_pos hxpos]
      have hdiff_nonneg :
          0 ≤ fmt.normalizedValue false mx ex -
            fmt.normalizedValue true my ey := by
        linarith
      rw [abs_of_nonneg hdiff_nonneg]
      linarith
    have hx_lower :
        fmt.betaR ^ (ex - 1) ≤ |fmt.normalizedValue false mx ex| :=
      fmt.normalizedValue_abs_lower_power hmx
    have hbig :
        fmt.betaR ^ (ex - 1) ≤
          |fmt.normalizedValue false mx ex -
            fmt.normalizedValue true my ey| :=
      le_trans hx_lower hle
    exact (not_lt_of_ge hbig) (by simpa [z] using hz_lt_ex_lower)
  · exfalso
    have hxneg := fmt.normalizedValue_true_neg (m := mx) (e := ex) hmx
    have hypos := fmt.normalizedValue_false_pos (m := my) (e := ey) hmy
    have hle : |fmt.normalizedValue true mx ex| ≤
        |fmt.normalizedValue true mx ex -
          fmt.normalizedValue false my ey| := by
      rw [abs_of_neg hxneg]
      have hdiff_nonpos :
          fmt.normalizedValue true mx ex -
            fmt.normalizedValue false my ey ≤ 0 := by
        linarith
      rw [abs_of_nonpos hdiff_nonpos]
      linarith
    have hx_lower :
        fmt.betaR ^ (ex - 1) ≤ |fmt.normalizedValue true mx ex| :=
      fmt.normalizedValue_abs_lower_power hmx
    have hbig :
        fmt.betaR ^ (ex - 1) ≤
          |fmt.normalizedValue true mx ex -
            fmt.normalizedValue false my ey| :=
      le_trans hx_lower hle
    exact (not_lt_of_ge hbig) (by simpa [z] using hz_lt_ex_lower)
  · rfl
theorem fergusonExponentCondition_exponent_gap_le_one
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentCondition x y) :
    ∃ ex ey : ℤ,
      fmt.normalizedExponentRepresentation x ex ∧
      fmt.normalizedExponentRepresentation y ey ∧
      ex ≤ ey + 1 ∧ ey ≤ ex + 1 := by
  rcases h with ⟨ex, ey, ez, hx, hy, hz, hcond⟩
  rcases fmt.normalizedExponentRepresentation_sub_exponent_gap_le_one
      hx hy hz hcond with ⟨hxy, hyx⟩
  exact ⟨ex, ey, hx, hy, hxy, hyx⟩
theorem fergusonExponentCondition_same_sign_and_exponent_gap
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentCondition x y) :
    ∃ negative mx my ex ey,
      fmt.normalizedMantissa mx ∧
      fmt.exponentInRange ex ∧
      x = fmt.normalizedValue negative mx ex ∧
      fmt.normalizedMantissa my ∧
      fmt.exponentInRange ey ∧
      y = fmt.normalizedValue negative my ey ∧
      ex ≤ ey + 1 ∧ ey ≤ ex + 1 := by
  rcases h with ⟨ex, ey, ez, hx, hy, hz, hcond⟩
  rcases hx with ⟨negativeX, mx, hmx, hex, hx_eq⟩
  rcases hy with ⟨negativeY, my, hmy, hey, hy_eq⟩
  subst x
  subst y
  have hsign : negativeX = negativeY :=
    fmt.normalizedValue_sub_fergusonCondition_sign_eq
      (negativeX := negativeX) (negativeY := negativeY)
      (mx := mx) (my := my) (ex := ex) (ey := ey) (ez := ez)
      hmx hmy hz hcond
  subst negativeY
  have hx_repr :
      fmt.normalizedExponentRepresentation
        (fmt.normalizedValue negativeX mx ex) ex :=
    ⟨negativeX, mx, hmx, hex, rfl⟩
  have hy_repr :
      fmt.normalizedExponentRepresentation
        (fmt.normalizedValue negativeX my ey) ey :=
    ⟨negativeX, my, hmy, hey, rfl⟩
  rcases fmt.normalizedExponentRepresentation_sub_exponent_gap_le_one
      hx_repr hy_repr hz hcond with ⟨hxy, hyx⟩
  exact ⟨negativeX, mx, my, ex, ey, hmx, hex, rfl, hmy, hey, rfl, hxy, hyx⟩
theorem fergusonExponentCondition_same_sign_exponent_cases
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentCondition x y) :
    ∃ negative mx my ex ey,
      fmt.normalizedMantissa mx ∧
      fmt.exponentInRange ex ∧
      x = fmt.normalizedValue negative mx ex ∧
      fmt.normalizedMantissa my ∧
      fmt.exponentInRange ey ∧
      y = fmt.normalizedValue negative my ey ∧
      (ex = ey ∨ ex = ey + 1 ∨ ey = ex + 1) := by
  rcases fmt.fergusonExponentCondition_same_sign_and_exponent_gap h with
    ⟨negative, mx, my, ex, ey, hmx, hex, hx, hmy, hey, hy, hxy, hyx⟩
  have hcases : ex = ey ∨ ex = ey + 1 ∨ ey = ex + 1 := by
    omega
  exact ⟨negative, mx, my, ex, ey, hmx, hex, hx, hmy, hey, hy, hcases⟩
/-- Raw aligned subtraction value when the first normalized mantissa has
exponent `e + 1`, the second has exponent `e`, and the signs agree.  The
factor `beta*mHigh - mLow` is the t+1 digit guard-aligned mantissa difference
from the Ferguson proof. -/
def guardAlignedMantissaDiff
    (fmt : FloatingPointFormat) (mHigh mLow : ℕ) : ℝ :=
  fmt.betaR * (mHigh : ℝ) - (mLow : ℝ)
/-- Integer form of the guard-aligned coefficient `beta*mHigh - mLow`.
This is the coefficient whose base-`beta` digits are formed before the final
t-digit rounding step in Ferguson's proof. -/
def guardAlignedMantissaDiffInt
    (fmt : FloatingPointFormat) (mHigh mLow : ℕ) : ℤ :=
  ((fmt.beta * mHigh : ℕ) : ℤ) - (mLow : ℤ)
theorem guardAlignedMantissaDiffInt_cast
    (fmt : FloatingPointFormat) (mHigh mLow : ℕ) :
    ((fmt.guardAlignedMantissaDiffInt mHigh mLow : ℤ) : ℝ) =
      fmt.guardAlignedMantissaDiff mHigh mLow := by
  simp [guardAlignedMantissaDiffInt, guardAlignedMantissaDiff, betaR]
def alignedAdjacentExponentSubtractionValue
    (fmt : FloatingPointFormat) (negative : Bool) (mHigh mLow : ℕ)
    (e : ℤ) : ℝ :=
  fmt.signValue negative *
    (fmt.guardAlignedMantissaDiff mHigh mLow *
      fmt.betaR ^ (e - (fmt.t : ℤ)))
theorem normalizedValue_sub_sameSign_adjacentExponent_eq_aligned
    (fmt : FloatingPointFormat) (negative : Bool) (mHigh mLow : ℕ)
    (e : ℤ) :
    fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e =
      fmt.alignedAdjacentExponentSubtractionValue negative mHigh mLow e := by
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  have hpow :
      fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) =
        fmt.betaR * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    calc
      fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) =
          fmt.betaR ^ ((e - (fmt.t : ℤ)) + 1) := by
        congr 1
        ring
      _ = fmt.betaR ^ (e - (fmt.t : ℤ)) * fmt.betaR ^ (1 : ℤ) := by
        rw [zpow_add₀ hbase]
      _ = fmt.betaR * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
        rw [zpow_one]
        ring
  cases negative <;>
    simp [alignedAdjacentExponentSubtractionValue, normalizedValue, signValue,
      guardAlignedMantissaDiff, hpow] <;>
    ring
theorem alignedAdjacentExponentSubtractionValue_abs
    (fmt : FloatingPointFormat) (negative : Bool) (mHigh mLow : ℕ)
    (e : ℤ) :
    |fmt.alignedAdjacentExponentSubtractionValue negative mHigh mLow e| =
      |fmt.guardAlignedMantissaDiff mHigh mLow| *
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  rw [alignedAdjacentExponentSubtractionValue, abs_mul, abs_mul,
    fmt.signValue_abs negative,
    abs_of_pos (fmt.betaR_zpow_pos (e - (fmt.t : ℤ)))]
  ring
theorem guardAlignedMantissaDiff_abs_lt_minNormalMantissa_of_fergusonAdjacent
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e) ez)
    (hcond : ez < e) :
    |fmt.guardAlignedMantissaDiff mHigh mLow| <
      (fmt.minNormalMantissa : ℝ) := by
  have hz_upper :
      |fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e| < fmt.betaR ^ ez :=
    fmt.normalizedExponentRepresentation_abs_lt_beta_pow hz
  have hz_lt_lower :
      |fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e| < fmt.betaR ^ (e - 1) :=
    lt_of_lt_of_le hz_upper
      (fmt.betaR_zpow_le_zpow_of_le (by omega : ez ≤ e - 1))
  have hvalue :=
    fmt.normalizedValue_sub_sameSign_adjacentExponent_eq_aligned
      negative mHigh mLow e
  have hscale_pos : 0 < fmt.betaR ^ (e - (fmt.t : ℤ)) :=
    fmt.betaR_zpow_pos (e - (fmt.t : ℤ))
  have hscaled :
      |fmt.guardAlignedMantissaDiff mHigh mLow| *
          fmt.betaR ^ (e - (fmt.t : ℤ)) <
        (fmt.minNormalMantissa : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    rw [← fmt.alignedAdjacentExponentSubtractionValue_abs negative mHigh mLow e]
    rw [← hvalue]
    simpa [fmt.minNormalMantissa_scale_eq e] using hz_lt_lower
  exact lt_of_mul_lt_mul_right hscaled (le_of_lt hscale_pos)
theorem guardAlignedMantissaDiffInt_abs_lt_minNormalMantissa_of_fergusonAdjacent
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e) ez)
    (hcond : ez < e) :
    |fmt.guardAlignedMantissaDiffInt mHigh mLow| <
      (fmt.minNormalMantissa : ℤ) := by
  have hreal :
      |((fmt.guardAlignedMantissaDiffInt mHigh mLow : ℤ) : ℝ)| <
        (fmt.minNormalMantissa : ℝ) := by
    simpa [fmt.guardAlignedMantissaDiffInt_cast mHigh mLow] using
      fmt.guardAlignedMantissaDiff_abs_lt_minNormalMantissa_of_fergusonAdjacent
        (negative := negative) (mHigh := mHigh) (mLow := mLow)
        (e := e) (ez := ez) hz hcond
  exact_mod_cast hreal
theorem guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e) ez)
    (hcond : ez < e) :
    (fmt.guardAlignedMantissaDiffInt mHigh mLow).natAbs <
      fmt.minNormalMantissa := by
  have hint :
      |fmt.guardAlignedMantissaDiffInt mHigh mLow| <
        (fmt.minNormalMantissa : ℤ) :=
    fmt.guardAlignedMantissaDiffInt_abs_lt_minNormalMantissa_of_fergusonAdjacent
      (negative := negative) (mHigh := mHigh) (mLow := mLow)
      (e := e) (ez := ez) hz hcond
  have hnatInt :
      (((fmt.guardAlignedMantissaDiffInt mHigh mLow).natAbs : ℕ) : ℤ) <
        (fmt.minNormalMantissa : ℤ) := by
    simpa using hint
  exact_mod_cast hnatInt
/-- In the positive adjacent-exponent Sterbenz branch, the guard-aligned
coefficient is positive: the higher-exponent normalized operand is already
larger than the lower-exponent one. -/
theorem guardAlignedMantissaDiffInt_pos_of_adjacentNormalizedMantissas
    {fmt : FloatingPointFormat} {mHigh mLow : ℕ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow) :
    0 < fmt.guardAlignedMantissaDiffInt mHigh mLow := by
  have hlow_lt_coeff : mLow < fmt.beta * mHigh := by
    calc
      mLow < fmt.beta ^ fmt.t := hmLow.2
      _ = fmt.minNormalMantissa * fmt.beta :=
          fmt.minNormalMantissa_mul_beta_eq_mantissaBound.symm
      _ = fmt.beta * fmt.minNormalMantissa := by rw [Nat.mul_comm]
      _ ≤ fmt.beta * mHigh := Nat.mul_le_mul_left fmt.beta hmHigh.1
  dsimp [guardAlignedMantissaDiffInt]
  omega
/-- Direct Sterbenz adjacent-branch coefficient bound.  If positive
same-sign operands have adjacent exponents and satisfy the Sterbenz ratio
condition, then the guard-aligned integer coefficient `beta*mHigh - mLow` has
at most `t` base-`beta` digits. -/
theorem guardAlignedMantissaDiffInt_natAbs_lt_mantissaBound_of_sterbenzAdjacent
    {fmt : FloatingPointFormat} {mHigh mLow : ℕ} {e : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (hsterbenz : fmt.sterbenzRatioCondition
      (fmt.normalizedValue false mHigh (e + 1))
      (fmt.normalizedValue false mLow e)) :
    (fmt.guardAlignedMantissaDiffInt mHigh mLow).natAbs <
      fmt.beta ^ fmt.t := by
  let s := fmt.betaR ^ (e - (fmt.t : ℤ))
  have hs_pos : 0 < s := fmt.betaR_zpow_pos (e - (fmt.t : ℤ))
  have hx_expr :
      fmt.normalizedValue false mHigh (e + 1) =
        ((fmt.beta : ℝ) * (mHigh : ℝ)) * s := by
    have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
    have hpow :
        fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) =
          fmt.betaR * s := by
      calc
        fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) =
            fmt.betaR ^ ((e - (fmt.t : ℤ)) + 1) := by
              congr 1
              ring
        _ = fmt.betaR ^ (e - (fmt.t : ℤ)) * fmt.betaR ^ (1 : ℤ) := by
              rw [zpow_add₀ hbase]
        _ = fmt.betaR * s := by
              rw [zpow_one]
              ring
    calc
      fmt.normalizedValue false mHigh (e + 1) =
          (mHigh : ℝ) *
            fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) := by
            simp [normalizedValue, signValue]
      _ = (mHigh : ℝ) * (fmt.betaR * s) := by rw [hpow]
      _ = ((fmt.beta : ℝ) * (mHigh : ℝ)) * s := by
            simp [betaR]
            ring
  have hy_expr :
      fmt.normalizedValue false mLow e = (mLow : ℝ) * s := by
    simp [normalizedValue, signValue, s]
  have hcoeff_real :
      (fmt.beta : ℝ) * (mHigh : ℝ) < 2 * (mLow : ℝ) := by
    have hxlt := hsterbenz.2
    rw [hx_expr, hy_expr] at hxlt
    have hxlt' :
        ((fmt.beta : ℝ) * (mHigh : ℝ)) * s <
          (2 * (mLow : ℝ)) * s := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hxlt
    exact lt_of_mul_lt_mul_right hxlt' (le_of_lt hs_pos)
  have hcoeff_nat : fmt.beta * mHigh < 2 * mLow := by
    exact_mod_cast hcoeff_real
  have hlow_lt_coeff : mLow < fmt.beta * mHigh := by
    calc
      mLow < fmt.beta ^ fmt.t := hmLow.2
      _ = fmt.minNormalMantissa * fmt.beta :=
          fmt.minNormalMantissa_mul_beta_eq_mantissaBound.symm
      _ = fmt.beta * fmt.minNormalMantissa := by rw [Nat.mul_comm]
      _ ≤ fmt.beta * mHigh := Nat.mul_le_mul_left fmt.beta hmHigh.1
  have hdiff_lt_low : fmt.beta * mHigh - mLow < mLow := by
    omega
  have hdiff_lt_bound :
      fmt.beta * mHigh - mLow < fmt.beta ^ fmt.t :=
    lt_trans hdiff_lt_low hmLow.2
  have hguard_eq :
      ((fmt.beta * mHigh - mLow : ℕ) : ℝ) =
        fmt.guardAlignedMantissaDiff mHigh mLow := by
    rw [Nat.cast_sub (le_of_lt hlow_lt_coeff)]
    simp [guardAlignedMantissaDiff, betaR, Nat.cast_mul]
  have hguard_pos :
      0 < fmt.guardAlignedMantissaDiff mHigh mLow := by
    rw [← hguard_eq]
    exact_mod_cast Nat.sub_pos_of_lt hlow_lt_coeff
  have hguard_lt_bound :
      fmt.guardAlignedMantissaDiff mHigh mLow <
        (fmt.beta ^ fmt.t : ℝ) := by
    rw [← hguard_eq]
    exact_mod_cast hdiff_lt_bound
  have hreal :
      |((fmt.guardAlignedMantissaDiffInt mHigh mLow : ℤ) : ℝ)| <
        (fmt.beta ^ fmt.t : ℝ) := by
    rw [fmt.guardAlignedMantissaDiffInt_cast mHigh mLow]
    rw [abs_of_pos hguard_pos]
    exact hguard_lt_bound
  have hint :
      |fmt.guardAlignedMantissaDiffInt mHigh mLow| <
        (fmt.beta ^ fmt.t : ℤ) := by
    exact_mod_cast hreal
  have hnatInt :
      (((fmt.guardAlignedMantissaDiffInt mHigh mLow).natAbs : ℕ) : ℤ) <
        (fmt.beta ^ fmt.t : ℤ) := by
    simpa using hint
  exact_mod_cast hnatInt
/-- The leading digit of the `t+1`-digit guard word associated to an integer
coefficient.  For the one-exponent-shift Ferguson branch this is the source
proof's `z₁` digit in `z₁.z₂...zₜzₜ₊₁`. -/
def guardDigitLeadingDigit (fmt : FloatingPointFormat) (k : ℤ) : ℕ :=
  k.natAbs / fmt.beta ^ fmt.t
/-- The trailing `t`-digit coefficient after removing the leading guard-word
digit.  When the leading digit is zero this is the original absolute
coefficient. -/
def guardDigitTailMantissa (fmt : FloatingPointFormat) (k : ℤ) : ℕ :=
  k.natAbs % fmt.beta ^ fmt.t
theorem guardDigitTailMantissa_eq_natAbs_of_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} {k : ℤ}
    (h : k.natAbs < fmt.beta ^ fmt.t) :
    fmt.guardDigitTailMantissa k = k.natAbs := by
  exact Nat.mod_eq_of_lt h
theorem guardDigitLeadingDigit_eq_zero_of_natAbs_lt_minNormalMantissa
    {fmt : FloatingPointFormat} {k : ℤ}
    (h : k.natAbs < fmt.minNormalMantissa) :
    fmt.guardDigitLeadingDigit k = 0 := by
  exact Nat.div_eq_of_lt
    (lt_trans h fmt.minNormalMantissa_lt_mantissaBound)
theorem guardDigitTailMantissa_eq_natAbs_of_natAbs_lt_minNormalMantissa
    {fmt : FloatingPointFormat} {k : ℤ}
    (h : k.natAbs < fmt.minNormalMantissa) :
    fmt.guardDigitTailMantissa k = k.natAbs := by
  exact fmt.guardDigitTailMantissa_eq_natAbs_of_natAbs_lt_mantissaBound
    (lt_trans h fmt.minNormalMantissa_lt_mantissaBound)
/-- The signed coefficient obtained by dropping the leading guard digit and
reattaching the original sign.  Under the Ferguson one-shift condition this is
the source proof's "round to t digits" coefficient. -/
def guardDigitRoundedCoeff (fmt : FloatingPointFormat) (k : ℤ) : ℤ :=
  if k < 0 then -((fmt.guardDigitTailMantissa k : ℕ) : ℤ)
  else ((fmt.guardDigitTailMantissa k : ℕ) : ℤ)
theorem guardDigitRoundedCoeff_eq_self_of_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} {k : ℤ}
    (h : k.natAbs < fmt.beta ^ fmt.t) :
    fmt.guardDigitRoundedCoeff k = k := by
  have htail := fmt.guardDigitTailMantissa_eq_natAbs_of_natAbs_lt_mantissaBound h
  unfold guardDigitRoundedCoeff
  by_cases hk : k < 0
  · rw [if_pos hk, htail, Int.natCast_natAbs, abs_of_neg hk]
    ring
  · have hk_nonneg : 0 ≤ k := le_of_not_gt hk
    rw [if_neg hk, htail, Int.natCast_natAbs, abs_of_nonneg hk_nonneg]
theorem guardDigitRoundedCoeff_eq_self_of_natAbs_lt_minNormalMantissa
    {fmt : FloatingPointFormat} {k : ℤ}
    (h : k.natAbs < fmt.minNormalMantissa) :
    fmt.guardDigitRoundedCoeff k = k :=
  fmt.guardDigitRoundedCoeff_eq_self_of_natAbs_lt_mantissaBound
    (lt_trans h fmt.minNormalMantissa_lt_mantissaBound)
/-- Same-exponent subtraction value after the t-digit subtraction coefficient
is kept exactly. -/
def guardDigitRoundedSameExponentSubtractionValue
    (fmt : FloatingPointFormat) (negative : Bool) (m n : ℕ)
    (e : ℤ) : ℝ :=
  fmt.signValue negative *
    (((fmt.guardDigitRoundedCoeff
      (fmt.sameExponentMantissaDiffInt m n) : ℤ) : ℝ) *
      fmt.betaR ^ (e - (fmt.t : ℤ)))
theorem normalizedValue_sub_sameSign_sameExponent_eq_guardDigitRounded
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ}
    {e : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n) :
    fmt.normalizedValue negative m e - fmt.normalizedValue negative n e =
      fmt.guardDigitRoundedSameExponentSubtractionValue negative m n e := by
  have hround :
      fmt.guardDigitRoundedCoeff (fmt.sameExponentMantissaDiffInt m n) =
        fmt.sameExponentMantissaDiffInt m n :=
    fmt.guardDigitRoundedCoeff_eq_self_of_natAbs_lt_mantissaBound
      (fmt.sameExponentMantissaDiffInt_natAbs_lt_mantissaBound hm.2 hn.2)
  have hcast :
      (((fmt.guardDigitRoundedCoeff
        (fmt.sameExponentMantissaDiffInt m n) : ℤ) : ℝ)) =
        (m : ℝ) - (n : ℝ) := by
    rw [hround]
    exact fmt.sameExponentMantissaDiffInt_cast m n
  rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
  simp [guardDigitRoundedSameExponentSubtractionValue,
    alignedSameExponentSubtractionValue, hcast]
  ring
/-- Higham Theorem 2.4's magnitude/exponent condition itself forces the exact
subtraction onto a finite radix lattice.  In particular, representability of
`x-y` is a conclusion rather than part of the hypothesis. -/
theorem fergusonMagnitudeExponentConditionLe_sub_finiteSystem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonMagnitudeExponentConditionLe x y) :
    fmt.finiteSystem (x - y) := by
  rcases h with ⟨ex, ey, hx, hy, hmag⟩
  rcases hx with ⟨negativeX, mx, _hmx, _hex, rfl⟩
  rcases hy with ⟨negativeY, my, _hmy, hey, rfl⟩
  by_cases hle : ey ≤ ex
  · have hmin : min ex ey = ey := min_eq_right hle
    apply fmt.normalizedValue_sub_orderedExponent_finiteSystem_of_abs_lt_beta_pow
      hey hle
    simpa [hmin] using hmag
  · have hex_le : ex ≤ ey := le_of_not_ge hle
    have hmin : min ex ey = ex := min_eq_left hex_le
    have hfin :
        fmt.finiteSystem
          (fmt.normalizedValue negativeY my ey -
            fmt.normalizedValue negativeX mx ex) := by
      apply fmt.normalizedValue_sub_orderedExponent_finiteSystem_of_abs_lt_beta_pow
        _hex hex_le
      simpa [hmin, abs_sub_comm] using hmag
    have hneg := fmt.finiteSystem_neg hfin
    convert hneg using 1
    ring
/-- The guard-aligned adjacent-exponent subtraction value is finite whenever
its exact signed integer coefficient has fewer than `t` radix digits. -/
theorem alignedAdjacentExponentSubtractionValue_finiteSystem_of_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hcoeff :
      (fmt.guardAlignedMantissaDiffInt mHigh mLow).natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      (fmt.alignedAdjacentExponentSubtractionValue negative mHigh mLow e) := by
  have h :=
    fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := negative)
      (k := fmt.guardAlignedMantissaDiffInt mHigh mLow)
      (e := e) he hcoeff
  convert h using 1
  rw [alignedAdjacentExponentSubtractionValue,
    fmt.guardAlignedMantissaDiffInt_cast mHigh mLow]
  ring
/-- Same-sign adjacent-exponent subtraction is finite when the guard-aligned
coefficient has fewer than `t` radix digits. -/
theorem normalizedValue_sub_sameSign_adjacentExponent_finiteSystem_of_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hcoeff :
      (fmt.guardAlignedMantissaDiffInt mHigh mLow).natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      (fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e) := by
  rw [fmt.normalizedValue_sub_sameSign_adjacentExponent_eq_aligned]
  exact
    fmt.alignedAdjacentExponentSubtractionValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := negative) (mHigh := mHigh) (mLow := mLow) (e := e)
      he hcoeff
/-- Positive adjacent-exponent Sterbenz branch: if the two normalized operands
satisfy the Sterbenz ratio condition, their exact subtraction is finite
representable. -/
theorem normalizedValue_sub_positive_adjacentExponent_finiteSystem_of_sterbenzAdjacent
    {fmt : FloatingPointFormat} {mHigh mLow : ℕ} {e : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (he : fmt.exponentInRange e)
    (hsterbenz : fmt.sterbenzRatioCondition
      (fmt.normalizedValue false mHigh (e + 1))
      (fmt.normalizedValue false mLow e)) :
    fmt.finiteSystem
      (fmt.normalizedValue false mHigh (e + 1) -
        fmt.normalizedValue false mLow e) := by
  exact
    fmt.normalizedValue_sub_sameSign_adjacentExponent_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := false) (mHigh := mHigh) (mLow := mLow) (e := e) he
      (fmt.guardAlignedMantissaDiffInt_natAbs_lt_mantissaBound_of_sterbenzAdjacent
        (mHigh := mHigh) (mLow := mLow) (e := e)
        hmHigh hmLow hsterbenz)
/-- Sterbenz's ratio condition forces two positive normalized operands to have
exponents that differ by at most one. -/
theorem sterbenzRatioCondition_positive_normalized_exponent_gap_le_one
    {fmt : FloatingPointFormat} {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hsterbenz : fmt.sterbenzRatioCondition
      (fmt.normalizedValue false m e)
      (fmt.normalizedValue false n e')) :
    e ≤ e' + 1 ∧ e' ≤ e + 1 := by
  constructor
  · by_contra hnot
    have hgap : e' + 1 < e := by omega
    have hx_lower :
        fmt.betaR ^ (e - 1) ≤ fmt.normalizedValue false m e :=
      by
        have hxpos := fmt.normalizedValue_false_pos (m := m) (e := e) hm
        simpa [abs_of_pos hxpos] using
          (fmt.normalizedValue_abs_lower_power
            (negative := false) (m := m) (e := e) hm)
    have hy_upper :
        fmt.normalizedValue false n e' < fmt.betaR ^ e' :=
      by
        have hypos := fmt.normalizedValue_false_pos (m := n) (e := e') hn
        simpa [abs_of_pos hypos] using
          (fmt.normalizedValue_abs_lt_beta_pow
            (negative := false) (m := n) (e := e') hn)
    have htwo_y_lt_x :
        2 * fmt.normalizedValue false n e' <
          fmt.normalizedValue false m e := by
      calc
        2 * fmt.normalizedValue false n e' <
            2 * fmt.betaR ^ e' :=
          mul_lt_mul_of_pos_left hy_upper (by norm_num)
        _ ≤ fmt.betaR ^ (e' + 1) :=
          fmt.betaR_zpow_add_one_le_of_two_mul e'
        _ ≤ fmt.betaR ^ (e - 1) :=
          fmt.betaR_zpow_le_zpow_of_le (by omega)
        _ ≤ fmt.normalizedValue false m e := hx_lower
    exact (not_lt_of_ge (le_of_lt htwo_y_lt_x)) hsterbenz.2
  · by_contra hnot
    have hgap : e + 1 < e' := by omega
    have hy_lower :
        fmt.betaR ^ (e' - 1) ≤ fmt.normalizedValue false n e' :=
      by
        have hypos := fmt.normalizedValue_false_pos (m := n) (e := e') hn
        simpa [abs_of_pos hypos] using
          (fmt.normalizedValue_abs_lower_power
            (negative := false) (m := n) (e := e') hn)
    have hx_upper :
        fmt.normalizedValue false m e < fmt.betaR ^ e :=
      by
        have hxpos := fmt.normalizedValue_false_pos (m := m) (e := e) hm
        simpa [abs_of_pos hxpos] using
          (fmt.normalizedValue_abs_lt_beta_pow
            (negative := false) (m := m) (e := e) hm)
    have htwo_x_lt_y :
        2 * fmt.normalizedValue false m e <
          fmt.normalizedValue false n e' := by
      calc
        2 * fmt.normalizedValue false m e <
            2 * fmt.betaR ^ e :=
          mul_lt_mul_of_pos_left hx_upper (by norm_num)
        _ ≤ fmt.betaR ^ (e + 1) :=
          fmt.betaR_zpow_add_one_le_of_two_mul e
        _ ≤ fmt.betaR ^ (e' - 1) :=
          fmt.betaR_zpow_le_zpow_of_le (by omega)
        _ ≤ fmt.normalizedValue false n e' := hy_lower
    have hy_lt_two_x :
        fmt.normalizedValue false n e' <
          2 * fmt.normalizedValue false m e := by
      rcases hsterbenz with ⟨hlo, _hhi⟩
      linarith
    exact (not_lt_of_ge (le_of_lt htwo_x_lt_y)) hy_lt_two_x
/-- Positive normalized Sterbenz finite-representability theorem.  For any two
positive normalized finite operands whose exponents are in range, the exact
subtraction is finite whenever Sterbenz's ratio condition holds. -/
theorem normalizedValue_sub_positive_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e) (he' : fmt.exponentInRange e')
    (hsterbenz : fmt.sterbenzRatioCondition
      (fmt.normalizedValue false m e)
      (fmt.normalizedValue false n e')) :
    fmt.finiteSystem
      (fmt.normalizedValue false m e -
        fmt.normalizedValue false n e') := by
  have hgap :=
    fmt.sterbenzRatioCondition_positive_normalized_exponent_gap_le_one
      (m := m) (n := n) (e := e) (e' := e') hm hn hsterbenz
  have hcases : e = e' ∨ e = e' + 1 ∨ e' = e + 1 := by
    omega
  rcases hcases with heq | hcases
  · subst e'
    exact
      fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedMantissas
        (negative := false) (m := m) (n := n) (e := e) hm hn he
  · rcases hcases with hsucc | hpred
    · subst e
      exact
        fmt.normalizedValue_sub_positive_adjacentExponent_finiteSystem_of_sterbenzAdjacent
          (mHigh := m) (mLow := n) (e := e') hm hn he' hsterbenz
    · subst e'
      have hsymm :
          fmt.sterbenzRatioCondition
            (fmt.normalizedValue false n (e + 1))
            (fmt.normalizedValue false m e) :=
        fmt.sterbenzRatioCondition_symm hsterbenz
      have hfin_yx :
          fmt.finiteSystem
            (fmt.normalizedValue false n (e + 1) -
              fmt.normalizedValue false m e) :=
        fmt.normalizedValue_sub_positive_adjacentExponent_finiteSystem_of_sterbenzAdjacent
          (mHigh := n) (mLow := m) (e := e) hn hm he hsymm
      have hneg := fmt.finiteSystem_neg hfin_yx
      convert hneg using 1
      ring
/-- Source-shaped normalized Sterbenz finite-representability theorem.  The
ratio condition forces normalized finite operands to be positive, so their sign
bits reduce to the positive-normalized theorem above. -/
theorem normalizedSystem_sub_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.normalizedSystem x)
    (hy : fmt.normalizedSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteSystem (x - y) := by
  rcases hx with ⟨negativeX, m, e, hm, he, rfl⟩
  rcases hy with ⟨negativeY, n, e', hn, he', rfl⟩
  cases negativeX
  · cases negativeY
    · exact
        fmt.normalizedValue_sub_positive_finiteSystem_of_sterbenzRatioCondition
          (m := m) (n := n) (e := e) (e' := e')
          hm hn he he' hsterbenz
    · have hypos := fmt.sterbenzRatioCondition_y_pos hsterbenz
      have hyneg := fmt.normalizedValue_true_neg (m := n) (e := e') hn
      linarith
  · have hxpos := fmt.sterbenzRatioCondition_x_pos hsterbenz
    have hxneg := fmt.normalizedValue_true_neg (m := m) (e := e) hm
    linarith
/-- Source-shaped subnormal Sterbenz finite-representability theorem.  The
ratio condition forces both subnormal finite operands to be positive, reducing
the proof to the same-sign subnormal lattice theorem. -/
theorem subnormalSystem_sub_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.subnormalSystem x)
    (hy : fmt.subnormalSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteSystem (x - y) := by
  rcases hx with ⟨negativeX, m, hm, rfl⟩
  rcases hy with ⟨negativeY, n, hn, rfl⟩
  cases negativeX
  · cases negativeY
    · exact
        fmt.subnormalValue_sub_sameSign_finiteSystem_of_subnormalMantissas
          (negative := false) (m := m) (n := n) hm hn
    · have hypos := fmt.sterbenzRatioCondition_y_pos hsterbenz
      have hyneg := fmt.subnormalValue_true_neg (m := n) hn
      linarith
  · have hxpos := fmt.sterbenzRatioCondition_x_pos hsterbenz
    have hxneg := fmt.subnormalValue_true_neg (m := m) hm
    linarith
/-- Positive mixed normal/subnormal Sterbenz finite-representability theorem.
The normalized operand is rewritten on the subnormal lattice with integer
coefficient `m * beta^(e - emin)`, and the Sterbenz upper ratio bounds that
coefficient below twice the subnormal mantissa. -/
theorem normalizedValue_sub_subnormalValue_positive_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hsterbenz : fmt.sterbenzRatioCondition
      (fmt.normalizedValue false m e)
      (fmt.subnormalValue false n)) :
    fmt.finiteSystem
      (fmt.normalizedValue false m e -
        fmt.subnormalValue false n) := by
  let q := Int.toNat (e - fmt.emin)
  let a := m * fmt.beta ^ q
  have _hm_range : fmt.mantissaInRange m := hm.2
  have hq_cast : ((q : ℕ) : ℤ) = e - fmt.emin := by
    have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr he.1
    simpa [q] using Int.toNat_of_nonneg hnonneg
  have hq_endpoint : e - (q : ℤ) = fmt.emin := by
    omega
  have hshift :
      fmt.normalizedValue false a fmt.emin =
        fmt.normalizedValue false m e := by
    have h :=
      fmt.normalizedValue_mul_beta_pow_subExponent_eq
        (negative := false) (m := m) (shift := q) (e := e)
    rw [hq_endpoint] at h
    simpa [a] using h
  let s := fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))
  have hs_pos : 0 < s := fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ))
  have hx_expr :
      fmt.normalizedValue false m e = (a : ℝ) * s := by
    rw [← hshift]
    simp [a, s, normalizedValue, signValue]
  have hy_expr :
      fmt.subnormalValue false n = (n : ℝ) * s := by
    simp [s, subnormalValue, signValue]
  have ha_lt_two_n_real : (a : ℝ) < 2 * (n : ℝ) := by
    have hxlt := hsterbenz.2
    rw [hx_expr, hy_expr] at hxlt
    have hxlt' :
        (a : ℝ) * s < (2 * (n : ℝ)) * s := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hxlt
    exact lt_of_mul_lt_mul_right hxlt' (le_of_lt hs_pos)
  have ha_lt_two_n : a < 2 * n := by
    exact_mod_cast ha_lt_two_n_real
  have ha_range : fmt.mantissaInRange a := by
    have htwo_n_lt :
        2 * n < 2 * fmt.minNormalMantissa :=
      Nat.mul_lt_mul_of_pos_left hn.2 (by decide)
    have htwo_min_le :
        2 * fmt.minNormalMantissa ≤ fmt.beta * fmt.minNormalMantissa :=
      Nat.mul_le_mul_right fmt.minNormalMantissa fmt.beta_ge_two
    have hbound :
        fmt.beta * fmt.minNormalMantissa = fmt.beta ^ fmt.t := by
      rw [Nat.mul_comm]
      exact fmt.minNormalMantissa_mul_beta_eq_mantissaBound
    exact lt_of_lt_of_le (lt_trans ha_lt_two_n htwo_n_lt)
      (by simpa [hbound] using htwo_min_le)
  have hn_range : fmt.mantissaInRange n :=
    fmt.subnormalMantissa_inRange hn
  have hcoeff :
      (fmt.sameExponentMantissaDiffInt a n).natAbs < fmt.beta ^ fmt.t :=
    fmt.sameExponentMantissaDiffInt_natAbs_lt_mantissaBound
      (m := a) (n := n) ha_range hn_range
  have hfin :
      fmt.finiteSystem
        (fmt.signValue false *
          ((fmt.sameExponentMantissaDiffInt a n : ℤ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) :=
    fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := false)
      (k := fmt.sameExponentMantissaDiffInt a n)
      (e := fmt.emin) ⟨le_rfl, fmt.emin_le_emax⟩ hcoeff
  convert hfin using 1
  rw [← hshift, fmt.sameExponentMantissaDiffInt_cast a n]
  simp [normalizedValue, subnormalValue, signValue]
  ring
/-- Source-shaped mixed normal/subnormal Sterbenz finite-representability
theorem.  The ratio condition forces both operands to be positive, reducing the
proof to the positive mixed lattice theorem. -/
theorem normalizedSystem_sub_subnormalSystem_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.normalizedSystem x)
    (hy : fmt.subnormalSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteSystem (x - y) := by
  rcases hx with ⟨negativeX, m, e, hm, he, rfl⟩
  rcases hy with ⟨negativeY, n, hn, rfl⟩
  cases negativeX
  · cases negativeY
    · exact
        fmt.normalizedValue_sub_subnormalValue_positive_finiteSystem_of_sterbenzRatioCondition
          (m := m) (n := n) (e := e) hm hn he hsterbenz
    · have hypos := fmt.sterbenzRatioCondition_y_pos hsterbenz
      have hyneg := fmt.subnormalValue_true_neg (m := n) hn
      linarith
  · have hxpos := fmt.sterbenzRatioCondition_x_pos hsterbenz
    have hxneg := fmt.normalizedValue_true_neg (m := m) (e := e) hm
    linarith
/-- Source-shaped mixed subnormal/normal Sterbenz finite-representability
theorem, obtained by symmetry and finite-system closure under negation. -/
theorem subnormalSystem_sub_normalizedSystem_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.subnormalSystem x)
    (hy : fmt.normalizedSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteSystem (x - y) := by
  have hsymm : fmt.sterbenzRatioCondition y x :=
    fmt.sterbenzRatioCondition_symm hsterbenz
  have hfin_yx : fmt.finiteSystem (y - x) :=
    fmt.normalizedSystem_sub_subnormalSystem_finiteSystem_of_sterbenzRatioCondition
      hy hx hsymm
  have hneg := fmt.finiteSystem_neg hfin_yx
  convert hneg using 1
  ring
/-- Full finite-system Sterbenz finite-representability theorem for the
source-facing real finite format.  Zero cases are impossible under Sterbenz's
strict positive ratio condition; the remaining normal/subnormal cases dispatch
to the closed branch theorems. -/
theorem finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x)
    (hy : fmt.finiteSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteSystem (x - y) := by
  rcases hx with hxzero | hxnorm | hxsub
  · subst x
    have hxpos := fmt.sterbenzRatioCondition_x_pos hsterbenz
    linarith
  rcases hy with hyzero | hynorm | hysub
  · subst y
    have hypos := fmt.sterbenzRatioCondition_y_pos hsterbenz
    linarith
  · exact
      fmt.normalizedSystem_sub_finiteSystem_of_sterbenzRatioCondition
        hxnorm hynorm hsterbenz
  · exact
      fmt.normalizedSystem_sub_subnormalSystem_finiteSystem_of_sterbenzRatioCondition
        hxnorm hysub hsterbenz
  rcases hy with hyzero | hynorm | hysub
  · subst y
    have hypos := fmt.sterbenzRatioCondition_y_pos hsterbenz
    linarith
  · exact
      fmt.subnormalSystem_sub_normalizedSystem_finiteSystem_of_sterbenzRatioCondition
        hxsub hynorm hsterbenz
  · exact
      fmt.subnormalSystem_sub_finiteSystem_of_sterbenzRatioCondition
        hxsub hysub hsterbenz
/-- Source-shaped inclusive Sterbenz finite-representability theorem.  The
strict interior is the existing Sterbenz theorem; the two printed endpoints
reduce to the already finite operands. -/
theorem finiteSystem_sub_finiteSystem_of_sterbenzRatioConditionLe
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x)
    (hy : fmt.finiteSystem y)
    (hsterbenz : fmt.sterbenzRatioConditionLe x y) :
    fmt.finiteSystem (x - y) := by
  rcases lt_or_eq_of_le hsterbenz.1 with hlo | hlo_eq
  · rcases lt_or_eq_of_le hsterbenz.2 with hhi | hhi_eq
    · exact
        fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
          hx hy ⟨hlo, hhi⟩
    · have hsub : x - y = y := by
        linarith
      rw [hsub]
      exact hy
  · have hsub : x - y = -x := by
      linarith
    rw [hsub]
    exact fmt.finiteSystem_neg hx
theorem guardDigitLeadingDigit_eq_zero_of_fergusonAdjacent
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e) ez)
    (hcond : ez < e) :
    fmt.guardDigitLeadingDigit
      (fmt.guardAlignedMantissaDiffInt mHigh mLow) = 0 := by
  apply fmt.guardDigitLeadingDigit_eq_zero_of_natAbs_lt_minNormalMantissa
  exact fmt.guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent
    (negative := negative) (mHigh := mHigh) (mLow := mLow)
    (e := e) (ez := ez) hz hcond
theorem guardDigitTailMantissa_eq_natAbs_of_fergusonAdjacent
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e) ez)
    (hcond : ez < e) :
    fmt.guardDigitTailMantissa
      (fmt.guardAlignedMantissaDiffInt mHigh mLow) =
        (fmt.guardAlignedMantissaDiffInt mHigh mLow).natAbs := by
  apply fmt.guardDigitTailMantissa_eq_natAbs_of_natAbs_lt_minNormalMantissa
  exact fmt.guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent
    (negative := negative) (mHigh := mHigh) (mLow := mLow)
    (e := e) (ez := ez) hz hcond
theorem guardDigitRoundedCoeff_eq_self_of_fergusonAdjacent
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e) ez)
    (hcond : ez < e) :
    fmt.guardDigitRoundedCoeff
      (fmt.guardAlignedMantissaDiffInt mHigh mLow) =
        fmt.guardAlignedMantissaDiffInt mHigh mLow := by
  apply fmt.guardDigitRoundedCoeff_eq_self_of_natAbs_lt_minNormalMantissa
  exact fmt.guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent
    (negative := negative) (mHigh := mHigh) (mLow := mLow)
    (e := e) (ez := ez) hz hcond
/-- Adjacent-exponent subtraction value after the guard word is rounded to t
digits by dropping the zero leading guard digit. -/
def guardDigitRoundedAdjacentExponentSubtractionValue
    (fmt : FloatingPointFormat) (negative : Bool) (mHigh mLow : ℕ)
    (e : ℤ) : ℝ :=
  fmt.signValue negative *
    (((fmt.guardDigitRoundedCoeff
      (fmt.guardAlignedMantissaDiffInt mHigh mLow) : ℤ) : ℝ) *
      fmt.betaR ^ (e - (fmt.t : ℤ)))
theorem normalizedValue_sub_sameSign_adjacentExponent_eq_guardDigitRounded_of_fergusonAdjacent
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e) ez)
    (hcond : ez < e) :
    fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e =
      fmt.guardDigitRoundedAdjacentExponentSubtractionValue
        negative mHigh mLow e := by
  have hround :
      fmt.guardDigitRoundedCoeff
        (fmt.guardAlignedMantissaDiffInt mHigh mLow) =
          fmt.guardAlignedMantissaDiffInt mHigh mLow :=
    fmt.guardDigitRoundedCoeff_eq_self_of_fergusonAdjacent
      (negative := negative) (mHigh := mHigh) (mLow := mLow)
      (e := e) (ez := ez) hz hcond
  have hcast :
      (((fmt.guardDigitRoundedCoeff
        (fmt.guardAlignedMantissaDiffInt mHigh mLow) : ℤ) : ℝ)) =
        fmt.guardAlignedMantissaDiff mHigh mLow := by
    rw [hround]
    exact fmt.guardAlignedMantissaDiffInt_cast mHigh mLow
  rw [fmt.normalizedValue_sub_sameSign_adjacentExponent_eq_aligned]
  simp [guardDigitRoundedAdjacentExponentSubtractionValue,
    alignedAdjacentExponentSubtractionValue, hcast]
theorem guardAlignedMantissaDiff_abs_lt_minNormalMantissa_of_fergusonAdjacent_reversed
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mLow e -
        fmt.normalizedValue negative mHigh (e + 1)) ez)
    (hcond : ez < e) :
    |fmt.guardAlignedMantissaDiff mHigh mLow| <
      (fmt.minNormalMantissa : ℝ) := by
  have hz_upper :
      |fmt.normalizedValue negative mLow e -
        fmt.normalizedValue negative mHigh (e + 1)| < fmt.betaR ^ ez :=
    fmt.normalizedExponentRepresentation_abs_lt_beta_pow hz
  have hz_lt_lower :
      |fmt.normalizedValue negative mLow e -
        fmt.normalizedValue negative mHigh (e + 1)| < fmt.betaR ^ (e - 1) :=
    lt_of_lt_of_le hz_upper
      (fmt.betaR_zpow_le_zpow_of_le (by omega : ez ≤ e - 1))
  have hvalue :=
    fmt.normalizedValue_sub_sameSign_adjacentExponent_eq_aligned
      negative mHigh mLow e
  have hscale_pos : 0 < fmt.betaR ^ (e - (fmt.t : ℤ)) :=
    fmt.betaR_zpow_pos (e - (fmt.t : ℤ))
  have hscaled :
      |fmt.guardAlignedMantissaDiff mHigh mLow| *
          fmt.betaR ^ (e - (fmt.t : ℤ)) <
        (fmt.minNormalMantissa : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    rw [← fmt.alignedAdjacentExponentSubtractionValue_abs negative mHigh mLow e]
    rw [← hvalue]
    rw [abs_sub_comm]
    simpa [fmt.minNormalMantissa_scale_eq e] using hz_lt_lower
  exact lt_of_mul_lt_mul_right hscaled (le_of_lt hscale_pos)
theorem guardAlignedMantissaDiffInt_abs_lt_minNormalMantissa_of_fergusonAdjacent_reversed
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mLow e -
        fmt.normalizedValue negative mHigh (e + 1)) ez)
    (hcond : ez < e) :
    |fmt.guardAlignedMantissaDiffInt mHigh mLow| <
      (fmt.minNormalMantissa : ℤ) := by
  have hreal :
      |((fmt.guardAlignedMantissaDiffInt mHigh mLow : ℤ) : ℝ)| <
        (fmt.minNormalMantissa : ℝ) := by
    simpa [fmt.guardAlignedMantissaDiffInt_cast mHigh mLow] using
      fmt.guardAlignedMantissaDiff_abs_lt_minNormalMantissa_of_fergusonAdjacent_reversed
        (negative := negative) (mHigh := mHigh) (mLow := mLow)
        (e := e) (ez := ez) hz hcond
  exact_mod_cast hreal
theorem guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent_reversed
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mLow e -
        fmt.normalizedValue negative mHigh (e + 1)) ez)
    (hcond : ez < e) :
    (fmt.guardAlignedMantissaDiffInt mHigh mLow).natAbs <
      fmt.minNormalMantissa := by
  have hint :
      |fmt.guardAlignedMantissaDiffInt mHigh mLow| <
        (fmt.minNormalMantissa : ℤ) :=
    fmt.guardAlignedMantissaDiffInt_abs_lt_minNormalMantissa_of_fergusonAdjacent_reversed
      (negative := negative) (mHigh := mHigh) (mLow := mLow)
      (e := e) (ez := ez) hz hcond
  have hnatInt :
      (((fmt.guardAlignedMantissaDiffInt mHigh mLow).natAbs : ℕ) : ℤ) <
        (fmt.minNormalMantissa : ℤ) := by
    simpa using hint
  exact_mod_cast hnatInt
theorem normalizedValue_sub_sameSign_reversedAdjacentExponent_eq_neg_guardDigitRounded_of_fergusonAdjacent
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mLow e -
        fmt.normalizedValue negative mHigh (e + 1)) ez)
    (hcond : ez < e) :
    fmt.normalizedValue negative mLow e -
        fmt.normalizedValue negative mHigh (e + 1) =
      -fmt.guardDigitRoundedAdjacentExponentSubtractionValue
        negative mHigh mLow e := by
  have hround :
      fmt.guardDigitRoundedCoeff
        (fmt.guardAlignedMantissaDiffInt mHigh mLow) =
          fmt.guardAlignedMantissaDiffInt mHigh mLow :=
    fmt.guardDigitRoundedCoeff_eq_self_of_natAbs_lt_minNormalMantissa
      (fmt.guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent_reversed
        (negative := negative) (mHigh := mHigh) (mLow := mLow)
        (e := e) (ez := ez) hz hcond)
  have hcast :
      (((fmt.guardDigitRoundedCoeff
        (fmt.guardAlignedMantissaDiffInt mHigh mLow) : ℤ) : ℝ)) =
        fmt.guardAlignedMantissaDiff mHigh mLow := by
    rw [hround]
    exact fmt.guardAlignedMantissaDiffInt_cast mHigh mLow
  have hforward :
      fmt.normalizedValue negative mHigh (e + 1) -
          fmt.normalizedValue negative mLow e =
        fmt.guardDigitRoundedAdjacentExponentSubtractionValue
          negative mHigh mLow e := by
    rw [fmt.normalizedValue_sub_sameSign_adjacentExponent_eq_aligned]
    simp [guardDigitRoundedAdjacentExponentSubtractionValue,
      alignedAdjacentExponentSubtractionValue, hcast]
  calc
    fmt.normalizedValue negative mLow e -
        fmt.normalizedValue negative mHigh (e + 1) =
        -(fmt.normalizedValue negative mHigh (e + 1) -
          fmt.normalizedValue negative mLow e) := by
          ring
    _ = -fmt.guardDigitRoundedAdjacentExponentSubtractionValue
        negative mHigh mLow e := by
          rw [hforward]
/-- The branch-level guard-digit subtraction value in Ferguson's proof.
It keeps the same-exponent `t`-digit difference exactly, uses the `t+1`
guard word in the high-minus-low adjacent-exponent branch, and negates that
adjacent branch when the requested subtraction has the lower exponent first. -/
def guardDigitRoundedBranchSubtractionValue
    (fmt : FloatingPointFormat) (negative : Bool) (mx my : ℕ)
    (ex ey : ℤ) : ℝ :=
  if _hsame : ex = ey then
    fmt.guardDigitRoundedSameExponentSubtractionValue negative mx my ey
  else if _hx : ex = ey + 1 then
    fmt.guardDigitRoundedAdjacentExponentSubtractionValue negative mx my ey
  else if _hy : ey = ex + 1 then
    -fmt.guardDigitRoundedAdjacentExponentSubtractionValue negative my mx ex
  else
    fmt.normalizedValue negative mx ex -
      fmt.normalizedValue negative my ey
theorem guardDigitRoundedBranchSubtractionValue_eq_sub_of_ferguson
    {fmt : FloatingPointFormat} {negative : Bool} {mx my : ℕ}
    {ex ey ez : ℤ}
    (hmx : fmt.normalizedMantissa mx)
    (hmy : fmt.normalizedMantissa my)
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mx ex -
        fmt.normalizedValue negative my ey) ez)
    (hcond : ez < min ex ey)
    (hcases : ex = ey ∨ ex = ey + 1 ∨ ey = ex + 1) :
    fmt.guardDigitRoundedBranchSubtractionValue negative mx my ex ey =
      fmt.normalizedValue negative mx ex -
        fmt.normalizedValue negative my ey := by
  unfold guardDigitRoundedBranchSubtractionValue
  by_cases hsame : ex = ey
  · rw [dif_pos hsame]
    subst ex
    exact (fmt.normalizedValue_sub_sameSign_sameExponent_eq_guardDigitRounded
      (negative := negative) (m := mx) (n := my) (e := ey) hmx hmy).symm
  · rw [dif_neg hsame]
    by_cases hx : ex = ey + 1
    · rw [dif_pos hx]
      subst ex
      have hcondEy : ez < ey :=
        lt_of_lt_of_le hcond (min_le_right (ey + 1) ey)
      exact
        (fmt.normalizedValue_sub_sameSign_adjacentExponent_eq_guardDigitRounded_of_fergusonAdjacent
          (negative := negative) (mHigh := mx) (mLow := my)
          (e := ey) (ez := ez) hz hcondEy).symm
    · rw [dif_neg hx]
      by_cases hy : ey = ex + 1
      · rw [dif_pos hy]
        subst ey
        have hcondEx : ez < ex :=
          lt_of_lt_of_le hcond (min_le_left ex (ex + 1))
        exact
          (fmt.normalizedValue_sub_sameSign_reversedAdjacentExponent_eq_neg_guardDigitRounded_of_fergusonAdjacent
            (negative := negative) (mHigh := my) (mLow := mx)
            (e := ex) (ez := ez) hz hcondEx).symm
      · rw [dif_neg hy]
/-- A concrete branch implementation contract for Ferguson subtraction.  It
does not assume exactness directly; it requires the routine to return the
rounded branch value dictated by the same-sign exponent case split. -/
def guardDigitBranchSubtractionModel
    (fmt : FloatingPointFormat) (flSub : ℝ → ℝ → ℝ) : Prop :=
  ∀ {negative : Bool} {mx my : ℕ} {ex ey ez : ℤ},
    fmt.normalizedMantissa mx →
    fmt.exponentInRange ex →
    fmt.normalizedMantissa my →
    fmt.exponentInRange ey →
    fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mx ex -
        fmt.normalizedValue negative my ey) ez →
    ez < min ex ey →
    flSub (fmt.normalizedValue negative mx ex)
      (fmt.normalizedValue negative my ey) =
        fmt.guardDigitRoundedBranchSubtractionValue negative mx my ex ey
theorem guardDigitBranchSubtractionModel_guardDigitSubtractionModel
    {fmt : FloatingPointFormat} {flSub : ℝ → ℝ → ℝ}
    (hbranch : fmt.guardDigitBranchSubtractionModel flSub) :
    fmt.guardDigitSubtractionModel flSub := by
  intro x y hferg
  rcases hferg with ⟨ex, ey, ez, hx, hy, hz, hcond⟩
  rcases hx with ⟨negativeX, mx, hmx, hex, hx_eq⟩
  rcases hy with ⟨negativeY, my, hmy, hey, hy_eq⟩
  subst x
  subst y
  have hsign : negativeX = negativeY :=
    fmt.normalizedValue_sub_fergusonCondition_sign_eq
      (negativeX := negativeX) (negativeY := negativeY)
      (mx := mx) (my := my) (ex := ex) (ey := ey) (ez := ez)
      hmx hmy hz hcond
  subst negativeY
  have hx_repr :
      fmt.normalizedExponentRepresentation
        (fmt.normalizedValue negativeX mx ex) ex :=
    ⟨negativeX, mx, hmx, hex, rfl⟩
  have hy_repr :
      fmt.normalizedExponentRepresentation
        (fmt.normalizedValue negativeX my ey) ey :=
    ⟨negativeX, my, hmy, hey, rfl⟩
  have hgap :
      ex ≤ ey + 1 ∧ ey ≤ ex + 1 :=
    fmt.normalizedExponentRepresentation_sub_exponent_gap_le_one
      hx_repr hy_repr hz hcond
  have hcases : ex = ey ∨ ex = ey + 1 ∨ ey = ex + 1 := by
    omega
  have hfl :=
    hbranch hmx hex hmy hey hz hcond
  rw [hfl]
  exact fmt.guardDigitRoundedBranchSubtractionValue_eq_sub_of_ferguson
    (negative := negativeX) (mx := mx) (my := my)
    (ex := ex) (ey := ey) (ez := ez) hmx hmy hz hcond hcases
theorem guardDigitBranchSubtractionModel_exact_of_fergusonCondition
    {fmt : FloatingPointFormat} {flSub : ℝ → ℝ → ℝ} {x y : ℝ}
    (hbranch : fmt.guardDigitBranchSubtractionModel flSub)
    (hcond : fmt.fergusonExponentCondition x y) :
    flSub x y = x - y :=
  fmt.guardDigitBranchSubtractionModel_guardDigitSubtractionModel hbranch hcond
/-- Normalized branch data for the Ferguson guard-digit subtraction proof.
This is the representation-selection evidence needed by the branch-level
routine below. -/
structure GuardDigitBranchSubtractionData
    (fmt : FloatingPointFormat) (x y : ℝ) where
  negative : Bool
  mx : ℕ
  my : ℕ
  ex : ℤ
  ey : ℤ
  ez : ℤ
  hmx : fmt.normalizedMantissa mx
  hex : fmt.exponentInRange ex
  hx : x = fmt.normalizedValue negative mx ex
  hmy : fmt.normalizedMantissa my
  hey : fmt.exponentInRange ey
  hy : y = fmt.normalizedValue negative my ey
  hz : fmt.normalizedExponentRepresentation (x - y) ez
  hcond : ez < min ex ey
theorem GuardDigitBranchSubtractionData.exponent_cases
    {fmt : FloatingPointFormat} {x y : ℝ}
    (d : GuardDigitBranchSubtractionData fmt x y) :
    d.ex = d.ey ∨ d.ex = d.ey + 1 ∨ d.ey = d.ex + 1 := by
  have hx_repr : fmt.normalizedExponentRepresentation x d.ex :=
    ⟨d.negative, d.mx, d.hmx, d.hex, d.hx⟩
  have hy_repr : fmt.normalizedExponentRepresentation y d.ey :=
    ⟨d.negative, d.my, d.hmy, d.hey, d.hy⟩
  have hgap :
      d.ex ≤ d.ey + 1 ∧ d.ey ≤ d.ex + 1 :=
    fmt.normalizedExponentRepresentation_sub_exponent_gap_le_one
      hx_repr hy_repr d.hz d.hcond
  omega
theorem GuardDigitBranchSubtractionData.branchValue_eq_sub
    {fmt : FloatingPointFormat} {x y : ℝ}
    (d : GuardDigitBranchSubtractionData fmt x y) :
    fmt.guardDigitRoundedBranchSubtractionValue
        d.negative d.mx d.my d.ex d.ey =
      x - y := by
  have hbranch :=
    fmt.guardDigitRoundedBranchSubtractionValue_eq_sub_of_ferguson
      (negative := d.negative) (mx := d.mx) (my := d.my)
      (ex := d.ex) (ey := d.ey) (ez := d.ez)
      d.hmx d.hmy
      (by
        simpa [d.hx, d.hy] using d.hz)
      d.hcond d.exponent_cases
  simpa [d.hx, d.hy] using hbranch
/-- The branch-selected guard-digit value is a finite floating-point value.
The same-exponent branch uses the finite-difference selector derived from the
operand mantissas; the adjacent branches use Ferguson's normalized
representation of the exact difference. -/
theorem guardDigitRoundedBranchSubtractionValue_finiteSystem_of_ferguson
    {fmt : FloatingPointFormat} {negative : Bool} {mx my : ℕ}
    {ex ey ez : ℤ}
    (hmx : fmt.normalizedMantissa mx) (hex : fmt.exponentInRange ex)
    (hmy : fmt.normalizedMantissa my) (hey : fmt.exponentInRange ey)
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mx ex -
        fmt.normalizedValue negative my ey) ez)
    (hcond : ez < min ex ey) :
    fmt.finiteSystem
      (fmt.guardDigitRoundedBranchSubtractionValue negative mx my ex ey) := by
  unfold guardDigitRoundedBranchSubtractionValue
  by_cases hsame : ex = ey
  · rw [dif_pos hsame]
    subst ex
    have hfinite :
        fmt.finiteSystem
          (fmt.normalizedValue negative mx ey -
            fmt.normalizedValue negative my ey) :=
      fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedMantissas
        (negative := negative) (m := mx) (n := my) (e := ey) hmx hmy hey
    have hvalue :
        fmt.normalizedValue negative mx ey -
            fmt.normalizedValue negative my ey =
          fmt.guardDigitRoundedSameExponentSubtractionValue
            negative mx my ey :=
      fmt.normalizedValue_sub_sameSign_sameExponent_eq_guardDigitRounded
        (negative := negative) (m := mx) (n := my) (e := ey) hmx hmy
    rwa [← hvalue]
  · rw [dif_neg hsame]
    by_cases hx : ex = ey + 1
    · rw [dif_pos hx]
      subst ex
      have hcondEy : ez < ey :=
        lt_of_lt_of_le hcond (min_le_right (ey + 1) ey)
      have hvalue :
          fmt.normalizedValue negative mx (ey + 1) -
              fmt.normalizedValue negative my ey =
            fmt.guardDigitRoundedAdjacentExponentSubtractionValue
              negative mx my ey :=
        fmt.normalizedValue_sub_sameSign_adjacentExponent_eq_guardDigitRounded_of_fergusonAdjacent
          (negative := negative) (mHigh := mx) (mLow := my)
          (e := ey) (ez := ez) hz hcondEy
      have hfinite :
          fmt.finiteSystem
            (fmt.normalizedValue negative mx (ey + 1) -
              fmt.normalizedValue negative my ey) :=
        Or.inr (Or.inl
          (fmt.normalizedExponentRepresentation_normalizedSystem hz))
      rwa [← hvalue]
    · rw [dif_neg hx]
      by_cases hy : ey = ex + 1
      · rw [dif_pos hy]
        subst ey
        have hcondEx : ez < ex :=
          lt_of_lt_of_le hcond (min_le_left ex (ex + 1))
        have hvalue :
            fmt.normalizedValue negative mx ex -
                fmt.normalizedValue negative my (ex + 1) =
              -fmt.guardDigitRoundedAdjacentExponentSubtractionValue
                negative my mx ex :=
          fmt.normalizedValue_sub_sameSign_reversedAdjacentExponent_eq_neg_guardDigitRounded_of_fergusonAdjacent
            (negative := negative) (mHigh := my) (mLow := mx)
            (e := ex) (ez := ez) hz hcondEx
        have hfinite :
            fmt.finiteSystem
              (fmt.normalizedValue negative mx ex -
                fmt.normalizedValue negative my (ex + 1)) :=
          Or.inr (Or.inl
            (fmt.normalizedExponentRepresentation_normalizedSystem hz))
        rwa [← hvalue]
      · rw [dif_neg hy]
        exact Or.inr (Or.inl
          (fmt.normalizedExponentRepresentation_normalizedSystem hz))
theorem GuardDigitBranchSubtractionData.branchValue_finiteSystem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (d : GuardDigitBranchSubtractionData fmt x y) :
    fmt.finiteSystem
      (fmt.guardDigitRoundedBranchSubtractionValue
        d.negative d.mx d.my d.ex d.ey) := by
  exact
    fmt.guardDigitRoundedBranchSubtractionValue_finiteSystem_of_ferguson
      d.hmx d.hex d.hmy d.hey
      (by simpa [d.hx, d.hy] using d.hz) d.hcond
/-- Noncomputable branch selector for Ferguson subtraction.  If normalized
Ferguson branch data are available, it returns the branch-rounded value from
that data; otherwise it falls back to exact subtraction.  The fallback is only a
totality device and is not used in the Ferguson theorem. -/
noncomputable def guardDigitBranchSubtractionRoutine
    (fmt : FloatingPointFormat) (x y : ℝ) : ℝ := by
  classical
  exact
    if h : Nonempty (GuardDigitBranchSubtractionData fmt x y) then
      let d := Classical.choice h
      fmt.guardDigitRoundedBranchSubtractionValue
        d.negative d.mx d.my d.ex d.ey
    else
      x - y
theorem guardDigitBranchSubtractionRoutine_eq_sub_of_data
    {fmt : FloatingPointFormat} {x y : ℝ}
    (d : GuardDigitBranchSubtractionData fmt x y) :
    fmt.guardDigitBranchSubtractionRoutine x y = x - y := by
  classical
  unfold guardDigitBranchSubtractionRoutine
  rw [dif_pos ⟨d⟩]
  exact (Classical.choice ⟨d⟩).branchValue_eq_sub
theorem guardDigitBranchSubtractionRoutine_branchModel
    {fmt : FloatingPointFormat} :
    fmt.guardDigitBranchSubtractionModel
      (fmt.guardDigitBranchSubtractionRoutine) := by
  intro negative mx my ex ey ez hmx hex hmy hey hz hcond
  let x := fmt.normalizedValue negative mx ex
  let y := fmt.normalizedValue negative my ey
  let d : GuardDigitBranchSubtractionData fmt x y :=
    { negative := negative
      mx := mx
      my := my
      ex := ex
      ey := ey
      ez := ez
      hmx := hmx
      hex := hex
      hx := rfl
      hmy := hmy
      hey := hey
      hy := rfl
      hz := hz
      hcond := hcond }
  have hroutine :
      fmt.guardDigitBranchSubtractionRoutine x y = x - y :=
    fmt.guardDigitBranchSubtractionRoutine_eq_sub_of_data d
  have hbranch :
      fmt.guardDigitRoundedBranchSubtractionValue negative mx my ex ey =
        x - y := by
    exact d.branchValue_eq_sub
  simpa [x, y] using hroutine.trans hbranch.symm
theorem guardDigitBranchSubtractionRoutine_guardDigitSubtractionModel
    {fmt : FloatingPointFormat} :
    fmt.guardDigitSubtractionModel
      (fmt.guardDigitBranchSubtractionRoutine) :=
  fmt.guardDigitBranchSubtractionModel_guardDigitSubtractionModel
    fmt.guardDigitBranchSubtractionRoutine_branchModel
theorem guardDigitBranchSubtractionRoutine_exact_of_fergusonCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonExponentCondition x y) :
    fmt.guardDigitBranchSubtractionRoutine x y = x - y :=
  fmt.guardDigitBranchSubtractionRoutine_guardDigitSubtractionModel hcond
theorem guardDigitBranchSubtractionRoutine_finiteSystem_of_data
    {fmt : FloatingPointFormat} {x y : ℝ}
    (d : GuardDigitBranchSubtractionData fmt x y) :
    fmt.finiteSystem (fmt.guardDigitBranchSubtractionRoutine x y) := by
  rw [fmt.guardDigitBranchSubtractionRoutine_eq_sub_of_data d]
  exact Or.inr (Or.inl
    (fmt.normalizedExponentRepresentation_normalizedSystem d.hz))
theorem guardDigitBranchSubtractionRoutine_finiteSystem_of_fergusonCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonExponentCondition x y) :
    fmt.finiteSystem (fmt.guardDigitBranchSubtractionRoutine x y) := by
  rw [fmt.guardDigitBranchSubtractionRoutine_exact_of_fergusonCondition hcond]
  exact Or.inr (Or.inl (fmt.fergusonExponentCondition_sub_normalized hcond))
/-- The one-digit decimal audit format contains `9` as a finite value. -/
theorem decimalSingleDigitFormat_finiteSystem_nine :
    decimalSingleDigitFormat.finiteSystem (9 : ℝ) := by
  exact Or.inr (Or.inl
    (decimalSingleDigitFormat.normalizedExponentRepresentation_normalizedSystem
      decimalSingleDigitFormat_normalizedExponentRepresentation_nine))
/-- The one-digit decimal audit format does not contain `18`; it is above the
largest finite magnitude. -/
theorem decimalSingleDigitFormat_not_finiteSystem_eighteen :
    ¬ decimalSingleDigitFormat.finiteSystem (18 : ℝ) := by
  intro h
  have hclass :=
    decimalSingleDigitFormat.finiteSystem_zero_or_finiteNormalRange_or_finiteUnderflowRange h
  rcases hclass with hzero | hnormal | hunder
  · norm_num at hzero
  · norm_num [finiteNormalRange, minNormalMagnitude, maxFiniteMagnitude,
      decimalSingleDigitFormat, betaR] at hnormal
    exact (by norm_num : ¬ (18 : ℝ) ≤ 9) hnormal
  · norm_num [finiteUnderflowRange, minNormalMagnitude,
      decimalSingleDigitFormat, betaR] at hunder
/-- Finite representability of operands alone does not make exact subtraction
finite representable.  The one-digit decimal audit format has finite operands
`9` and `-9`, but their exact difference `18` is outside the finite system. -/
theorem not_forall_finiteSystem_sub_finiteSystem :
    ¬ (∀ (fmt : FloatingPointFormat) (x y : ℝ),
        fmt.finiteSystem x → fmt.finiteSystem y →
          fmt.finiteSystem (x - y)) := by
  intro h
  have h9 : decimalSingleDigitFormat.finiteSystem (9 : ℝ) :=
    decimalSingleDigitFormat_finiteSystem_nine
  have hneg9 : decimalSingleDigitFormat.finiteSystem (-9 : ℝ) := by
    simpa using decimalSingleDigitFormat.finiteSystem_neg h9
  have hbad := h decimalSingleDigitFormat (9 : ℝ) (-9 : ℝ) h9 hneg9
  norm_num at hbad
  exact decimalSingleDigitFormat_not_finiteSystem_eighteen hbad
/-- A one-digit decimal audit format with exponent range `1..2`.

It is useful for overflow-saturation counterexamples: `1` and `90` are finite,
but the exact sum `91` rounds back to the maximum finite value `90`. -/
def decimalSingleDigitTwoExponentFormat : FloatingPointFormat where
  beta := 10
  t := 1
  emin := 1
  emax := 2
  beta_ge_two := by norm_num
  t_pos := by norm_num
  emin_le_emax := by norm_num
/-- The two-exponent one-digit decimal audit format contains `1`. -/
theorem decimalSingleDigitTwoExponentFormat_finiteSystem_one :
    decimalSingleDigitTwoExponentFormat.finiteSystem (1 : ℝ) := by
  exact Or.inr (Or.inl
    (decimalSingleDigitTwoExponentFormat.normalizedExponentRepresentation_normalizedSystem
      (show
        decimalSingleDigitTwoExponentFormat.normalizedExponentRepresentation
          (1 : ℝ) 1 from by
        refine ⟨false, 1, ?_, ?_, ?_⟩
        · norm_num [decimalSingleDigitTwoExponentFormat, normalizedMantissa,
            mantissaInRange, minNormalMantissa]
        · norm_num [decimalSingleDigitTwoExponentFormat, exponentInRange]
        · norm_num [decimalSingleDigitTwoExponentFormat, normalizedValue,
            signValue, betaR])))
/-- The two-exponent one-digit decimal audit format contains `90`. -/
theorem decimalSingleDigitTwoExponentFormat_finiteSystem_ninety :
    decimalSingleDigitTwoExponentFormat.finiteSystem (90 : ℝ) := by
  exact Or.inr (Or.inl
    (decimalSingleDigitTwoExponentFormat.normalizedExponentRepresentation_normalizedSystem
      (show
        decimalSingleDigitTwoExponentFormat.normalizedExponentRepresentation
          (90 : ℝ) 2 from by
        refine ⟨false, 9, ?_, ?_, ?_⟩
        · norm_num [decimalSingleDigitTwoExponentFormat, normalizedMantissa,
            mantissaInRange, minNormalMantissa]
        · norm_num [decimalSingleDigitTwoExponentFormat, exponentInRange]
        · norm_num [decimalSingleDigitTwoExponentFormat, normalizedValue,
            signValue, betaR])))
/-- The two-exponent one-digit decimal audit format does not contain `89`. -/
theorem decimalSingleDigitTwoExponentFormat_not_finiteSystem_eightynine :
    ¬ decimalSingleDigitTwoExponentFormat.finiteSystem (89 : ℝ) := by
  intro h
  rcases h with hzero | hnorm | hsub
  · norm_num at hzero
  · rcases hnorm with ⟨negative, m, e, hm, he, hval⟩
    norm_num [decimalSingleDigitTwoExponentFormat, exponentInRange] at he
    have he_cases : e = 1 ∨ e = 2 := by omega
    rcases he_cases with rfl | rfl
    · cases negative <;>
        norm_num [decimalSingleDigitTwoExponentFormat, normalizedMantissa,
          mantissaInRange, minNormalMantissa, normalizedValue, signValue, betaR] at hm hval
      all_goals
        have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
        have hm_lt : (m : ℝ) < 10 := by exact_mod_cast hm.2
        nlinarith
    · cases negative
      · norm_num [decimalSingleDigitTwoExponentFormat, normalizedMantissa,
          mantissaInRange, minNormalMantissa, normalizedValue, signValue, betaR] at hm hval
        have hval_nat : 89 = m * 10 := by
          exact_mod_cast hval
        omega
      · norm_num [decimalSingleDigitTwoExponentFormat, normalizedMantissa,
          mantissaInRange, minNormalMantissa, normalizedValue, signValue, betaR] at hm hval
        have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
        nlinarith
  · rcases hsub with ⟨negative, m, hm, hval⟩
    norm_num [decimalSingleDigitTwoExponentFormat, subnormalMantissa,
      minNormalMantissa] at hm
    omega
/-- Adding the negation of a normalized operand is exact under Sterbenz's ratio
condition.  This packages the opposite-sign normalized-add branch as ordinary
Sterbenz subtraction. -/
theorem finiteRoundToEvenOp_add_neg_right_normalizedSystem_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.normalizedSystem x)
    (hy : fmt.normalizedSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteRoundToEvenOp BasicOp.add x (-y) = x + (-y) := by
  have hfin_sub : fmt.finiteSystem (x - y) :=
    fmt.normalizedSystem_sub_finiteSystem_of_sterbenzRatioCondition
      hx hy hsterbenz
  have hfin_add : fmt.finiteSystem (x + (-y)) := by
    simpa [sub_eq_add_neg] using hfin_sub
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add) (x := x) (y := -y) hfin_add)
/-- The local roundoff error is finite for normalized `x + (-y)` under
Sterbenz's ratio condition, since the rounded add is exact. -/
theorem finiteRoundToEvenOp_add_neg_right_normalizedSystem_error_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.normalizedSystem x)
    (hy : fmt.normalizedSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteSystem
      ((x + (-y)) - fmt.finiteRoundToEvenOp BasicOp.add x (-y)) := by
  rw [
    fmt.finiteRoundToEvenOp_add_neg_right_normalizedSystem_eq_exact_of_sterbenzRatioCondition
      hx hy hsterbenz]
  simpa using fmt.finiteSystem_zero
/-- Positive normalized specialization of the Sterbenz exact `x + (-y)` branch,
written with an explicit negative second operand. -/
theorem finiteRoundToEvenOp_add_neg_right_positive_normalizedValue_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e)
    (he' : fmt.exponentInRange e')
    (hsterbenz : fmt.sterbenzRatioCondition
      (fmt.normalizedValue false m e)
      (fmt.normalizedValue false n e')) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue false m e)
        (fmt.normalizedValue true n e') =
      fmt.normalizedValue false m e + fmt.normalizedValue true n e' := by
  have hx : fmt.normalizedSystem (fmt.normalizedValue false m e) :=
    ⟨false, m, e, hm, he, rfl⟩
  have hy : fmt.normalizedSystem (fmt.normalizedValue false n e') :=
    ⟨false, n, e', hn, he', rfl⟩
  simpa [fmt.normalizedValue_true_eq_neg_false n e'] using
    (fmt.finiteRoundToEvenOp_add_neg_right_normalizedSystem_eq_exact_of_sterbenzRatioCondition
      hx hy hsterbenz)
/-- Positive normalized specialization of the finite-error form of exact
Sterbenz `x + (-y)` addition. -/
theorem finiteRoundToEvenOp_add_neg_right_positive_normalizedValue_error_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e)
    (he' : fmt.exponentInRange e')
    (hsterbenz : fmt.sterbenzRatioCondition
      (fmt.normalizedValue false m e)
      (fmt.normalizedValue false n e')) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.normalizedValue true n e') -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.normalizedValue true n e')) := by
  rw [
    fmt.finiteRoundToEvenOp_add_neg_right_positive_normalizedValue_eq_exact_of_sterbenzRatioCondition
      hm hn he he' hsterbenz]
  simpa using fmt.finiteSystem_zero
/-- Adding the negation of a finite representable operand is exact under
Sterbenz's ratio condition, including normal, subnormal, and mixed branches. -/
theorem finiteRoundToEvenOp_add_neg_right_finiteSystem_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x)
    (hy : fmt.finiteSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteRoundToEvenOp BasicOp.add x (-y) = x + (-y) := by
  have hfin_sub : fmt.finiteSystem (x - y) :=
    fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition hx hy hsterbenz
  have hfin_add : fmt.finiteSystem (x + (-y)) := by
    simpa [sub_eq_add_neg] using hfin_sub
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add) (x := x) (y := -y) hfin_add)
/-- The local roundoff error is finite for finite-system `x + (-y)` under
Sterbenz's ratio condition, since the rounded add is exact. -/
theorem finiteRoundToEvenOp_add_neg_right_finiteSystem_error_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x)
    (hy : fmt.finiteSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteSystem
      ((x + (-y)) - fmt.finiteRoundToEvenOp BasicOp.add x (-y)) := by
  rw [
    fmt.finiteRoundToEvenOp_add_neg_right_finiteSystem_eq_exact_of_sterbenzRatioCondition
      hx hy hsterbenz]
  simpa using fmt.finiteSystem_zero
/-- Commuted finite-system form of exact Sterbenz addition with an explicit
negative operand. -/
theorem finiteRoundToEvenOp_add_neg_left_finiteSystem_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x)
    (hy : fmt.finiteSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteRoundToEvenOp BasicOp.add (-y) x = (-y) + x := by
  have hfin_sub : fmt.finiteSystem (x - y) :=
    fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition hx hy hsterbenz
  have hfin_add : fmt.finiteSystem ((-y) + x) := by
    convert hfin_sub using 1
    ring
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add) (x := -y) (y := x) hfin_add)
/-- The local roundoff error is finite for the commuted finite-system
Sterbenz add-neg branch. -/
theorem finiteRoundToEvenOp_add_neg_left_finiteSystem_error_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x)
    (hy : fmt.finiteSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteSystem
      (((-y) + x) - fmt.finiteRoundToEvenOp BasicOp.add (-y) x) := by
  rw [
    fmt.finiteRoundToEvenOp_add_neg_left_finiteSystem_eq_exact_of_sterbenzRatioCondition
      hx hy hsterbenz]
  simpa using fmt.finiteSystem_zero
/-- Positive adjacent-exponent Sterbenz subtraction is exact for the concrete
finite round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_sub_positive_adjacentExponent_eq_exact_of_sterbenzAdjacent
    {fmt : FloatingPointFormat} {mHigh mLow : ℕ} {e : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (he : fmt.exponentInRange e)
    (hsterbenz : fmt.sterbenzRatioCondition
      (fmt.normalizedValue false mHigh (e + 1))
      (fmt.normalizedValue false mLow e)) :
    fmt.finiteRoundToEvenOp BasicOp.sub
        (fmt.normalizedValue false mHigh (e + 1))
        (fmt.normalizedValue false mLow e) =
      fmt.normalizedValue false mHigh (e + 1) -
        fmt.normalizedValue false mLow e := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue false mHigh (e + 1) -
          fmt.normalizedValue false mLow e) :=
    fmt.normalizedValue_sub_positive_adjacentExponent_finiteSystem_of_sterbenzAdjacent
      (mHigh := mHigh) (mLow := mLow) (e := e)
      hmHigh hmLow he hsterbenz
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub)
      (x := fmt.normalizedValue false mHigh (e + 1))
      (y := fmt.normalizedValue false mLow e) hfin)
/-- Positive normalized Sterbenz subtraction is exact for the concrete finite
round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_sub_positive_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e)
    (he' : fmt.exponentInRange e')
    (hsterbenz : fmt.sterbenzRatioCondition
      (fmt.normalizedValue false m e)
      (fmt.normalizedValue false n e')) :
    fmt.finiteRoundToEvenOp BasicOp.sub
        (fmt.normalizedValue false m e)
        (fmt.normalizedValue false n e') =
      fmt.normalizedValue false m e -
        fmt.normalizedValue false n e' := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue false m e -
          fmt.normalizedValue false n e') :=
    fmt.normalizedValue_sub_positive_finiteSystem_of_sterbenzRatioCondition
      (m := m) (n := n) (e := e) (e' := e')
      hm hn he he' hsterbenz
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub)
      (x := fmt.normalizedValue false m e)
      (y := fmt.normalizedValue false n e') hfin)
/-- Source-shaped normalized Sterbenz subtraction is exact for the concrete
finite round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_sub_normalizedSystem_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.normalizedSystem x)
    (hy : fmt.normalizedSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hfin : fmt.finiteSystem (x - y) :=
    fmt.normalizedSystem_sub_finiteSystem_of_sterbenzRatioCondition
      hx hy hsterbenz
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := x) (y := y) hfin)
/-- Source-shaped subnormal Sterbenz subtraction is exact for the concrete
finite round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_sub_subnormalSystem_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.subnormalSystem x)
    (hy : fmt.subnormalSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hfin : fmt.finiteSystem (x - y) :=
    fmt.subnormalSystem_sub_finiteSystem_of_sterbenzRatioCondition
      hx hy hsterbenz
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := x) (y := y) hfin)
/-- Mixed normal/subnormal Sterbenz subtraction is exact for the concrete
finite round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_sub_normalizedSystem_subnormalSystem_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.normalizedSystem x)
    (hy : fmt.subnormalSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hfin : fmt.finiteSystem (x - y) :=
    fmt.normalizedSystem_sub_subnormalSystem_finiteSystem_of_sterbenzRatioCondition
      hx hy hsterbenz
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := x) (y := y) hfin)
/-- Mixed subnormal/normal Sterbenz subtraction is exact for the concrete
finite round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_sub_subnormalSystem_normalizedSystem_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.subnormalSystem x)
    (hy : fmt.normalizedSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hfin : fmt.finiteSystem (x - y) :=
    fmt.subnormalSystem_sub_normalizedSystem_finiteSystem_of_sterbenzRatioCondition
      hx hy hsterbenz
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := x) (y := y) hfin)
/-- Full source-facing finite-system Sterbenz subtraction is exact for the
concrete finite round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x)
    (hy : fmt.finiteSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hfin : fmt.finiteSystem (x - y) :=
    fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
      hx hy hsterbenz
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := x) (y := y) hfin)
/-- Source-shaped inclusive form of Higham Theorem 2.5 (Sterbenz) for the
concrete finite round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioConditionLe
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x)
    (hy : fmt.finiteSystem y)
    (hsterbenz : fmt.sterbenzRatioConditionLe x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hfin : fmt.finiteSystem (x - y) :=
    fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioConditionLe
      hx hy hsterbenz
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := x) (y := y) hfin)
theorem finiteRoundToEvenOp_sub_eq_exact_of_guardDigitBranchSubtractionData
    {fmt : FloatingPointFormat} {x y : ℝ}
    (d : GuardDigitBranchSubtractionData fmt x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hfin :
      fmt.finiteSystem (BasicOp.exact BasicOp.sub x y) := by
    simpa [BasicOp.exact] using
      (Or.inr (Or.inl
        (fmt.normalizedExponentRepresentation_normalizedSystem d.hz)) :
        fmt.finiteSystem (x - y))
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := x) (y := y) hfin)
theorem finiteRoundToEvenOp_sub_eq_exact_of_fergusonCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonExponentCondition x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hfin :
      fmt.finiteSystem (BasicOp.exact BasicOp.sub x y) := by
    simpa [BasicOp.exact] using
      (Or.inr (Or.inl
        (fmt.fergusonExponentCondition_sub_normalized hcond)) :
        fmt.finiteSystem (x - y))
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := x) (y := y) hfin)
/-- Under the printed Ferguson magnitude condition and the source's explicit
no-underflow proviso, the internally reconstructed exact difference is a
normalized finite value. -/
theorem fergusonMagnitudeExponentConditionLe_sub_normalized_of_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonMagnitudeExponentConditionLe x y)
    (hnoUnderflow : ¬ fmt.finiteUnderflowRange (x - y)) :
    fmt.normalizedSystem (x - y) := by
  have hfin : fmt.finiteSystem (x - y) :=
    fmt.fergusonMagnitudeExponentConditionLe_sub_finiteSystem hcond
  rcases hfin with hzero | hnormal | hsubnormal
  · exfalso
    apply hnoUnderflow
    rw [hzero]
    simpa [finiteUnderflowRange] using fmt.minNormalMagnitude_pos
  · exact hnormal
  · exfalso
    exact hnoUnderflow (fmt.subnormalSystem_finiteUnderflowRange hsubnormal)
/-- Source-facing Higham Theorem 2.4 (Ferguson): the hypotheses are the
printed magnitude/exponent condition and the separate no-underflow proviso.
The representation of `x-y` is derived internally from the common radix
lattice before exactness of the concrete finite round-to-even operation is
invoked. -/
theorem finiteRoundToEvenOp_sub_eq_exact_of_fergusonMagnitudeExponentConditionLe
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonMagnitudeExponentConditionLe x y)
    (hnoUnderflow : ¬ fmt.finiteUnderflowRange (x - y)) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hnormal : fmt.normalizedSystem (x - y) :=
    fmt.fergusonMagnitudeExponentConditionLe_sub_normalized_of_not_finiteUnderflowRange
      hcond hnoUnderflow
  have hfin : fmt.finiteSystem (BasicOp.exact BasicOp.sub x y) := by
    simpa [BasicOp.exact] using
      (Or.inr (Or.inl hnormal) : fmt.finiteSystem (x - y))
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := x) (y := y) hfin)
/-- Compatibility theorem for the older representation-form inclusive
Ferguson condition.  Its proof now factors through the source-facing
magnitude theorem above. -/
theorem finiteRoundToEvenOp_sub_eq_exact_of_fergusonConditionLe
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonExponentConditionLe x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  exact
    fmt.finiteRoundToEvenOp_sub_eq_exact_of_fergusonMagnitudeExponentConditionLe
      (fmt.fergusonExponentConditionLe_fergusonMagnitudeExponentConditionLe
        hcond)
      (fmt.normalizedSystem_not_finiteUnderflowRange
        (fmt.fergusonExponentConditionLe_sub_normalized hcond))
/-- Ferguson's exponent condition places the exact subtraction result in the
finite-normal range.  This is the source's "assuming `x-y` does not underflow
or overflow" side condition, exposed in the finite-range vocabulary. -/
theorem fergusonExponentCondition_sub_finiteNormalRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonExponentCondition x y) :
    fmt.finiteNormalRange (x - y) :=
  fmt.normalizedSystem_finiteNormalRange
    (fmt.fergusonExponentCondition_sub_normalized hcond)
/-- The inclusive source-shaped Ferguson condition also places the exact
subtraction result in the finite-normal range. -/
theorem fergusonExponentConditionLe_sub_finiteNormalRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonExponentConditionLe x y) :
    fmt.finiteNormalRange (x - y) :=
  fmt.normalizedSystem_finiteNormalRange
    (fmt.fergusonExponentConditionLe_sub_normalized hcond)
/-- The source-facing magnitude Ferguson condition plus its no-underflow
proviso places the internally reconstructed exact result in the finite-normal
range. -/
theorem fergusonMagnitudeExponentConditionLe_sub_finiteNormalRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonMagnitudeExponentConditionLe x y)
    (hnoUnderflow : ¬ fmt.finiteUnderflowRange (x - y)) :
    fmt.finiteNormalRange (x - y) :=
  fmt.normalizedSystem_finiteNormalRange
    (fmt.fergusonMagnitudeExponentConditionLe_sub_normalized_of_not_finiteUnderflowRange
      hcond hnoUnderflow)
/-- IEEE-facing nearest/even version of Ferguson exact subtraction.  Under the
source-shaped Ferguson condition, the primitive subtraction wrapper takes the
finite/no-flags branch and its value is exactly `x-y`. -/
theorem ieeeRoundToNearestEvenOpResult_sub_eq_finiteNoFlags_of_fergusonCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonExponentCondition x y) :
    fmt.ieeeRoundToNearestEvenOpResult BasicOp.sub x y =
      IeeeOperationResult.finiteNoFlags (x - y) := by
  have hnormal :
      fmt.finiteNormalRange (BasicOp.exact BasicOp.sub x y) := by
    simpa [BasicOp.exact] using
      fmt.fergusonExponentCondition_sub_finiteNormalRange hcond
  have hbranch :=
    fmt.ieeeRoundToNearestEvenOpResult_eq_finiteNoFlags_of_finiteNormalRange
      (op := BasicOp.sub) (x := x) (y := y) hnormal
  rw [fmt.finiteRoundToEvenOp_sub_eq_exact_of_fergusonCondition hcond] at hbranch
  exact hbranch
theorem ieeeRoundToNearestEvenOpResult_sub_noFlags_of_fergusonCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonExponentCondition x y) :
    (fmt.ieeeRoundToNearestEvenOpResult BasicOp.sub x y).noFlags := by
  rw [fmt.ieeeRoundToNearestEvenOpResult_sub_eq_finiteNoFlags_of_fergusonCondition
    hcond]
  exact IeeeOperationResult.finiteNoFlags_noFlags _
theorem ieeeRoundToNearestEvenOpResult_sub_toReal?_of_fergusonCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonExponentCondition x y) :
    (fmt.ieeeRoundToNearestEvenOpResult BasicOp.sub x y).value.toReal? =
      some (x - y) := by
  rw [fmt.ieeeRoundToNearestEvenOpResult_sub_eq_finiteNoFlags_of_fergusonCondition
    hcond]
  exact IeeeOperationResult.finiteNoFlags_toReal? _
/-- IEEE-facing nearest/even form of the source-facing Ferguson theorem.  The
same magnitude/exponent and no-underflow hypotheses give the normal/no-flags
branch and the exact real subtraction value. -/
theorem ieeeRoundToNearestEvenOpResult_sub_eq_finiteNoFlags_of_fergusonMagnitudeExponentConditionLe
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonMagnitudeExponentConditionLe x y)
    (hnoUnderflow : ¬ fmt.finiteUnderflowRange (x - y)) :
    fmt.ieeeRoundToNearestEvenOpResult BasicOp.sub x y =
      IeeeOperationResult.finiteNoFlags (x - y) := by
  have hnormal :
      fmt.finiteNormalRange (BasicOp.exact BasicOp.sub x y) := by
    simpa [BasicOp.exact] using
      fmt.fergusonMagnitudeExponentConditionLe_sub_finiteNormalRange
        hcond hnoUnderflow
  have hbranch :=
    fmt.ieeeRoundToNearestEvenOpResult_eq_finiteNoFlags_of_finiteNormalRange
      (op := BasicOp.sub) (x := x) (y := y) hnormal
  rw [fmt.finiteRoundToEvenOp_sub_eq_exact_of_fergusonMagnitudeExponentConditionLe
    hcond hnoUnderflow] at hbranch
  exact hbranch
theorem ieeeRoundToNearestEvenOpResult_sub_noFlags_of_fergusonMagnitudeExponentConditionLe
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonMagnitudeExponentConditionLe x y)
    (hnoUnderflow : ¬ fmt.finiteUnderflowRange (x - y)) :
    (fmt.ieeeRoundToNearestEvenOpResult BasicOp.sub x y).noFlags := by
  rw [fmt.ieeeRoundToNearestEvenOpResult_sub_eq_finiteNoFlags_of_fergusonMagnitudeExponentConditionLe
    hcond hnoUnderflow]
  exact IeeeOperationResult.finiteNoFlags_noFlags _
theorem ieeeRoundToNearestEvenOpResult_sub_toReal?_of_fergusonMagnitudeExponentConditionLe
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonMagnitudeExponentConditionLe x y)
    (hnoUnderflow : ¬ fmt.finiteUnderflowRange (x - y)) :
    (fmt.ieeeRoundToNearestEvenOpResult BasicOp.sub x y).value.toReal? =
      some (x - y) := by
  rw [fmt.ieeeRoundToNearestEvenOpResult_sub_eq_finiteNoFlags_of_fergusonMagnitudeExponentConditionLe
    hcond hnoUnderflow]
  exact IeeeOperationResult.finiteNoFlags_toReal? _
/-- Compatibility IEEE theorem for the older representation-form inclusive
Ferguson condition. -/
theorem ieeeRoundToNearestEvenOpResult_sub_eq_finiteNoFlags_of_fergusonConditionLe
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonExponentConditionLe x y) :
    fmt.ieeeRoundToNearestEvenOpResult BasicOp.sub x y =
      IeeeOperationResult.finiteNoFlags (x - y) := by
  have hnormal :
      fmt.finiteNormalRange (BasicOp.exact BasicOp.sub x y) := by
    simpa [BasicOp.exact] using
      fmt.fergusonExponentConditionLe_sub_finiteNormalRange hcond
  have hbranch :=
    fmt.ieeeRoundToNearestEvenOpResult_eq_finiteNoFlags_of_finiteNormalRange
      (op := BasicOp.sub) (x := x) (y := y) hnormal
  rw [fmt.finiteRoundToEvenOp_sub_eq_exact_of_fergusonConditionLe hcond] at hbranch
  exact hbranch
theorem ieeeRoundToNearestEvenOpResult_sub_noFlags_of_fergusonConditionLe
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonExponentConditionLe x y) :
    (fmt.ieeeRoundToNearestEvenOpResult BasicOp.sub x y).noFlags := by
  rw [fmt.ieeeRoundToNearestEvenOpResult_sub_eq_finiteNoFlags_of_fergusonConditionLe
    hcond]
  exact IeeeOperationResult.finiteNoFlags_noFlags _
theorem ieeeRoundToNearestEvenOpResult_sub_toReal?_of_fergusonConditionLe
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonExponentConditionLe x y) :
    (fmt.ieeeRoundToNearestEvenOpResult BasicOp.sub x y).value.toReal? =
      some (x - y) := by
  rw [fmt.ieeeRoundToNearestEvenOpResult_sub_eq_finiteNoFlags_of_fergusonConditionLe
    hcond]
  exact IeeeOperationResult.finiteNoFlags_toReal? _
/-- In the two-exponent one-digit decimal audit format, `1 + 90` overflows the
finite range and saturates to the maximum finite value `90`. -/
theorem decimalSingleDigitTwoExponentFormat_round_add_one_ninety :
    decimalSingleDigitTwoExponentFormat.finiteRoundToEvenOp BasicOp.add
      (1 : ℝ) 90 = 90 := by
  have hround :
      decimalSingleDigitTwoExponentFormat.nearestRoundingToFinite
        (BasicOp.exact BasicOp.add (1 : ℝ) 90)
        (decimalSingleDigitTwoExponentFormat.finiteRoundToEvenOp
          BasicOp.add (1 : ℝ) 90) := by
    exact
      decimalSingleDigitTwoExponentFormat.finiteRoundToEvenOp_nearestRoundingToFinite
        BasicOp.add (1 : ℝ) 90
  have hgt :
      decimalSingleDigitTwoExponentFormat.maxFiniteMagnitude <
        BasicOp.exact BasicOp.add (1 : ℝ) 90 := by
    norm_num [decimalSingleDigitTwoExponentFormat, maxFiniteMagnitude, betaR,
      BasicOp.exact]
    change (90 : ℝ) < 91
    norm_num
  have hmax :=
    nearestRoundingToFinite_eq_maxFiniteMagnitude_of_gt_maxFiniteMagnitude
      hround hgt
  norm_num [decimalSingleDigitTwoExponentFormat, maxFiniteMagnitude, betaR] at hmax
  exact hmax
/-- Positive finite operand plus a negative finite operand is exact under
Sterbenz's ratio condition on the positive magnitudes. -/
theorem finiteRoundToEvenOp_add_pos_neg_finiteSystemWithSign_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystemWithSign false x)
    (hy : fmt.finiteSystemWithSign true y)
    (hsterbenz : fmt.sterbenzRatioCondition x (-y)) :
    fmt.finiteRoundToEvenOp BasicOp.add x y = x + y := by
  have hxfin : fmt.finiteSystem x :=
    fmt.finiteSystem_of_finiteSystemWithSign hx
  have hyfin : fmt.finiteSystem y :=
    fmt.finiteSystem_of_finiteSystemWithSign hy
  have hneg_y_fin : fmt.finiteSystem (-y) :=
    fmt.finiteSystem_neg hyfin
  simpa using
    (fmt.finiteRoundToEvenOp_add_neg_right_finiteSystem_eq_exact_of_sterbenzRatioCondition
      (x := x) (y := -y) hxfin hneg_y_fin hsterbenz)
theorem finiteRoundToEvenOp_add_pos_neg_finiteSystemWithSign_error_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystemWithSign false x)
    (hy : fmt.finiteSystemWithSign true y)
    (hsterbenz : fmt.sterbenzRatioCondition x (-y)) :
    fmt.finiteSystem
      ((x + y) - fmt.finiteRoundToEvenOp BasicOp.add x y) := by
  have hxfin : fmt.finiteSystem x :=
    fmt.finiteSystem_of_finiteSystemWithSign hx
  have hyfin : fmt.finiteSystem y :=
    fmt.finiteSystem_of_finiteSystemWithSign hy
  have hneg_y_fin : fmt.finiteSystem (-y) :=
    fmt.finiteSystem_neg hyfin
  simpa using
    (fmt.finiteRoundToEvenOp_add_neg_right_finiteSystem_error_finiteSystem_of_sterbenzRatioCondition
      (x := x) (y := -y) hxfin hneg_y_fin hsterbenz)
/-- Negative finite operand plus a positive finite operand is exact under
Sterbenz's ratio condition on the positive magnitudes. -/
theorem finiteRoundToEvenOp_add_neg_pos_finiteSystemWithSign_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystemWithSign true x)
    (hy : fmt.finiteSystemWithSign false y)
    (hsterbenz : fmt.sterbenzRatioCondition y (-x)) :
    fmt.finiteRoundToEvenOp BasicOp.add x y = x + y := by
  have hxfin : fmt.finiteSystem x :=
    fmt.finiteSystem_of_finiteSystemWithSign hx
  have hyfin : fmt.finiteSystem y :=
    fmt.finiteSystem_of_finiteSystemWithSign hy
  have hneg_x_fin : fmt.finiteSystem (-x) :=
    fmt.finiteSystem_neg hxfin
  simpa using
    (fmt.finiteRoundToEvenOp_add_neg_left_finiteSystem_eq_exact_of_sterbenzRatioCondition
      (x := y) (y := -x) hyfin hneg_x_fin hsterbenz)
theorem finiteRoundToEvenOp_add_neg_pos_finiteSystemWithSign_error_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystemWithSign true x)
    (hy : fmt.finiteSystemWithSign false y)
    (hsterbenz : fmt.sterbenzRatioCondition y (-x)) :
    fmt.finiteSystem
      ((x + y) - fmt.finiteRoundToEvenOp BasicOp.add x y) := by
  have hxfin : fmt.finiteSystem x :=
    fmt.finiteSystem_of_finiteSystemWithSign hx
  have hyfin : fmt.finiteSystem y :=
    fmt.finiteSystem_of_finiteSystemWithSign hy
  have hneg_x_fin : fmt.finiteSystem (-x) :=
    fmt.finiteSystem_neg hxfin
  simpa [add_comm] using
    (fmt.finiteRoundToEvenOp_add_neg_left_finiteSystem_error_finiteSystem_of_sterbenzRatioCondition
      (x := y) (y := -x) hyfin hneg_x_fin hsterbenz)
/-- Positive finite operand plus a negative finite operand is exact in the
near-magnitude branch `x < 2*(-y)`: the inequalities imply the Sterbenz ratio
condition on the positive magnitudes. -/
theorem finiteRoundToEvenOp_add_pos_neg_finiteSystemWithSign_eq_exact_of_magnitude_lt_two
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystemWithSign false x)
    (hy : fmt.finiteSystemWithSign true y)
    (hmag : -y < x)
    (hlt_two : x < 2 * (-y)) :
    fmt.finiteRoundToEvenOp BasicOp.add x y = x + y := by
  have hneg_y_pos : 0 < -y := by
    linarith
  have hsterbenz : fmt.sterbenzRatioCondition x (-y) := by
    constructor <;> linarith
  exact
    fmt.finiteRoundToEvenOp_add_pos_neg_finiteSystemWithSign_eq_exact_of_sterbenzRatioCondition
      hx hy hsterbenz
/-- Positive finite operand plus a negative finite operand has a finite local
roundoff error in the near-magnitude branch because that branch is exact. -/
theorem finiteRoundToEvenOp_add_pos_neg_finiteSystemWithSign_error_finiteSystem_of_magnitude_lt_two
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystemWithSign false x)
    (hy : fmt.finiteSystemWithSign true y)
    (hmag : -y < x)
    (hlt_two : x < 2 * (-y)) :
    fmt.finiteSystem
      ((x + y) - fmt.finiteRoundToEvenOp BasicOp.add x y) := by
  have hneg_y_pos : 0 < -y := by
    linarith
  have hsterbenz : fmt.sterbenzRatioCondition x (-y) := by
    constructor <;> linarith
  exact
    fmt.finiteRoundToEvenOp_add_pos_neg_finiteSystemWithSign_error_finiteSystem_of_sterbenzRatioCondition
      hx hy hsterbenz
/-- If a positive finite operand plus a negative finite operand rounds
inexactly, then the near-magnitude branch `x < 2*(-y)` is impossible. -/
theorem finiteRoundToEvenOp_add_pos_neg_finiteSystemWithSign_not_lt_two_of_ne_exact
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystemWithSign false x)
    (hy : fmt.finiteSystemWithSign true y)
    (hinexact : fmt.finiteRoundToEvenOp BasicOp.add x y ≠ x + y)
    (hmag : -y < x) :
    ¬ x < 2 * (-y) := by
  intro hlt_two
  exact hinexact
    (fmt.finiteRoundToEvenOp_add_pos_neg_finiteSystemWithSign_eq_exact_of_magnitude_lt_two
      hx hy hmag hlt_two)
/-- Negative finite operand plus a positive finite operand is exact in the
near-magnitude branch `y < 2*(-x)`: the inequalities imply the Sterbenz ratio
condition on the positive magnitudes. -/
theorem finiteRoundToEvenOp_add_neg_pos_finiteSystemWithSign_eq_exact_of_magnitude_lt_two
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystemWithSign true x)
    (hy : fmt.finiteSystemWithSign false y)
    (hmag : -x < y)
    (hlt_two : y < 2 * (-x)) :
    fmt.finiteRoundToEvenOp BasicOp.add x y = x + y := by
  have hneg_x_pos : 0 < -x := by
    linarith
  have hsterbenz : fmt.sterbenzRatioCondition y (-x) := by
    constructor <;> linarith
  exact
    fmt.finiteRoundToEvenOp_add_neg_pos_finiteSystemWithSign_eq_exact_of_sterbenzRatioCondition
      hx hy hsterbenz
/-- Negative finite operand plus a positive finite operand has a finite local
roundoff error in the near-magnitude branch because that branch is exact. -/
theorem finiteRoundToEvenOp_add_neg_pos_finiteSystemWithSign_error_finiteSystem_of_magnitude_lt_two
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystemWithSign true x)
    (hy : fmt.finiteSystemWithSign false y)
    (hmag : -x < y)
    (hlt_two : y < 2 * (-x)) :
    fmt.finiteSystem
      ((x + y) - fmt.finiteRoundToEvenOp BasicOp.add x y) := by
  have hneg_x_pos : 0 < -x := by
    linarith
  have hsterbenz : fmt.sterbenzRatioCondition y (-x) := by
    constructor <;> linarith
  exact
    fmt.finiteRoundToEvenOp_add_neg_pos_finiteSystemWithSign_error_finiteSystem_of_sterbenzRatioCondition
      hx hy hsterbenz
/-- If a negative finite operand plus a positive finite operand rounds
inexactly, then the near-magnitude branch `y < 2*(-x)` is impossible. -/
theorem finiteRoundToEvenOp_add_neg_pos_finiteSystemWithSign_not_lt_two_of_ne_exact
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystemWithSign true x)
    (hy : fmt.finiteSystemWithSign false y)
    (hinexact : fmt.finiteRoundToEvenOp BasicOp.add x y ≠ x + y)
    (hmag : -x < y) :
    ¬ y < 2 * (-x) := by
  intro hlt_two
  exact hinexact
    (fmt.finiteRoundToEvenOp_add_neg_pos_finiteSystemWithSign_eq_exact_of_magnitude_lt_two
      hx hy hmag hlt_two)
/-- Source-facing near-magnitude exactness for a nonnegative finite operand
plus a nonpositive finite operand.

This is the ordinary finite-system wrapper around the sign-witnessed
opposite-sign exact branch. -/
theorem finiteRoundToEvenOp_add_pos_neg_finiteSystem_eq_exact_of_magnitude_lt_two
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x) (hy : fmt.finiteSystem y)
    (hx_nonneg : 0 ≤ x) (hy_nonpos : y ≤ 0)
    (hmag : -y < x)
    (hlt_two : x < 2 * (-y)) :
    fmt.finiteRoundToEvenOp BasicOp.add x y = x + y := by
  have hxsgn : fmt.finiteSystemWithSign false x :=
    fmt.finiteSystemWithSign_false_of_finiteSystem_of_nonneg hx hx_nonneg
  have hysgn : fmt.finiteSystemWithSign true y :=
    fmt.finiteSystemWithSign_true_of_finiteSystem_of_nonpos hy hy_nonpos
  exact
    fmt.finiteRoundToEvenOp_add_pos_neg_finiteSystemWithSign_eq_exact_of_magnitude_lt_two
      hxsgn hysgn hmag hlt_two
/-- If a nonnegative finite operand plus a nonpositive finite operand rounds
inexactly, then the source near-magnitude branch `x < 2*(-y)` is impossible. -/
theorem finiteRoundToEvenOp_add_pos_neg_finiteSystem_not_lt_two_of_ne_exact
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x) (hy : fmt.finiteSystem y)
    (hx_nonneg : 0 ≤ x) (hy_nonpos : y ≤ 0)
    (hinexact : fmt.finiteRoundToEvenOp BasicOp.add x y ≠ x + y)
    (hmag : -y < x) :
    ¬ x < 2 * (-y) := by
  intro hlt_two
  exact hinexact
    (fmt.finiteRoundToEvenOp_add_pos_neg_finiteSystem_eq_exact_of_magnitude_lt_two
      hx hy hx_nonneg hy_nonpos hmag hlt_two)
/-- Source-facing near-magnitude exactness for a nonpositive finite operand
plus a nonnegative finite operand.

This is the ordinary finite-system wrapper around the sign-witnessed
opposite-sign exact branch. -/
theorem finiteRoundToEvenOp_add_neg_pos_finiteSystem_eq_exact_of_magnitude_lt_two
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x) (hy : fmt.finiteSystem y)
    (hx_nonpos : x ≤ 0) (hy_nonneg : 0 ≤ y)
    (hmag : -x < y)
    (hlt_two : y < 2 * (-x)) :
    fmt.finiteRoundToEvenOp BasicOp.add x y = x + y := by
  have hxsgn : fmt.finiteSystemWithSign true x :=
    fmt.finiteSystemWithSign_true_of_finiteSystem_of_nonpos hx hx_nonpos
  have hysgn : fmt.finiteSystemWithSign false y :=
    fmt.finiteSystemWithSign_false_of_finiteSystem_of_nonneg hy hy_nonneg
  exact
    fmt.finiteRoundToEvenOp_add_neg_pos_finiteSystemWithSign_eq_exact_of_magnitude_lt_two
      hxsgn hysgn hmag hlt_two
/-- If a nonpositive finite operand plus a nonnegative finite operand rounds
inexactly, then the source near-magnitude branch `y < 2*(-x)` is impossible. -/
theorem finiteRoundToEvenOp_add_neg_pos_finiteSystem_not_lt_two_of_ne_exact
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x) (hy : fmt.finiteSystem y)
    (hx_nonpos : x ≤ 0) (hy_nonneg : 0 ≤ y)
    (hinexact : fmt.finiteRoundToEvenOp BasicOp.add x y ≠ x + y)
    (hmag : -x < y) :
    ¬ y < 2 * (-x) := by
  intro hlt_two
  exact hinexact
    (fmt.finiteRoundToEvenOp_add_neg_pos_finiteSystem_eq_exact_of_magnitude_lt_two
      hx hy hx_nonpos hy_nonneg hmag hlt_two)

end FloatingPointFormat

end

end NumStability
