import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import NumStability.Analysis.Error.Measures.ScalarDefinitions
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.IeeeValue
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.FloatingPointArithmetic.Rounding

namespace NumStability

/-!
# RoundToEvenLocalError

Extracted without change from FloatingPointArithmetic.
-/

noncomputable section

namespace FloatingPointFormat

theorem finiteRoundToModeOp_nearestEven
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    fmt.finiteRoundToModeOp IeeeRoundingMode.nearestEven op x y =
      fmt.finiteRoundToEvenOp op x y := rfl
theorem finiteRoundToMode_ieeeUnderflowModeRoundingEvidence_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.ieeeUnderflowModeRoundingEvidence mode x
      (fmt.finiteRoundToMode mode x) := by
  cases mode
  · simpa [finiteRoundToMode] using fmt.finiteRoundToEven_nearestRoundingToFinite x
  · constructor
    · rw [finiteRoundToMode_towardZero,
        fmt.finiteRoundTowardZero_eq_underflow hunder]
      exact fmt.finiteUnderflowRoundTowardZero_finiteSystem hunder
    · rw [finiteRoundToMode_towardZero]
      exact fmt.finiteRoundTowardZero_abs_le_abs_of_finiteUnderflowRange
        hunder
  · constructor
    · rw [finiteRoundToMode_towardPositive,
        fmt.finiteRoundTowardPositive_eq_underflow hunder]
      exact fmt.finiteUnderflowRoundTowardPositive_finiteSystem hunder
    · rw [finiteRoundToMode_towardPositive]
      exact fmt.le_finiteRoundTowardPositive_of_finiteUnderflowRange
        hunder
  · constructor
    · rw [finiteRoundToMode_towardNegative,
        fmt.finiteRoundTowardNegative_eq_underflow hunder]
      exact fmt.finiteUnderflowRoundTowardNegative_finiteSystem hunder
    · rw [finiteRoundToMode_towardNegative]
      exact fmt.finiteRoundTowardNegative_le_of_finiteUnderflowRange
        hunder
theorem finiteRoundToModeOp_ieeeUnderflowModeRoundingEvidence_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteUnderflowRange (BasicOp.exact op x y)) :
    fmt.ieeeUnderflowModeRoundingEvidence mode (BasicOp.exact op x y)
      (fmt.finiteRoundToModeOp mode op x y) := by
  simpa [finiteRoundToModeOp] using
    fmt.finiteRoundToMode_ieeeUnderflowModeRoundingEvidence_of_finiteUnderflowRange
      (mode := mode) hxy
theorem finiteRoundToEvenOp_nearestRoundingToFinite
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    fmt.nearestRoundingToFinite (BasicOp.exact op x y)
      (fmt.finiteRoundToEvenOp op x y) := by
  simpa [finiteRoundToEvenOp] using
    fmt.finiteRoundToEven_nearestRoundingToFinite (BasicOp.exact op x y)
/-- Higham Problem 4.6 / Shewchuk: for correctly rounded addition, the local
error is no larger than the smaller input magnitude.

The proof is just nearest-rounding minimality: both operands are themselves
finite representable candidates for the exact sum `a + b`, so the rounded
result is at least as close to `a + b` as either candidate. -/
theorem nearestRoundingToFinite_add_abs_error_le_min_of_finiteSystem
    (fmt : FloatingPointFormat) {a b s : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hround : fmt.nearestRoundingToFinite (a + b) s) :
    |(a + b) - s| ≤ min |a| |b| := by
  have hle_a_candidate : |(a + b) - s| ≤ |(a + b) - a| :=
    nearestRoundingIn_minimal hround ha
  have hle_b_candidate : |(a + b) - s| ≤ |(a + b) - b| :=
    nearestRoundingIn_minimal hround hb
  have hle_b : |(a + b) - s| ≤ |b| := by
    have hdist : (a + b) - a = b := by ring
    simpa [hdist] using hle_a_candidate
  have hle_a : |(a + b) - s| ≤ |a| := by
    have hdist : (a + b) - b = a := by ring
    simpa [hdist] using hle_b_candidate
  exact le_min hle_a hle_b
/-- Higham Problem 4.6 / Shewchuk, specialized to the finite round-to-even
addition selector. -/
theorem finiteRoundToEvenOp_add_abs_error_le_min_of_finiteSystem
    (fmt : FloatingPointFormat) {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b) :
    |(a + b) - fmt.finiteRoundToEvenOp BasicOp.add a b| ≤ min |a| |b| := by
  exact
    fmt.nearestRoundingToFinite_add_abs_error_le_min_of_finiteSystem ha hb
      (by
        simpa [BasicOp.exact] using
          fmt.finiteRoundToEvenOp_nearestRoundingToFinite BasicOp.add a b)
/-- The finite round-to-even primitive-operation wrapper returns a finite
representable value. -/
theorem finiteRoundToEvenOp_finiteSystem
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    fmt.finiteSystem (fmt.finiteRoundToEvenOp op x y) := by
  simpa [finiteRoundToEvenOp] using
    fmt.finiteRoundToEven_finiteSystem (BasicOp.exact op x y)
/-- If the exact primitive operation result is finite representable, the
finite round-to-even operation wrapper returns it exactly. -/
theorem finiteRoundToEvenOp_eq_exact_of_finiteSystem
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteSystem (BasicOp.exact op x y)) :
    fmt.finiteRoundToEvenOp op x y = BasicOp.exact op x y := by
  simpa [finiteRoundToEvenOp] using
    fmt.finiteRoundToEven_eq_self_of_finiteSystem hxy
/-- Nearest finite round-to-even addition by a nonnegative quantity cannot
return a value below the finite left input.

The proof uses nearestness with the finite left input as a candidate for the
exact sum. -/
theorem finiteRoundToEvenOp_add_ge_left_of_finiteSystem_of_nonneg
    {fmt : FloatingPointFormat} {s t : ℝ}
    (hs : fmt.finiteSystem s) (ht : 0 ≤ t) :
    s ≤ fmt.finiteRoundToEvenOp BasicOp.add s t := by
  let x : ℝ := BasicOp.exact BasicOp.add s t
  let y : ℝ := fmt.finiteRoundToEvenOp BasicOp.add s t
  have hround : fmt.nearestRoundingToFinite x y := by
    simpa [x, y] using
      fmt.finiteRoundToEvenOp_nearestRoundingToFinite BasicOp.add s t
  by_contra hnot
  have hylt : y < s := lt_of_not_ge hnot
  have hsx : s ≤ x := by
    simp [x, BasicOp.exact]
    exact ht
  have hyx : y < x := lt_of_lt_of_le hylt hsx
  have hnear := nearestRoundingIn_minimal hround hs
  have hxy_nonneg : 0 ≤ x - y := by linarith
  have hxs_nonneg : 0 ≤ x - s := by linarith
  rw [abs_of_nonneg hxy_nonneg, abs_of_nonneg hxs_nonneg] at hnear
  linarith
/-- Nearest finite round-to-even addition cannot return above a finite
candidate that is already above the exact sum. -/
theorem finiteRoundToEvenOp_add_le_of_exact_le_finiteSystem
    {fmt : FloatingPointFormat} {s t c : ℝ}
    (hc : fmt.finiteSystem c)
    (hxc : s + t ≤ c) :
    fmt.finiteRoundToEvenOp BasicOp.add s t ≤ c := by
  let x : ℝ := BasicOp.exact BasicOp.add s t
  let y : ℝ := fmt.finiteRoundToEvenOp BasicOp.add s t
  have hround : fmt.nearestRoundingToFinite x y := by
    simpa [x, y] using
      fmt.finiteRoundToEvenOp_nearestRoundingToFinite BasicOp.add s t
  by_contra hnot
  have hcy : c < y := lt_of_not_ge hnot
  have hxc' : x ≤ c := by
    simpa [x, BasicOp.exact] using hxc
  have hxy : x < y := lt_of_le_of_lt hxc' hcy
  have hnear := nearestRoundingIn_minimal hround hc
  have hxy_nonneg : 0 ≤ y - x := by linarith
  have hxc_nonneg : 0 ≤ c - x := by linarith
  rw [abs_sub_comm x y, abs_of_nonneg hxy_nonneg,
      abs_sub_comm x c, abs_of_nonneg hxc_nonneg] at hnear
  linarith
/-- Nearest finite round-to-even addition cannot return below a finite
candidate that is already below the exact sum. -/
theorem finiteRoundToEvenOp_add_ge_of_finiteSystem_le_exact
    {fmt : FloatingPointFormat} {s t c : ℝ}
    (hc : fmt.finiteSystem c)
    (hcx : c ≤ s + t) :
    c ≤ fmt.finiteRoundToEvenOp BasicOp.add s t := by
  let x : ℝ := BasicOp.exact BasicOp.add s t
  let y : ℝ := fmt.finiteRoundToEvenOp BasicOp.add s t
  have hround : fmt.nearestRoundingToFinite x y := by
    simpa [x, y] using
      fmt.finiteRoundToEvenOp_nearestRoundingToFinite BasicOp.add s t
  by_contra hnot
  have hyc : y < c := lt_of_not_ge hnot
  have hcx' : c ≤ x := by
    simpa [x, BasicOp.exact] using hcx
  have hyx : y < x := lt_of_lt_of_le hyc hcx'
  have hnear := nearestRoundingIn_minimal hround hc
  have hxy_nonneg : 0 ≤ x - y := by linarith
  have hxc_nonneg : 0 ≤ x - c := by linarith
  rw [abs_of_nonneg hxy_nonneg, abs_of_nonneg hxc_nonneg] at hnear
  linarith
/-- Two finite candidates bracketing the exact addition result also bracket the
nearest finite round-to-even addition result. -/
theorem finiteRoundToEvenOp_add_mem_Icc_of_finiteSystem_bounds
    {fmt : FloatingPointFormat} {s t lo hi : ℝ}
    (hlo : fmt.finiteSystem lo) (hhi : fmt.finiteSystem hi)
    (hlo_exact : lo ≤ s + t) (hexact_hi : s + t ≤ hi) :
    lo ≤ fmt.finiteRoundToEvenOp BasicOp.add s t ∧
      fmt.finiteRoundToEvenOp BasicOp.add s t ≤ hi :=
  ⟨fmt.finiteRoundToEvenOp_add_ge_of_finiteSystem_le_exact hlo hlo_exact,
    fmt.finiteRoundToEvenOp_add_le_of_exact_le_finiteSystem hhi hexact_hi⟩
/-- Nearest finite round-to-even addition by a nonnegative quantity has
absolute rounding error no larger than that quantity, when the left input is
finite. -/
theorem finiteRoundToEvenOp_add_abs_error_le_right_of_finiteSystem_of_nonneg
    {fmt : FloatingPointFormat} {s t : ℝ}
    (hs : fmt.finiteSystem s) (ht : 0 ≤ t) :
    |fmt.finiteRoundToEvenOp BasicOp.add s t - (s + t)| ≤ t := by
  let x : ℝ := BasicOp.exact BasicOp.add s t
  let y : ℝ := fmt.finiteRoundToEvenOp BasicOp.add s t
  have hround : fmt.nearestRoundingToFinite x y := by
    simpa [x, y] using
      fmt.finiteRoundToEvenOp_nearestRoundingToFinite BasicOp.add s t
  have hnear := nearestRoundingIn_minimal hround hs
  have hxs : |x - s| = t := by
    rw [abs_of_nonneg]
    · simp [x, BasicOp.exact]
    · simp [x, BasicOp.exact]
      exact ht
  have hxy : |x - y| ≤ t := by
    simpa [hxs] using hnear
  simpa [x, y, BasicOp.exact, abs_sub_comm] using hxy
/-- Consequence of the one-step nearestness bound: a rounded nonnegative
addition can increase a finite left input by at most twice the added quantity. -/
theorem finiteRoundToEvenOp_add_le_left_add_two_mul_right_of_finiteSystem_of_nonneg
    {fmt : FloatingPointFormat} {s t : ℝ}
    (hs : fmt.finiteSystem s) (ht : 0 ≤ t) :
    fmt.finiteRoundToEvenOp BasicOp.add s t ≤ s + 2 * t := by
  have herr :=
    fmt.finiteRoundToEvenOp_add_abs_error_le_right_of_finiteSystem_of_nonneg
      hs ht
  have hle_abs :
      fmt.finiteRoundToEvenOp BasicOp.add s t - (s + t) ≤
        |fmt.finiteRoundToEvenOp BasicOp.add s t - (s + t)| :=
    le_abs_self _
  linarith
/-- Exact-add branch for aligned same-sign normalized operands whose source
coefficient already fits in `t` digits. -/
theorem finiteRoundToEvenOp_add_sameSign_sameExponent_eq_exact_of_add_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hadd : m + n < fmt.beta ^ fmt.t) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue negative m e)
        (fmt.normalizedValue negative n e) =
      fmt.normalizedValue negative m e +
        fmt.normalizedValue negative n e := by
  exact
    fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue negative m e)
      (y := fmt.normalizedValue negative n e)
      (fmt.normalizedValue_add_sameSign_sameExponent_finiteSystem_of_add_lt_mantissaBound
        (negative := negative) (m := m) (n := n) (e := e) he hadd)
/-- Exact-add branch for same-sign normalized operands with ordered exponents
whose aligned lower-lattice coefficient already fits in `t` digits. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_eq_exact_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ fmt.t) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue negative mHigh eHigh)
        (fmt.normalizedValue negative mLow eLow) =
      fmt.normalizedValue negative mHigh eHigh +
        fmt.normalizedValue negative mLow eLow := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) :=
    fmt.normalizedValue_add_sameSign_orderedExponent_finiteSystem_of_alignedCoeff_lt_mantissaBound
      (negative := negative) hmHigh hmLow heHigh heLow hle hcoeff
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue negative mHigh eHigh)
      (y := fmt.normalizedValue negative mLow eLow) hfin)
/-- The ordered-exponent exact normalized-add branch has zero local roundoff
error. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  rw [
    finiteRoundToEvenOp_add_sameSign_orderedExponent_eq_exact_of_alignedCoeff_lt_mantissaBound
      hmHigh hmLow heHigh heLow hle hcoeff]
  simpa using fmt.finiteSystem_zero
/-- Commuted exact-add branch for same-sign normalized operands with ordered
exponents whose aligned lower-lattice coefficient already fits in `t` digits. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_eq_exact_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ fmt.t) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue negative mLow eLow)
        (fmt.normalizedValue negative mHigh eHigh) =
      fmt.normalizedValue negative mLow eLow +
        fmt.normalizedValue negative mHigh eHigh := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) :=
    fmt.normalizedValue_add_sameSign_orderedExponent_finiteSystem_of_alignedCoeff_lt_mantissaBound
      (negative := negative) hmHigh hmLow heHigh heLow hle hcoeff
  have hfin_comm :
      fmt.finiteSystem
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) := by
    convert hfin using 1
    ring
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue negative mLow eLow)
      (y := fmt.normalizedValue negative mHigh eHigh) hfin_comm)
/-- The commuted ordered-exponent exact normalized-add branch has zero local
roundoff error. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
  rw [
    finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_eq_exact_of_alignedCoeff_lt_mantissaBound
      hmHigh hmLow heHigh heLow hle hcoeff]
  simpa using fmt.finiteSystem_zero
/-- Positive high normalized operand plus negative lower normalized operand is
itself finite representable when the aligned difference coefficient fits in
`t` radix digits. -/
theorem normalizedValue_add_positive_neg_orderedExponent_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (_hmHigh : fmt.normalizedMantissa mHigh)
    (_hmLow : fmt.normalizedMantissa mLow)
    (_heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hcoeff :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      (fmt.normalizedValue false mHigh eHigh +
        fmt.normalizedValue true mLow eLow) := by
  let shift := Int.toNat (eHigh - eLow)
  let k : ℕ := mHigh * fmt.beta ^ shift - mLow
  have hshift_cast : ((shift : ℕ) : ℤ) = eHigh - eLow := by
    have hnonneg : 0 ≤ eHigh - eLow := sub_nonneg.mpr hle
    simpa [shift] using Int.toNat_of_nonneg hnonneg
  have hshift_endpoint : eHigh - (shift : ℤ) = eLow := by
    omega
  have hcoeff_le' : mLow ≤ mHigh * fmt.beta ^ shift := by
    simpa [shift] using hcoeff_le
  have hcoeff' : k < fmt.beta ^ fmt.t := by
    simpa [k, shift] using hcoeff
  have hshift :
      fmt.normalizedValue false (mHigh * fmt.beta ^ shift) eLow =
        fmt.normalizedValue false mHigh eHigh := by
    have h :=
      fmt.normalizedValue_mul_beta_pow_subExponent_eq
        (negative := false) (m := mHigh) (shift := shift) (e := eHigh)
    rw [hshift_endpoint] at h
    exact h
  have hsource :
      fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow =
        ((k : ℕ) : ℝ) * fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
    rw [← hshift, fmt.normalizedValue_true_eq_neg_false]
    simp [k, normalizedValue, signValue, Nat.cast_sub hcoeff_le',
      Nat.cast_mul, Nat.cast_pow]
    ring
  have hscaled :
      fmt.finiteSystem
        (((k : ℤ) : ℝ) * fmt.betaR ^ (eLow - (fmt.t : ℤ))) := by
    have hk : ((k : ℤ).natAbs) < fmt.beta ^ fmt.t := by
      simpa using hcoeff'
    simpa [signValue] using
      (fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
        (negative := false) (k := (k : ℤ)) (e := eLow) heLow hk)
  simpa [hsource] using hscaled
/-- Negative high normalized operand plus positive lower normalized operand is
finite representable in the small aligned-difference branch. -/
theorem normalizedValue_add_negative_pos_orderedExponent_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (_hmHigh : fmt.normalizedMantissa mHigh)
    (_hmLow : fmt.normalizedMantissa mLow)
    (_heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hcoeff :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      (fmt.normalizedValue true mHigh eHigh +
        fmt.normalizedValue false mLow eLow) := by
  let shift := Int.toNat (eHigh - eLow)
  let k : ℕ := mHigh * fmt.beta ^ shift - mLow
  have hshift_cast : ((shift : ℕ) : ℤ) = eHigh - eLow := by
    have hnonneg : 0 ≤ eHigh - eLow := sub_nonneg.mpr hle
    simpa [shift] using Int.toNat_of_nonneg hnonneg
  have hshift_endpoint : eHigh - (shift : ℤ) = eLow := by
    omega
  have hcoeff_le' : mLow ≤ mHigh * fmt.beta ^ shift := by
    simpa [shift] using hcoeff_le
  have hcoeff' : k < fmt.beta ^ fmt.t := by
    simpa [k, shift] using hcoeff
  have hshift :
      fmt.normalizedValue true (mHigh * fmt.beta ^ shift) eLow =
        fmt.normalizedValue true mHigh eHigh := by
    have h :=
      fmt.normalizedValue_mul_beta_pow_subExponent_eq
        (negative := true) (m := mHigh) (shift := shift) (e := eHigh)
    rw [hshift_endpoint] at h
    exact h
  have hsource :
      fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow =
        fmt.signValue true * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
    rw [← hshift]
    simp [k, normalizedValue, signValue, Nat.cast_sub hcoeff_le',
      Nat.cast_mul, Nat.cast_pow]
    ring
  have hscaled :
      fmt.finiteSystem
        (fmt.signValue true * ((k : ℤ) : ℝ) *
          fmt.betaR ^ (eLow - (fmt.t : ℤ))) := by
    have hk : ((k : ℤ).natAbs) < fmt.beta ^ fmt.t := by
      simpa using hcoeff'
    simpa using
      (fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
        (negative := true) (k := (k : ℤ)) (e := eLow) heLow hk)
  simpa [hsource] using hscaled
/-- Positive high plus negative low ordered-exponent addition is exact for the
concrete finite round-to-even operation in the small aligned-difference branch.
-/
theorem finiteRoundToEvenOp_add_positive_neg_orderedExponent_eq_exact_of_alignedDiffCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hcoeff :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ fmt.t) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue false mHigh eHigh)
        (fmt.normalizedValue true mLow eLow) =
      fmt.normalizedValue false mHigh eHigh +
        fmt.normalizedValue true mLow eLow := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) :=
    fmt.normalizedValue_add_positive_neg_orderedExponent_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
      hmHigh hmLow heHigh heLow hle hcoeff_le hcoeff
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue false mHigh eHigh)
      (y := fmt.normalizedValue true mLow eLow) hfin)
/-- The positive-high/negative-low small aligned-difference branch has zero
local roundoff error. -/
theorem finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hcoeff :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  rw [
    fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_eq_exact_of_alignedDiffCoeff_lt_mantissaBound
      hmHigh hmLow heHigh heLow hle hcoeff_le hcoeff]
  simpa using fmt.finiteSystem_zero
/-- Negative high plus positive low ordered-exponent addition is exact for the
concrete finite round-to-even operation in the small aligned-difference branch.
-/
theorem finiteRoundToEvenOp_add_negative_pos_orderedExponent_eq_exact_of_alignedDiffCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hcoeff :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ fmt.t) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue true mHigh eHigh)
        (fmt.normalizedValue false mLow eLow) =
      fmt.normalizedValue true mHigh eHigh +
        fmt.normalizedValue false mLow eLow := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) :=
    fmt.normalizedValue_add_negative_pos_orderedExponent_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
      hmHigh hmLow heHigh heLow hle hcoeff_le hcoeff
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue true mHigh eHigh)
      (y := fmt.normalizedValue false mLow eLow) hfin)
/-- The negative-high/positive-low small aligned-difference branch has zero
local roundoff error. -/
theorem finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hcoeff :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  rw [
    fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_eq_exact_of_alignedDiffCoeff_lt_mantissaBound
      hmHigh hmLow heHigh heLow hle hcoeff_le hcoeff]
  simpa using fmt.finiteSystem_zero
theorem finiteRoundToEvenOp_eq_finiteNormalRoundToEven_of_finiteNormalRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    fmt.finiteRoundToEvenOp op x y =
      fmt.finiteNormalRoundToEven (BasicOp.exact op x y) hxy := by
  simpa [finiteRoundToEvenOp] using
    fmt.finiteRoundToEven_eq_finiteNormalRoundToEven_of_finiteNormalRange hxy
/-- Operation-level handoff for the finite-normal add branch.

If a source-level round-to-even witness for the exact sum has a finite local
error, uniqueness of the finite-normal round-to-even selector transfers that
finite-error certificate to the concrete `finiteRoundToEvenOp add` wrapper. -/
theorem finiteRoundToEvenOp_add_error_finite_of_sourceRoundToEvenEvidence
    {fmt : FloatingPointFormat} {a b y : ℝ}
    (hxy : fmt.finiteNormalRange (a + b))
    (hpolicy : fmt.sourceRoundToEvenEvidence (a + b) y)
    (herr : fmt.finiteSystem ((a + b) - y)) :
    fmt.finiteSystem
      ((a + b) - fmt.finiteRoundToEvenOp BasicOp.add a b) := by
  have hop :
      fmt.finiteRoundToEvenOp BasicOp.add a b =
        fmt.finiteNormalRoundToEven (a + b) hxy := by
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_finiteNormalRoundToEven_of_finiteNormalRange
        (op := BasicOp.add) (x := a) (y := b) hxy)
  have hround :
      fmt.finiteNormalRoundToEven (a + b) hxy = y :=
    fmt.finiteNormalRoundToEven_eq_of_sourceRoundToEvenEvidence hxy hpolicy
  rw [hop, hround]
  exact herr
/-- Operation-level aligned same-sign normalized addition has finite
representable local roundoff error in the finite-normal binary branch. -/
theorem finiteRoundToEvenOp_add_sameSign_sameExponent_error_finiteSystem
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {m n : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.normalizedMantissa n)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative m e +
          fmt.normalizedValue negative n e)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.normalizedValue negative n e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.normalizedValue negative n e)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative m e +
          fmt.normalizedValue negative n e)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.normalizedValue negative n e)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_sameExponent_error_finiteSystem
      hbeta he hm hn hpolicy
/-- Operation-level same-sign normalized ordered-exponent addition has finite
representable local roundoff error in the binary one-guard-word branch. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hlo :
      fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_guardCoeffBounds
      hbeta hmHigh hmLow heHigh heLow hle hlo hhi hpolicy
/-- Commuted operation-level same-sign normalized ordered-exponent addition has
finite representable local roundoff error in the binary one-guard-word branch. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hlo :
      fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue negative mHigh eHigh +
            fmt.normalizedValue negative mLow eLow) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.normalizedValue negative mLow eLow)
            (fmt.normalizedValue negative mHigh eHigh)) :=
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_guardCoeffBounds
      hbeta hmHigh hmLow heHigh heLow hle hlo hhi hpolicy
  convert hfin using 1
  ring
/-- Operation-level positive high plus negative low normalized ordered-exponent
addition has finite local error in the binary one-guard-word aligned-difference
branch. -/
theorem finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hlo :
      fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_guardCoeffBounds
      hbeta hmHigh hmLow heHigh heLow hle hcoeff_le hlo hhi hpolicy
/-- Operation-level negative high plus positive low normalized ordered-exponent
addition has finite local error in the binary one-guard-word aligned-difference
branch. -/
theorem finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hlo :
      fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_guardCoeffBounds
      hbeta hmHigh hmLow heHigh heLow hle hcoeff_le hlo hhi hpolicy
/-- Operation-level positive high plus negative low normalized ordered-exponent
addition has finite local error throughout the exact-or-one-guard aligned-
difference range `diffCoeff < 2*beta^t`. -/
theorem finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_two_mul_mantissaBound
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  by_cases hsmall :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ fmt.t
  · exact
      fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
        hmHigh hmLow heHigh heLow hle hcoeff_le hsmall
  · have hlo :
        fmt.beta ^ fmt.t ≤
          mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow :=
      le_of_not_gt hsmall
    exact
      fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_guardCoeffBounds
        hbeta hmHigh hmLow heHigh heLow hle hcoeff_le hlo hhi hxy
/-- Operation-level negative high plus positive low normalized ordered-exponent
addition has finite local error throughout the exact-or-one-guard aligned-
difference range `diffCoeff < 2*beta^t`. -/
theorem finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_two_mul_mantissaBound
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  by_cases hsmall :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ fmt.t
  · exact
      fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
        hmHigh hmLow heHigh heLow hle hcoeff_le hsmall
  · have hlo :
        fmt.beta ^ fmt.t ≤
          mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow :=
      le_of_not_gt hsmall
    exact
      fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_guardCoeffBounds
        hbeta hmHigh hmLow heHigh heLow hle hcoeff_le hlo hhi hxy
/-- Operation-level same-sign normalized ordered-exponent addition has finite
representable local roundoff error once a normalized multi-guard quotient
bracket for the aligned source coefficient is supplied.

This transfers the source-level multi-guard wrapper to the concrete finite
round-to-even add selector.  It is intentionally scoped to supplied quotient
endpoint hypotheses; the automatic complementary-region quotient dispatcher
remains a separate C4.4 dependency. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardNormalizedQuotient
    {fmt : FloatingPointFormat}
    {negative : Bool} {mHigh mLow q r d : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hdle : d ≤ fmt.t)
    (hk :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow =
        fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardNormalizedQuotient
      hmHigh hmLow heHigh heLow hle hdle hk hr hq hqs hpolicy
/-- Commuted operation-level same-sign normalized ordered-exponent addition has
finite representable local roundoff error once a normalized multi-guard
quotient bracket for the aligned source coefficient is supplied. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_multiGuardNormalizedQuotient
    {fmt : FloatingPointFormat}
    {negative : Bool} {mHigh mLow q r d : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hdle : d ≤ fmt.t)
    (hk :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow =
        fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue negative mHigh eHigh +
            fmt.normalizedValue negative mLow eLow) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.normalizedValue negative mLow eLow)
            (fmt.normalizedValue negative mHigh eHigh)) :=
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardNormalizedQuotient
      hmHigh hmLow heHigh heLow hle hdle hk hr hq hqs hpolicy
  convert hfin using 1
  ring
/-- Operation-level same-sign normalized ordered-exponent addition has finite
representable local roundoff error in the shifted exponent-boundary multi-guard
case. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardBoundary
    {fmt : FloatingPointFormat}
    {negative : Bool} {mHigh mLow r d : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hdle : d ≤ fmt.t)
    (hk :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow =
        fmt.beta ^ d * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta ^ d)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardBoundary
      hmHigh hmLow heHigh heLow hle hdle hk hr hpolicy
/-- Commuted operation-level same-sign normalized ordered-exponent addition has
finite representable local roundoff error in the shifted exponent-boundary
multi-guard case. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_multiGuardBoundary
    {fmt : FloatingPointFormat}
    {negative : Bool} {mHigh mLow r d : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hdle : d ≤ fmt.t)
    (hk :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow =
        fmt.beta ^ d * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta ^ d)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue negative mHigh eHigh +
            fmt.normalizedValue negative mLow eLow) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.normalizedValue negative mLow eLow)
            (fmt.normalizedValue negative mHigh eHigh)) :=
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardBoundary
      hmHigh hmLow heHigh heLow hle hdle hk hr hpolicy
  convert hfin using 1
  ring
/-- Operation-level same-sign normalized ordered-exponent addition has finite
representable local roundoff error from a supplied multi-guard scaled mantissa
range.  The internal dispatcher chooses the ordinary quotient branch or the
shifted boundary/carry branch. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardScaledMantissaRange
    {fmt : FloatingPointFormat}
    {negative : Bool} {mHigh mLow q r d : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hdle : d ≤ fmt.t)
    (hk :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow =
        fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d)
    (hlo :
      fmt.beta ^ d * fmt.minNormalMantissa ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ d * (fmt.maxNormalMantissa + 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardScaledMantissaRange
      hmHigh hmLow heHigh heLow hle hdle hk hr hlo hhi hpolicy
/-- Commuted operation-level same-sign normalized ordered-exponent addition has
finite representable local roundoff error from a supplied multi-guard scaled
mantissa range. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_multiGuardScaledMantissaRange
    {fmt : FloatingPointFormat}
    {negative : Bool} {mHigh mLow q r d : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hdle : d ≤ fmt.t)
    (hk :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow =
        fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d)
    (hlo :
      fmt.beta ^ d * fmt.minNormalMantissa ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ d * (fmt.maxNormalMantissa + 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue negative mHigh eHigh +
            fmt.normalizedValue negative mLow eLow) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.normalizedValue negative mLow eLow)
            (fmt.normalizedValue negative mHigh eHigh)) :=
      fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardScaledMantissaRange
      hmHigh hmLow heHigh heLow hle hdle hk hr hlo hhi hpolicy
  convert hfin using 1
  ring
/-- Operation-level same-sign normalized ordered-exponent addition has finite
representable local roundoff error from a supplied multi-guard scale and scaled
mantissa range.

The quotient and remainder for the scaled coefficient are derived internally,
leaving only the still-open C4.4 task of deriving the correct scale and range
from the raw aligned-coefficient inequalities. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardScaleRange
    {fmt : FloatingPointFormat}
    {negative : Bool} {mHigh mLow d : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hdle : d ≤ fmt.t)
    (hlo :
      fmt.beta ^ d * fmt.minNormalMantissa ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ d * (fmt.maxNormalMantissa + 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  let k : ℕ := mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow
  let q : ℕ := k / fmt.beta ^ d
  let r : ℕ := k % fmt.beta ^ d
  have hpow_pos : 0 < fmt.beta ^ d :=
    Nat.pow_pos (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hk :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow =
        fmt.beta ^ d * q + r := by
    change k = fmt.beta ^ d * (k / fmt.beta ^ d) + k % fmt.beta ^ d
    exact (Nat.div_add_mod k (fmt.beta ^ d)).symm
  have hr : r < fmt.beta ^ d := by
    rw [show r = k % fmt.beta ^ d by rfl]
    exact Nat.mod_lt k hpow_pos
  exact
    fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardScaledMantissaRange
      hmHigh hmLow heHigh heLow hle hdle hk hr hlo hhi hxy
/-- Operation-level same-sign normalized ordered-exponent addition has finite
representable local roundoff error from base-2 complementary coefficient
bounds.

This removes the explicit multi-guard scale from the theorem surface; callers
only provide the lower `2*beta^t` bound and a two-precision upper bound for the
aligned coefficient. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardCoefficientBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ (2 * fmt.t))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  rcases fmt.multiGuardScaleRange_exists_of_baseTwo_bounds hbeta hlo hhi with
    ⟨d, hdle, hrange_lo, hrange_hi⟩
  exact
    fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardScaleRange
      hmHigh hmLow heHigh heLow hle hdle hrange_lo hrange_hi hxy
/-- Concrete finite round-to-even positive high plus negative low wrapper for
the supplied aligned-difference multi-guard scale range. -/
theorem finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_multiGuardScaleRange
    {fmt : FloatingPointFormat}
    {mHigh mLow d : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hdle : d ≤ fmt.t)
    (hlo :
      fmt.beta ^ d * fmt.minNormalMantissa ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ d * (fmt.maxNormalMantissa + 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
        hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_multiGuardScaleRange
      hmHigh hmLow heHigh heLow hle hcoeff_le hdle hlo hhi hpolicy
/-- Concrete finite round-to-even negative high plus positive low wrapper for
the supplied aligned-difference multi-guard scale range. -/
theorem finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_multiGuardScaleRange
    {fmt : FloatingPointFormat}
    {mHigh mLow d : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hdle : d ≤ fmt.t)
    (hlo :
      fmt.beta ^ d * fmt.minNormalMantissa ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ d * (fmt.maxNormalMantissa + 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
        hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_multiGuardScaleRange
      hmHigh hmLow heHigh heLow hle hcoeff_le hdle hlo hhi hpolicy
/-- Concrete finite round-to-even positive high plus negative low wrapper for
the base-2 aligned-difference multi-guard coefficient range. -/
theorem finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_multiGuardCoefficientBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ (2 * fmt.t))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
        hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_multiGuardCoefficientBounds
      hbeta hmHigh hmLow heHigh heLow hle hcoeff_le hlo hhi hpolicy
/-- Concrete finite round-to-even negative high plus positive low wrapper for
the base-2 aligned-difference multi-guard coefficient range. -/
theorem finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_multiGuardCoefficientBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ (2 * fmt.t))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
        hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_multiGuardCoefficientBounds
      hbeta hmHigh hmLow heHigh heLow hle hcoeff_le hlo hhi hpolicy
/-- Concrete finite round-to-even positive high plus negative low wrapper for
the ordinary-cancellation complementary multi-guard region. -/
theorem finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_multiGuardComplementaryRegion
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow)
    (hwindow : eLow + (fmt.t : ℤ) > eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ (2 * fmt.t) :=
    fmt.alignedDiffCoeff_lt_two_precision_bound_of_normalizedMantissas_window
      hbeta hmHigh hmLow hle hwindow
  exact
    fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_multiGuardCoefficientBounds
      hbeta hmHigh hmLow heHigh heLow hle hcoeff_le hlo hhi hxy
/-- Concrete finite round-to-even negative high plus positive low wrapper for
the ordinary-cancellation complementary multi-guard region. -/
theorem finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_multiGuardComplementaryRegion
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow)
    (hwindow : eLow + (fmt.t : ℤ) > eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ (2 * fmt.t) :=
    fmt.alignedDiffCoeff_lt_two_precision_bound_of_normalizedMantissas_window
      hbeta hmHigh hmLow hle hwindow
  exact
    fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_multiGuardCoefficientBounds
      hbeta hmHigh hmLow heHigh heLow hle hcoeff_le hlo hhi hxy
/-- Operation-level same-sign normalized ordered-exponent addition has finite
representable local roundoff error in the complementary multi-guard region.

The exponent-window hypothesis supplies the two-precision upper bound for the
aligned coefficient; the lower complementary bound supplies the other side of
the logarithmic scale selection. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardComplementaryRegion
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow)
    (hwindow : eLow + (fmt.t : ℤ) > eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  have hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ (2 * fmt.t) :=
    fmt.alignedCoeff_lt_two_precision_bound_of_normalizedMantissas_window
      hbeta hmHigh hmLow hle hwindow
  exact
    fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardCoefficientBounds
      hbeta hmHigh hmLow heHigh heLow hle hlo hhi hxy
/-- Commuted operation-level same-sign normalized ordered-exponent addition has
finite representable local roundoff error from a supplied multi-guard scale and
scaled mantissa range, with quotient and remainder derived internally. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_multiGuardScaleRange
    {fmt : FloatingPointFormat}
    {negative : Bool} {mHigh mLow d : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hdle : d ≤ fmt.t)
    (hlo :
      fmt.beta ^ d * fmt.minNormalMantissa ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ d * (fmt.maxNormalMantissa + 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
  let k : ℕ := mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow
  let q : ℕ := k / fmt.beta ^ d
  let r : ℕ := k % fmt.beta ^ d
  have hpow_pos : 0 < fmt.beta ^ d :=
    Nat.pow_pos (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hk :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow =
        fmt.beta ^ d * q + r := by
    change k = fmt.beta ^ d * (k / fmt.beta ^ d) + k % fmt.beta ^ d
    exact (Nat.div_add_mod k (fmt.beta ^ d)).symm
  have hr : r < fmt.beta ^ d := by
    rw [show r = k % fmt.beta ^ d by rfl]
    exact Nat.mod_lt k hpow_pos
  exact
    fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_multiGuardScaledMantissaRange
      hmHigh hmLow heHigh heLow hle hdle hk hr hlo hhi hxy
/-- Commuted operation-level same-sign normalized ordered-exponent addition has
finite representable local roundoff error from base-2 complementary coefficient
bounds, with the multi-guard scale selected internally. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_multiGuardCoefficientBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ (2 * fmt.t))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
  rcases fmt.multiGuardScaleRange_exists_of_baseTwo_bounds hbeta hlo hhi with
    ⟨d, hdle, hrange_lo, hrange_hi⟩
  exact
    fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_multiGuardScaleRange
      hmHigh hmLow heHigh heLow hle hdle hrange_lo hrange_hi hxy
/-- Commuted operation-level same-sign normalized ordered-exponent addition has
finite representable local roundoff error in the complementary multi-guard
region. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_multiGuardComplementaryRegion
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow)
    (hwindow : eLow + (fmt.t : ℤ) > eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
  have hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ (2 * fmt.t) :=
    fmt.alignedCoeff_lt_two_precision_bound_of_normalizedMantissas_window
      hbeta hmHigh hmLow hle hwindow
  exact
    fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_multiGuardCoefficientBounds
      hbeta hmHigh hmLow heHigh heLow hle hlo hhi hxy
/-- Operation-level same-sign normalized ordered-exponent addition has finite
representable local roundoff error throughout the exact-or-one-guard range
`alignedCoeff < 2*beta^t`. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  by_cases hsmall :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ fmt.t
  · exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_mantissaBound
        hmHigh hmLow heHigh heLow hle hsmall
  · have hlo :
        fmt.beta ^ fmt.t ≤
          mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow :=
      le_of_not_gt hsmall
    exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_guardCoeffBounds
        hbeta hmHigh hmLow heHigh heLow hle hlo hhi hxy
/-- Commuted operation-level same-sign normalized ordered-exponent addition has
finite representable local roundoff error throughout the exact-or-one-guard
range `alignedCoeff < 2*beta^t`. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
  by_cases hsmall :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ fmt.t
  · exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_alignedCoeff_lt_mantissaBound
        hmHigh hmLow heHigh heLow hle hsmall
  · have hlo :
        fmt.beta ^ fmt.t ≤
          mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow :=
      le_of_not_gt hsmall
    exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_guardCoeffBounds
        hbeta hmHigh hmLow heHigh heLow hle hlo hhi hxy
/-- A normalized lower operand is strictly inside the left half-cell of a much
higher operand in base `2` once the exponent gap is larger than one precision
window.

This derives the low-cell hypothesis used by the large-alignment ordered-
exponent C4.4/FastTwoSum branches. -/
theorem normalizedValue_false_lt_half_ulpAtExponent_of_exponent_gap_gt_t
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {m : ℕ} {eLow eHigh : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hgap : eLow + (fmt.t : ℤ) < eHigh) :
    fmt.normalizedValue false m eLow <
      (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh := by
  have hlow_pos : 0 < fmt.normalizedValue false m eLow :=
    fmt.normalizedValue_false_pos hm
  have hlow_lt_beta : fmt.normalizedValue false m eLow < fmt.betaR ^ eLow := by
    have h := fmt.normalizedValue_abs_lt_beta_pow
      (negative := false) (e := eLow) hm
    simpa [abs_of_pos hlow_pos] using h
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  have hbetaR : fmt.betaR = 2 := by
    simp [betaR, hbeta]
  have hpow_le :
      fmt.betaR ^ (eLow + 1) ≤
        fmt.betaR ^ (eHigh - (fmt.t : ℤ)) :=
    fmt.betaR_zpow_le_zpow_of_le (by omega)
  have hhalf_le :
      (1 / 2 : ℝ) * fmt.betaR ^ (eLow + 1) ≤
        (1 / 2 : ℝ) * fmt.betaR ^ (eHigh - (fmt.t : ℤ)) := by
    exact mul_le_mul_of_nonneg_left hpow_le (by norm_num)
  have hhalf_eq :
      (1 / 2 : ℝ) * fmt.betaR ^ (eLow + 1) =
        fmt.betaR ^ eLow := by
    rw [show eLow + 1 = eLow + (1 : ℤ) by ring]
    rw [zpow_add₀ hbase, zpow_one, hbetaR]
    ring
  have hbeta_le_half :
      fmt.betaR ^ eLow ≤ (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh := by
    rw [ulpAtExponent]
    rw [← hhalf_eq]
    exact hhalf_le
  exact lt_of_lt_of_le hlow_lt_beta hbeta_le_half
/-- Operation-level positive same-sign normalized ordered-exponent addition has
finite representable local roundoff error in the strict left half-cell branch
around the high operand.

This closes a concrete large-alignment C4.4/FastTwoSum subcase: if the lower
positive normalized addend is less than half an ulp at the higher exponent, the
finite round-to-even add returns the high operand and the local error is the
finite lower operand. -/
theorem finiteRoundToEvenOp_add_positive_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
      fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
      hmHigh hmHighSucc hmLow heLow hlow hpolicy
/-- Operation-level positive normalized `high + (-low)` has finite local error
in the strict predecessor half-cell branch.

This transfers the source-evidence far-magnitude cell to the concrete finite
round-to-even add wrapper under the usual finite-normal source range
hypothesis. -/
theorem finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
      hmHigh hneHighMin hmLow heLow hlow hpolicy
/-- Operation-level negative normalized `high + (-low)` has finite local error
in the strict predecessor half-cell branch by sign symmetry. -/
theorem finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
      hbeta ht hmHigh hneHighMin hmLow heLow hlow hpolicy
/-- Operation-level positive normalized `high + (-low)` has finite local error
when the lower operand is more than one precision window below the higher
operand and the high operand has a same-exponent predecessor.

In base `2`, the exponent gap implies the lower magnitude is strictly below
half an ulp at the high exponent, so the predecessor half-cell branch applies. -/
theorem finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_exponent_gap_gt_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hgap : eLow + (fmt.t : ℤ) < eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh :=
    fmt.normalizedValue_false_lt_half_ulpAtExponent_of_exponent_gap_gt_t
      hbeta hmLow hgap
  exact
    fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
      hmHigh hneHighMin hmLow heLow hlow hxy
/-- Operation-level negative normalized `high + (-low)` has finite local error
in the same large-exponent-gap predecessor branch by sign symmetry. -/
theorem finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_exponent_gap_gt_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hgap : eLow + (fmt.t : ℤ) < eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh :=
    fmt.normalizedValue_false_lt_half_ulpAtExponent_of_exponent_gap_gt_t
      hbeta hmLow hgap
  exact
    fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
      hbeta ht hmHigh hneHighMin hmLow heLow hlow hxy
/-- Operation-level positive minimum-mantissa normalized `high + (-low)` has
finite local error in the strict boundary predecessor half-cell. -/
theorem finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_low_lt_half_pred_ulp
    {fmt : FloatingPointFormat}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_min_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_low_lt_half_pred_ulp
      hmLow heLow hlow hpolicy
/-- Operation-level negative minimum-mantissa normalized `high + (-low)` has
finite local error in the strict boundary predecessor half-cell. -/
theorem finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_low_lt_half_pred_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_min_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_low_lt_half_pred_ulp
      hbeta ht hmLow heLow hlow hpolicy
/-- Operation-level positive minimum-mantissa normalized `high + (-low)` has
finite local error when the smaller operand is more than one precision window
below the boundary predecessor exponent. -/
theorem finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_exponent_gap_gt_t_pred
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hgap : eLow + (fmt.t : ℤ) < eHigh - 1)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) :=
    fmt.normalizedValue_false_lt_half_ulpAtExponent_of_exponent_gap_gt_t
      hbeta hmLow hgap
  exact
    fmt.finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_low_lt_half_pred_ulp
      hmLow heLow hlow hxy
/-- Operation-level negative minimum-mantissa normalized `high + (-low)` has
finite local error in the same strict boundary predecessor exponent-gap
branch. -/
theorem finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_exponent_gap_gt_t_pred
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hgap : eLow + (fmt.t : ℤ) < eHigh - 1)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) :=
    fmt.normalizedValue_false_lt_half_ulpAtExponent_of_exponent_gap_gt_t
      hbeta hmLow hgap
  exact
    fmt.finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_low_lt_half_pred_ulp
      hbeta ht hmLow heLow hlow hxy
/-- Positive normalized `high + (-low)` has finite local error at the
predecessor half-ulp tie, provided the high operand has a same-exponent
predecessor.

Source round-to-even may select either adjacent endpoint; the residual is the
finite lower operand or its negation. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) - y) := by
  let a := fmt.normalizedValue false (mHigh - 1) eHigh
  let b := fmt.normalizedValue false mHigh eHigh
  let low := fmt.normalizedValue false mLow eLow
  have hmHighPred :
      fmt.normalizedMantissa (mHigh - 1) :=
    fmt.normalizedMantissa_pred_of_ne_minNormalMantissa hmHigh hneHighMin
  have hmHigh_pos : 0 < mHigh :=
    fmt.normalizedMantissa_pos hmHigh
  have hpred_succ : (mHigh - 1) + 1 = mHigh := by
    omega
  have hlow_eq : low = (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh := by
    simpa [low] using hlow
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.normalizedValue_false_pos hmLow
  have hulp_pos : 0 < fmt.ulpAtExponent eHigh :=
    fmt.ulpAtExponent_pos eHigh
  have hlow_lt_ulp : low < fmt.ulpAtExponent eHigh := by
    rw [hlow_eq]
    linarith
  have hb_sub_a : b - a = fmt.ulpAtExponent eHigh := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_succ_sub_sameExponent false (mHigh - 1) eHigh)
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, mHigh - 1, eHigh, hmHighPred, ?_, Or.inl ?_⟩
    · simpa [hpred_succ] using hmHigh
    · exact ⟨rfl, by dsimp [b]; rw [hpred_succ]⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hsource_eq :
      fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow =
        b - low := by
    dsimp [b, low]
    rw [fmt.normalizedValue_true_eq_neg_false]
    ring
  have hpolicy' :
      fmt.sourceRoundToEvenEvidence (b - low) y := by
    simpa [hsource_eq] using hpolicy
  have hsource_between : a ≤ b - low ∧ b - low ≤ b := by
    constructor <;> linarith
  have hlow_fin : fmt.finiteSystem low :=
    Or.inr (Or.inl ⟨false, mLow, eLow, hmLow, heLow, rfl⟩)
  rcases
      fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
        hpolicy' hadj hsource_between with hy | hy
  · rw [hy]
    convert hlow_fin using 1
    dsimp [b, low]
    rw [fmt.normalizedValue_true_eq_neg_false]
    linarith
  · rw [hy]
    have hneg_low_fin := fmt.finiteSystem_neg hlow_fin
    convert hneg_low_fin using 1
    dsimp [b, low]
    rw [fmt.normalizedValue_true_eq_neg_false]
    ring
/-- Operation-level positive normalized `high + (-low)` has finite local
error at the predecessor half-ulp tie. -/
theorem finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
      hmHigh hneHighMin hmLow heLow hlow hpolicy
/-- Negative normalized `high + (-low)` has finite local error at the
predecessor half-ulp tie by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) - y) := by
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    convert hneg using 1
    simp [fmt.normalizedValue_true_eq_neg_false]
    ring
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false mHigh eHigh +
            fmt.normalizedValue true mLow eLow) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
      hmHigh hneHighMin hmLow heLow hlow hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [fmt.normalizedValue_true_eq_neg_false]
  ring
/-- Operation-level negative normalized `high + (-low)` has finite local
error at the predecessor half-ulp tie. -/
theorem finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
      hbeta ht hmHigh hneHighMin hmLow heLow hlow hpolicy
/-- Positive normalized `high + (-low)` has finite local error in the strict
right half-cell around the predecessor.

When the lower magnitude is strictly between half an ulp and one ulp at the
high exponent, source round-to-even selects the predecessor endpoint.  The
residual `ulp - low` lies on the lower operand lattice under
`eHigh = eLow + t`. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
        fmt.normalizedValue false mLow eLow)
    (hulp :
      fmt.normalizedValue false mLow eLow < fmt.ulpAtExponent eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) - y) := by
  let a := fmt.normalizedValue false (mHigh - 1) eHigh
  let b := fmt.normalizedValue false mHigh eHigh
  let low := fmt.normalizedValue false mLow eLow
  have hmHighPred :
      fmt.normalizedMantissa (mHigh - 1) :=
    fmt.normalizedMantissa_pred_of_ne_minNormalMantissa hmHigh hneHighMin
  have hmHigh_pos : 0 < mHigh :=
    fmt.normalizedMantissa_pos hmHigh
  have hpred_succ : (mHigh - 1) + 1 = mHigh := by
    omega
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.normalizedValue_false_pos hmLow
  have hb_sub_a : b - a = fmt.ulpAtExponent eHigh := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_succ_sub_sameExponent false (mHigh - 1) eHigh)
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, mHigh - 1, eHigh, hmHighPred, ?_, Or.inl ?_⟩
    · simpa [hpred_succ] using hmHigh
    · exact ⟨rfl, by dsimp [b]; rw [hpred_succ]⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hsource_eq :
      fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow =
        b - low := by
    dsimp [b, low]
    rw [fmt.normalizedValue_true_eq_neg_false]
    ring
  have hpolicy' :
      fmt.sourceRoundToEvenEvidence (b - low) y := by
    simpa [hsource_eq] using hpolicy
  have ha_lt_source : a < b - low := by
    linarith
  have hsource_lt_b : b - low < b := by
    linarith
  have hright_abs : |(b - low) - b| = low := by
    have hsub : (b - low) - b = -low := by ring
    rw [hsub, abs_neg, abs_of_pos hlow_pos]
  have hleft_abs :
      |(b - low) - a| = fmt.ulpAtExponent eHigh - low := by
    have hsub : (b - low) - a = fmt.ulpAtExponent eHigh - low := by
      linarith
    have hpos : 0 < fmt.ulpAtExponent eHigh - low := by
      linarith
    rw [hsub, abs_of_pos hpos]
  have hleftCloser : |(b - low) - a| < |(b - low) - b| := by
    rw [hright_abs, hleft_abs]
    linarith
  have hy : y = a := by
    exact
      fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
        hpolicy' hadj ⟨ha_lt_source, hsource_lt_b⟩ hleftCloser
  have hulp_lattice :
      fmt.ulpAtExponent eHigh =
        ((fmt.beta ^ fmt.t : ℕ) : ℝ) *
          fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
    calc
      fmt.ulpAtExponent eHigh =
          fmt.betaR ^ (eLow + (fmt.t : ℤ) - (fmt.t : ℤ)) := by
        rw [ulpAtExponent, hexp]
      _ = fmt.betaR ^ eLow := by
        congr 1
        ring
      _ = fmt.betaR ^ fmt.t * fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
        exact (fmt.mantissaBound_scale_eq eLow).symm
      _ = ((fmt.beta ^ fmt.t : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
        simp [betaR, Nat.cast_pow]
  have hdiff :
      ((((fmt.beta ^ fmt.t : ℕ) : ℤ) - (mLow : ℤ)).natAbs <
        fmt.beta ^ fmt.t) := by
    have hm_lt : mLow < fmt.beta ^ fmt.t := hmLow.2
    have hm_pos : 0 < mLow := fmt.normalizedMantissa_pos hmLow
    have hgap_nonneg :
        0 ≤ ((fmt.beta ^ fmt.t : ℕ) : ℤ) - (mLow : ℤ) := by
      omega
    have hnatabs :
        (((((fmt.beta ^ fmt.t : ℕ) : ℤ) - (mLow : ℤ)).natAbs : ℤ) =
          ((fmt.beta ^ fmt.t : ℕ) : ℤ) - (mLow : ℤ)) := by
      exact Int.natAbs_of_nonneg hgap_nonneg
    omega
  have hfin_scaled :
      fmt.finiteSystem
        (fmt.signValue false *
            ((((fmt.beta ^ fmt.t : ℕ) : ℤ) : ℝ)) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ)) -
          fmt.signValue false * ((mLow : ℤ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) :=
    fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := false)
      (k := ((fmt.beta ^ fmt.t : ℕ) : ℤ))
      (l := (mLow : ℤ)) (e := eLow) heLow hdiff
  rw [hy, hsource_eq]
  change fmt.finiteSystem ((b - low) - a)
  convert hfin_scaled using 1
  have hres : (b - low) - a = fmt.ulpAtExponent eHigh - low := by
    linarith
  rw [hres, hulp_lattice]
  dsimp [low]
  simp [normalizedValue, signValue]
/-- Operation-level positive normalized `high + (-low)` has finite local error
in the strict predecessor right-half branch. -/
theorem finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
        fmt.normalizedValue false mLow eLow)
    (hulp :
      fmt.normalizedValue false mLow eLow < fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hmHigh hneHighMin hmLow heLow hexp hhalf hulp hpolicy
/-- Negative normalized `high + (-low)` has finite local error in the strict
predecessor right-half branch by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
        fmt.normalizedValue false mLow eLow)
    (hulp :
      fmt.normalizedValue false mLow eLow < fmt.ulpAtExponent eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) - y) := by
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    convert hneg using 1
    simp [fmt.normalizedValue_true_eq_neg_false]
    ring
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false mHigh eHigh +
            fmt.normalizedValue true mLow eLow) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hmHigh hneHighMin hmLow heLow hexp hhalf hulp hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [fmt.normalizedValue_true_eq_neg_false]
  ring
/-- Operation-level negative normalized `high + (-low)` has finite local error
in the strict predecessor right-half branch. -/
theorem finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
        fmt.normalizedValue false mLow eLow)
    (hulp :
      fmt.normalizedValue false mLow eLow < fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hbeta ht hmHigh hneHighMin hmLow heLow hexp hhalf hulp hpolicy
/-- Positive normalized `high + (-low)` is exact when the lower magnitude is
exactly one high-exponent ulp and the high operand has a same-exponent
predecessor. -/
theorem finiteRoundToEvenOp_add_positive_neg_orderedExponent_eq_exact_of_low_eq_ulp
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (_hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (hlow :
      fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue false mHigh eHigh)
        (fmt.normalizedValue true mLow eLow) =
      fmt.normalizedValue false mHigh eHigh +
        fmt.normalizedValue true mLow eLow := by
  let a := fmt.normalizedValue false (mHigh - 1) eHigh
  let b := fmt.normalizedValue false mHigh eHigh
  let low := fmt.normalizedValue false mLow eLow
  have hmHighPred :
      fmt.normalizedMantissa (mHigh - 1) :=
    fmt.normalizedMantissa_pred_of_ne_minNormalMantissa hmHigh hneHighMin
  have hmHigh_pos : 0 < mHigh :=
    fmt.normalizedMantissa_pos hmHigh
  have hpred_succ : (mHigh - 1) + 1 = mHigh := by
    omega
  have hb_sub_a : b - a = fmt.ulpAtExponent eHigh := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_succ_sub_sameExponent false (mHigh - 1) eHigh)
  have hsource_eq :
      fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow =
        a := by
    dsimp [a, b, low]
    rw [fmt.normalizedValue_true_eq_neg_false, hlow]
    linarith
  have hfin_source :
      fmt.finiteSystem
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) := by
    rw [hsource_eq]
    exact Or.inr (Or.inl ⟨false, mHigh - 1, eHigh, hmHighPred, heHigh, rfl⟩)
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue false mHigh eHigh)
      (y := fmt.normalizedValue true mLow eLow)
      hfin_source)
/-- The positive exact-predecessor branch has zero local roundoff error. -/
theorem finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_low_eq_ulp
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (hlow :
      fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  rw [
    finiteRoundToEvenOp_add_positive_neg_orderedExponent_eq_exact_of_low_eq_ulp
      hmHigh hneHighMin hmLow heHigh hlow]
  simpa using fmt.finiteSystem_zero
/-- Negative normalized `high + (-low)` is exact when the lower positive
operand is exactly one high-exponent ulp and the high operand has a
same-exponent predecessor. -/
theorem finiteRoundToEvenOp_add_negative_pos_orderedExponent_eq_exact_of_low_eq_ulp
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (_hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (hlow :
      fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue true mHigh eHigh)
        (fmt.normalizedValue false mLow eLow) =
      fmt.normalizedValue true mHigh eHigh +
        fmt.normalizedValue false mLow eLow := by
  let a := fmt.normalizedValue false (mHigh - 1) eHigh
  let b := fmt.normalizedValue false mHigh eHigh
  have hmHighPred :
      fmt.normalizedMantissa (mHigh - 1) :=
    fmt.normalizedMantissa_pred_of_ne_minNormalMantissa hmHigh hneHighMin
  have hmHigh_pos : 0 < mHigh :=
    fmt.normalizedMantissa_pos hmHigh
  have hpred_succ : (mHigh - 1) + 1 = mHigh := by
    omega
  have hb_sub_a : b - a = fmt.ulpAtExponent eHigh := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_succ_sub_sameExponent false (mHigh - 1) eHigh)
  have hsource_eq :
      fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow =
        fmt.normalizedValue true (mHigh - 1) eHigh := by
    dsimp [a, b]
    rw [fmt.normalizedValue_true_eq_neg_false, hlow]
    rw [show fmt.normalizedValue true (mHigh - 1) eHigh = -a by
      rw [fmt.normalizedValue_true_eq_neg_false]]
    linarith
  have hfin_source :
      fmt.finiteSystem
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) := by
    rw [hsource_eq]
    exact Or.inr (Or.inl ⟨true, mHigh - 1, eHigh, hmHighPred, heHigh, rfl⟩)
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue true mHigh eHigh)
      (y := fmt.normalizedValue false mLow eLow)
      hfin_source)
/-- The negative exact-predecessor branch has zero local roundoff error. -/
theorem finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_low_eq_ulp
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (hlow :
      fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  rw [
    finiteRoundToEvenOp_add_negative_pos_orderedExponent_eq_exact_of_low_eq_ulp
      hmHigh hneHighMin hmLow heHigh hlow]
  simpa using fmt.finiteSystem_zero
/-- Dispatcher for the positive normalized opposite-sign predecessor
low-cell split. -/
theorem finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_low_cell_cases
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hcell :
      fmt.normalizedValue false mLow eLow <
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        fmt.normalizedValue false mLow eLow =
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
            fmt.normalizedValue false mLow eLow ∧
          fmt.normalizedValue false mLow eLow <
            fmt.ulpAtExponent eHigh) ∨
        fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  rcases hcell with hlt | hrest
  · exact
      fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
        hmHigh hneHighMin hmLow heLow hlt hxy
  · rcases hrest with heq | hrest
    · exact
        fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
          hmHigh hneHighMin hmLow heLow heq hxy
    · rcases hrest with hright | hulp
      · exact
          fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
            hmHigh hneHighMin hmLow heLow hexp hright.1 hright.2 hxy
      · exact
          fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_low_eq_ulp
            hmHigh hneHighMin hmLow heHigh hulp
/-- Dispatcher for the negative normalized opposite-sign predecessor
low-cell split. -/
theorem finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_low_cell_cases
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hcell :
      fmt.normalizedValue false mLow eLow <
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        fmt.normalizedValue false mLow eLow =
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
            fmt.normalizedValue false mLow eLow ∧
          fmt.normalizedValue false mLow eLow <
            fmt.ulpAtExponent eHigh) ∨
        fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  rcases hcell with hlt | hrest
  · exact
      fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
        hbeta ht hmHigh hneHighMin hmLow heLow hlt hxy
  · rcases hrest with heq | hrest
    · exact
        fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
          hbeta ht hmHigh hneHighMin hmLow heLow heq hxy
    · rcases hrest with hright | hulp
      · exact
          fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
            hbeta ht hmHigh hneHighMin hmLow heLow hexp hright.1 hright.2 hxy
      · exact
          fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_low_eq_ulp
            hmHigh hneHighMin hmLow heHigh hulp
/-- Positive minimum-mantissa normalized `high + (-low)` has finite local error
at the boundary predecessor half-ulp tie. -/
theorem sourceRoundToEvenEvidence_positive_min_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_low_eq_half_pred_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) - y) := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa (eHigh - 1)
  let b := fmt.normalizedValue false fmt.minNormalMantissa eHigh
  let low := fmt.normalizedValue false mLow eLow
  have hpred_succ : eHigh - 1 + 1 = eHigh := by
    ring
  have hlow_eq : low = (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) := by
    simpa [low] using hlow
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.normalizedValue_false_pos hmLow
  have hulp_pos : 0 < fmt.ulpAtExponent (eHigh - 1) :=
    fmt.ulpAtExponent_pos (eHigh - 1)
  have hlow_lt_ulp : low < fmt.ulpAtExponent (eHigh - 1) := by
    rw [hlow_eq]
    linarith
  have hb_sub_a : b - a = fmt.ulpAtExponent (eHigh - 1) := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_boundary_sub false (eHigh - 1))
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, eHigh - 1, Or.inl ?_⟩
    exact ⟨rfl, by dsimp [b]; rw [hpred_succ]⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hsource_eq :
      fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow =
        b - low := by
    dsimp [b, low]
    rw [fmt.normalizedValue_true_eq_neg_false]
    ring
  have hpolicy' :
      fmt.sourceRoundToEvenEvidence (b - low) y := by
    simpa [hsource_eq] using hpolicy
  have hsource_between : a ≤ b - low ∧ b - low ≤ b := by
    constructor <;> linarith
  have hlow_fin : fmt.finiteSystem low :=
    Or.inr (Or.inl ⟨false, mLow, eLow, hmLow, heLow, rfl⟩)
  rcases
      fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
        hpolicy' hadj hsource_between with hy | hy
  · rw [hy, hsource_eq]
    convert hlow_fin using 1
    linarith
  · rw [hy, hsource_eq]
    have hneg_low_fin := fmt.finiteSystem_neg hlow_fin
    convert hneg_low_fin using 1
    ring
/-- Operation-level positive minimum-mantissa normalized `high + (-low)` has
finite local error at the boundary predecessor half-ulp tie. -/
theorem finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_low_eq_half_pred_ulp
    {fmt : FloatingPointFormat}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_min_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_low_eq_half_pred_ulp
      hmLow heLow hlow hpolicy
/-- Negative minimum-mantissa normalized `high + (-low)` has finite local error
at the boundary predecessor half-ulp tie by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_min_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_low_eq_half_pred_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) - y) := by
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    convert hneg using 1
    simp [fmt.normalizedValue_true_eq_neg_false]
    ring
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
            fmt.normalizedValue true mLow eLow) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_min_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_low_eq_half_pred_ulp
      hmLow heLow hlow hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [fmt.normalizedValue_true_eq_neg_false]
  ring
/-- Operation-level negative minimum-mantissa normalized `high + (-low)` has
finite local error at the boundary predecessor half-ulp tie. -/
theorem finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_low_eq_half_pred_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_min_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_low_eq_half_pred_ulp
      hbeta ht hmLow heLow hlow hpolicy
/-- Positive minimum-mantissa normalized `high + (-low)` has finite local error
in the strict right half-cell around the boundary predecessor. -/
theorem sourceRoundToEvenEvidence_positive_min_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_half_pred_ulp_lt_low_lt_pred_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh - 1 = eLow + (fmt.t : ℤ))
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) <
        fmt.normalizedValue false mLow eLow)
    (hulp :
      fmt.normalizedValue false mLow eLow <
        fmt.ulpAtExponent (eHigh - 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) - y) := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa (eHigh - 1)
  let b := fmt.normalizedValue false fmt.minNormalMantissa eHigh
  let low := fmt.normalizedValue false mLow eLow
  have hpred_succ : eHigh - 1 + 1 = eHigh := by
    ring
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.normalizedValue_false_pos hmLow
  have hb_sub_a : b - a = fmt.ulpAtExponent (eHigh - 1) := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_boundary_sub false (eHigh - 1))
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, eHigh - 1, Or.inl ?_⟩
    exact ⟨rfl, by dsimp [b]; rw [hpred_succ]⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hsource_eq :
      fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow =
        b - low := by
    dsimp [b, low]
    rw [fmt.normalizedValue_true_eq_neg_false]
    ring
  have hpolicy' :
      fmt.sourceRoundToEvenEvidence (b - low) y := by
    simpa [hsource_eq] using hpolicy
  have ha_lt_source : a < b - low := by
    linarith
  have hsource_lt_b : b - low < b := by
    linarith
  have hright_abs : |(b - low) - b| = low := by
    have hsub : (b - low) - b = -low := by ring
    rw [hsub, abs_neg, abs_of_pos hlow_pos]
  have hleft_abs :
      |(b - low) - a| = fmt.ulpAtExponent (eHigh - 1) - low := by
    have hsub :
        (b - low) - a = fmt.ulpAtExponent (eHigh - 1) - low := by
      linarith
    have hpos : 0 < fmt.ulpAtExponent (eHigh - 1) - low := by
      linarith
    rw [hsub, abs_of_pos hpos]
  have hleftCloser : |(b - low) - a| < |(b - low) - b| := by
    rw [hright_abs, hleft_abs]
    linarith
  have hy : y = a := by
    exact
      fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
        hpolicy' hadj ⟨ha_lt_source, hsource_lt_b⟩ hleftCloser
  have hulp_lattice :
      fmt.ulpAtExponent (eHigh - 1) =
        ((fmt.beta ^ fmt.t : ℕ) : ℝ) *
          fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
    calc
      fmt.ulpAtExponent (eHigh - 1) =
          fmt.betaR ^ (eLow + (fmt.t : ℤ) - (fmt.t : ℤ)) := by
        rw [ulpAtExponent, hexp]
      _ = fmt.betaR ^ eLow := by
        congr 1
        ring
      _ = fmt.betaR ^ fmt.t * fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
        exact (fmt.mantissaBound_scale_eq eLow).symm
      _ = ((fmt.beta ^ fmt.t : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
        simp [betaR, Nat.cast_pow]
  have hdiff :
      ((((fmt.beta ^ fmt.t : ℕ) : ℤ) - (mLow : ℤ)).natAbs <
        fmt.beta ^ fmt.t) := by
    have hm_lt : mLow < fmt.beta ^ fmt.t := hmLow.2
    have hm_pos : 0 < mLow := fmt.normalizedMantissa_pos hmLow
    have hgap_nonneg :
        0 ≤ ((fmt.beta ^ fmt.t : ℕ) : ℤ) - (mLow : ℤ) := by
      omega
    have hnatabs :
        (((((fmt.beta ^ fmt.t : ℕ) : ℤ) - (mLow : ℤ)).natAbs : ℤ) =
          ((fmt.beta ^ fmt.t : ℕ) : ℤ) - (mLow : ℤ)) := by
      exact Int.natAbs_of_nonneg hgap_nonneg
    omega
  have hfin_scaled :
      fmt.finiteSystem
        (fmt.signValue false *
            ((((fmt.beta ^ fmt.t : ℕ) : ℤ) : ℝ)) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ)) -
          fmt.signValue false * ((mLow : ℤ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) :=
    fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := false)
      (k := ((fmt.beta ^ fmt.t : ℕ) : ℤ))
      (l := (mLow : ℤ)) (e := eLow) heLow hdiff
  rw [hy, hsource_eq]
  change fmt.finiteSystem ((b - low) - a)
  convert hfin_scaled using 1
  have hres : (b - low) - a = fmt.ulpAtExponent (eHigh - 1) - low := by
    linarith
  rw [hres, hulp_lattice]
  dsimp [low]
  simp [normalizedValue, signValue]
/-- Operation-level positive minimum-mantissa normalized `high + (-low)` has
finite local error in the strict boundary predecessor right-half branch. -/
theorem finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_half_pred_ulp_lt_low_lt_pred_ulp
    {fmt : FloatingPointFormat}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh - 1 = eLow + (fmt.t : ℤ))
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) <
        fmt.normalizedValue false mLow eLow)
    (hulp :
      fmt.normalizedValue false mLow eLow <
        fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_min_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_half_pred_ulp_lt_low_lt_pred_ulp
      hmLow heLow hexp hhalf hulp hpolicy
/-- Negative minimum-mantissa normalized `high + (-low)` has finite local error
in the strict boundary predecessor right-half branch by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_min_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_half_pred_ulp_lt_low_lt_pred_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh - 1 = eLow + (fmt.t : ℤ))
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) <
        fmt.normalizedValue false mLow eLow)
    (hulp :
      fmt.normalizedValue false mLow eLow <
        fmt.ulpAtExponent (eHigh - 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) - y) := by
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    convert hneg using 1
    simp [fmt.normalizedValue_true_eq_neg_false]
    ring
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
            fmt.normalizedValue true mLow eLow) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_min_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_half_pred_ulp_lt_low_lt_pred_ulp
      hmLow heLow hexp hhalf hulp hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [fmt.normalizedValue_true_eq_neg_false]
  ring
/-- Operation-level negative minimum-mantissa normalized `high + (-low)` has
finite local error in the strict boundary predecessor right-half branch. -/
theorem finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_half_pred_ulp_lt_low_lt_pred_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh - 1 = eLow + (fmt.t : ℤ))
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) <
        fmt.normalizedValue false mLow eLow)
    (hulp :
      fmt.normalizedValue false mLow eLow <
        fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_min_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_half_pred_ulp_lt_low_lt_pred_ulp
      hbeta ht hmLow heLow hexp hhalf hulp hpolicy
/-- Positive minimum-mantissa normalized `high + (-low)` is exact when the
lower magnitude is exactly one boundary predecessor ulp. -/
theorem finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_eq_exact_of_low_eq_pred_ulp
    {fmt : FloatingPointFormat}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (_hmLow : fmt.normalizedMantissa mLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
        (fmt.normalizedValue true mLow eLow) =
      fmt.normalizedValue false fmt.minNormalMantissa eHigh +
        fmt.normalizedValue true mLow eLow := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa (eHigh - 1)
  let b := fmt.normalizedValue false fmt.minNormalMantissa eHigh
  let low := fmt.normalizedValue false mLow eLow
  have hpred_succ : eHigh - 1 + 1 = eHigh := by
    ring
  have hb_sub_a : b - a = fmt.ulpAtExponent (eHigh - 1) := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_boundary_sub false (eHigh - 1))
  have hsource_eq :
      fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow =
        a := by
    dsimp [a, b, low]
    rw [fmt.normalizedValue_true_eq_neg_false, hlow]
    linarith
  have ha_unbounded : fmt.unboundedNormalizedSystem a :=
    ⟨false, fmt.maxNormalMantissa, eHigh - 1,
      fmt.maxNormalMantissa_normalized, rfl⟩
  have ha_range : fmt.finiteNormalRange a := by
    simpa [hsource_eq] using hxy
  have ha_norm : fmt.normalizedSystem a :=
    fmt.unboundedNormalizedSystem_normalizedSystem_of_finiteNormalRange
      ha_unbounded ha_range
  have hfin_source :
      fmt.finiteSystem
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) := by
    rw [hsource_eq]
    exact Or.inr (Or.inl ha_norm)
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue false fmt.minNormalMantissa eHigh)
      (y := fmt.normalizedValue true mLow eLow)
      hfin_source)
/-- The positive boundary exact-predecessor branch has zero local roundoff
error. -/
theorem finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_low_eq_pred_ulp
    {fmt : FloatingPointFormat}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  rw [
    finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_eq_exact_of_low_eq_pred_ulp
      hmLow hlow hxy]
  simpa using fmt.finiteSystem_zero
/-- Negative minimum-mantissa normalized `high + (-low)` is exact when the
lower positive operand is exactly one boundary predecessor ulp. -/
theorem finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_eq_exact_of_low_eq_pred_ulp
    {fmt : FloatingPointFormat}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (_hmLow : fmt.normalizedMantissa mLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
        (fmt.normalizedValue false mLow eLow) =
      fmt.normalizedValue true fmt.minNormalMantissa eHigh +
        fmt.normalizedValue false mLow eLow := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa (eHigh - 1)
  let b := fmt.normalizedValue false fmt.minNormalMantissa eHigh
  have hpred_succ : eHigh - 1 + 1 = eHigh := by
    ring
  have hb_sub_a : b - a = fmt.ulpAtExponent (eHigh - 1) := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_boundary_sub false (eHigh - 1))
  have hsource_eq :
      fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow =
        fmt.normalizedValue true fmt.maxNormalMantissa (eHigh - 1) := by
    dsimp [a, b]
    rw [fmt.normalizedValue_true_eq_neg_false, hlow]
    rw [show fmt.normalizedValue true fmt.maxNormalMantissa (eHigh - 1) = -a by
      rw [fmt.normalizedValue_true_eq_neg_false]]
    linarith
  have ha_unbounded :
      fmt.unboundedNormalizedSystem
        (fmt.normalizedValue true fmt.maxNormalMantissa (eHigh - 1)) :=
    ⟨true, fmt.maxNormalMantissa, eHigh - 1,
      fmt.maxNormalMantissa_normalized, rfl⟩
  have ha_range :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.maxNormalMantissa (eHigh - 1)) := by
    simpa [hsource_eq] using hxy
  have ha_norm :
      fmt.normalizedSystem
        (fmt.normalizedValue true fmt.maxNormalMantissa (eHigh - 1)) :=
    fmt.unboundedNormalizedSystem_normalizedSystem_of_finiteNormalRange
      ha_unbounded ha_range
  have hfin_source :
      fmt.finiteSystem
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) := by
    rw [hsource_eq]
    exact Or.inr (Or.inl ha_norm)
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue true fmt.minNormalMantissa eHigh)
      (y := fmt.normalizedValue false mLow eLow)
      hfin_source)
/-- The negative boundary exact-predecessor branch has zero local roundoff
error. -/
theorem finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_low_eq_pred_ulp
    {fmt : FloatingPointFormat}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  rw [
    finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_eq_exact_of_low_eq_pred_ulp
      hmLow hlow hxy]
  simpa using fmt.finiteSystem_zero
/-- Dispatcher for the positive minimum-mantissa normalized opposite-sign
boundary predecessor low-cell split. -/
theorem finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_pred_low_cell_cases
    {fmt : FloatingPointFormat}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh - 1 = eLow + (fmt.t : ℤ))
    (hcell :
      fmt.normalizedValue false mLow eLow <
          (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) ∨
        fmt.normalizedValue false mLow eLow =
          (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) <
            fmt.normalizedValue false mLow eLow ∧
          fmt.normalizedValue false mLow eLow <
            fmt.ulpAtExponent (eHigh - 1)) ∨
        fmt.normalizedValue false mLow eLow =
          fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  rcases hcell with hlt | hrest
  · exact
      fmt.finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_low_lt_half_pred_ulp
        hmLow heLow hlt hxy
  · rcases hrest with heq | hrest
    · exact
        fmt.finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_low_eq_half_pred_ulp
          hmLow heLow heq hxy
    · rcases hrest with hright | hulp
      · exact
          fmt.finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_half_pred_ulp_lt_low_lt_pred_ulp
            hmLow heLow hexp hright.1 hright.2 hxy
      · exact
          fmt.finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_low_eq_pred_ulp
            hmLow hulp hxy
/-- Dispatcher for the negative minimum-mantissa normalized opposite-sign
boundary predecessor low-cell split. -/
theorem finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_pred_low_cell_cases
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh - 1 = eLow + (fmt.t : ℤ))
    (hcell :
      fmt.normalizedValue false mLow eLow <
          (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) ∨
        fmt.normalizedValue false mLow eLow =
          (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) <
            fmt.normalizedValue false mLow eLow ∧
          fmt.normalizedValue false mLow eLow <
            fmt.ulpAtExponent (eHigh - 1)) ∨
        fmt.normalizedValue false mLow eLow =
          fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  rcases hcell with hlt | hrest
  · exact
      fmt.finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_low_lt_half_pred_ulp
        hbeta ht hmLow heLow hlt hxy
  · rcases hrest with heq | hrest
    · exact
        fmt.finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_low_eq_half_pred_ulp
          hbeta ht hmLow heLow heq hxy
    · rcases hrest with hright | hulp
      · exact
          fmt.finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_half_pred_ulp_lt_low_lt_pred_ulp
            hbeta ht hmLow heLow hexp hright.1 hright.2 hxy
      · exact
          fmt.finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_low_eq_pred_ulp
            hmLow hulp hxy
/-- Negative same-sign normalized ordered-exponent addition has finite local
roundoff error in the strict left half-cell branch around the high-magnitude
operand.

This is the sign-symmetric companion of the positive branch: negating the
source round-to-even evidence reduces the proof to the positive left half-cell
case, and the local error is the negation of that positive-branch error. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue true mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue true mLow eLow) - y) := by
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    rw [add_comm]
    convert hneg using 1
    simp [fmt.normalizedValue_true_eq_neg_false]
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false mHigh eHigh +
            fmt.normalizedValue false mLow eLow) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
      hmHigh hmHighSucc hmLow heLow hlow hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [fmt.normalizedValue_true_eq_neg_false]
  ring
/-- Operation-level negative same-sign normalized ordered-exponent addition has
finite representable local roundoff error in the strict left half-cell branch.

This transfers the source-evidence sign-symmetric branch to the concrete finite
round-to-even add wrapper. -/
theorem finiteRoundToEvenOp_add_negative_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue true mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
      hbeta ht hmHigh hmHighSucc hmLow heLow hlow hpolicy
/-- Positive same-sign normalized ordered-exponent addition has finite local
roundoff error in the strict left half-cell branch when the high operand is the
largest mantissa of its exponent.

The adjacent right endpoint is the smallest normalized mantissa at the next
exponent.  If the lower addend is strictly below half an ulp at the high
exponent, source round-to-even still selects the high operand, so the residual
is exactly the finite lower operand. -/
theorem sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) - y) := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa eHigh
  let b := fmt.normalizedValue false fmt.minNormalMantissa (eHigh + 1)
  let low := fmt.normalizedValue false mLow eLow
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.normalizedValue_false_pos hmLow
  have hulp_pos : 0 < fmt.ulpAtExponent eHigh := fmt.ulpAtExponent_pos eHigh
  have hlow_lt_ulp : low < fmt.ulpAtExponent eHigh := by
    linarith
  have hb_sub_a : b - a = fmt.ulpAtExponent eHigh := by
    dsimp [a, b]
    simpa [ulpAtExponent, signValue] using
      (fmt.normalizedValue_boundary_sub false eHigh)
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, eHigh, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have ha_lt_source : a < a + low := by
    linarith
  have hsource_lt_b : a + low < b := by
    linarith
  have hleft_abs : |(a + low) - a| = low := by
    have hsub : (a + low) - a = low := by ring
    rw [hsub, abs_of_pos hlow_pos]
  have hright_abs :
      |(a + low) - b| = fmt.ulpAtExponent eHigh - low := by
    have hsub : (a + low) - b = low - fmt.ulpAtExponent eHigh := by
      linarith
    have hneg : low - fmt.ulpAtExponent eHigh < 0 := by
      linarith
    rw [hsub, abs_of_neg hneg]
    ring
  have hleftCloser : |(a + low) - a| < |(a + low) - b| := by
    rw [hleft_abs, hright_abs]
    linarith
  have hy : y = a := by
    exact
      fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
        hpolicy hadj ⟨ha_lt_source, hsource_lt_b⟩ hleftCloser
  have hlow_fin : fmt.finiteSystem low :=
    Or.inr (Or.inl ⟨false, mLow, eLow, hmLow, heLow, rfl⟩)
  rw [hy]
  convert hlow_fin using 1
  dsimp [a, low]
  ring
/-- Operation-level positive same-sign normalized ordered-exponent addition has
finite representable local roundoff error in the strict left half-cell boundary
branch where the high operand is `maxNormalMantissa`. -/
theorem finiteRoundToEvenOp_add_positive_max_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
      hmLow heLow hlow hpolicy
/-- Negative same-sign normalized ordered-exponent addition has finite local
roundoff error in the strict left half-cell boundary branch by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_max_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) - y) := by
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    rw [add_comm]
    convert hneg using 1
    simp [fmt.normalizedValue_true_eq_neg_false]
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
            fmt.normalizedValue false mLow eLow) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
      hmLow heLow hlow hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [fmt.normalizedValue_true_eq_neg_false]
  ring
/-- Operation-level negative same-sign normalized ordered-exponent addition has
finite representable local roundoff error in the strict left half-cell boundary
branch where the high operand is `maxNormalMantissa`. -/
theorem finiteRoundToEvenOp_add_negative_max_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_max_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
      hbeta ht hmLow heLow hlow hpolicy
/-- Operation-level same-sign normalized ordered-exponent addition has finite
local error when the lower operand is more than one precision window below the
higher operand.

The exponent gap implies the lower operand is strictly below half an ulp at the
higher exponent, so this is a derived strict-left branch. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_exponent_gap_gt_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hgap : eLow + (fmt.t : ℤ) < eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  have hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh :=
    fmt.normalizedValue_false_lt_half_ulpAtExponent_of_exponent_gap_gt_t
      hbeta hmLow hgap
  cases negative
  · exact
      fmt.finiteRoundToEvenOp_add_positive_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
        hmHigh hmHighSucc hmLow heLow hlow hxy
  · exact
      fmt.finiteRoundToEvenOp_add_negative_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
        hbeta ht hmHigh hmHighSucc hmLow heLow hlow hxy
/-- Commuted operation-level same-sign normalized ordered-exponent addition
has finite local error when the lower operand is more than one precision window
below the higher operand. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_exponent_gap_gt_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hgap : eLow + (fmt.t : ℤ) < eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
  have hxy_order :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) := by
    convert hxy using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue negative mHigh eHigh +
            fmt.normalizedValue negative mLow eLow) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.normalizedValue negative mHigh eHigh)
            (fmt.normalizedValue negative mLow eLow)) :=
    fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_exponent_gap_gt_t
      hbeta ht hmHigh hmHighSucc hmLow heLow hgap hxy_order
  have hop :
      fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh) =
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow) := by
    simp [finiteRoundToEvenOp, BasicOp.exact, add_comm]
  rw [hop]
  convert hfin using 1
  ring
/-- Operation-level same-sign normalized ordered-exponent addition has finite
local error in the large exponent-gap branch when the high operand is
`maxNormalMantissa`. -/
theorem finiteRoundToEvenOp_add_max_sameSign_orderedExponent_error_finiteSystem_of_exponent_gap_gt_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hgap : eLow + (fmt.t : ℤ) < eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  have hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh :=
    fmt.normalizedValue_false_lt_half_ulpAtExponent_of_exponent_gap_gt_t
      hbeta hmLow hgap
  cases negative
  · exact
      fmt.finiteRoundToEvenOp_add_positive_max_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
        hmLow heLow hlow hxy
  · exact
      fmt.finiteRoundToEvenOp_add_negative_max_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
        hbeta ht hmLow heLow hlow hxy
/-- Commuted operation-level same-sign normalized ordered-exponent addition
has finite local error in the large exponent-gap branch when the high operand
is `maxNormalMantissa`. -/
theorem finiteRoundToEvenOp_add_max_sameSign_orderedExponent_comm_error_finiteSystem_of_exponent_gap_gt_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hgap : eLow + (fmt.t : ℤ) < eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative fmt.maxNormalMantissa eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)) := by
  have hxy_order :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue negative mLow eLow) := by
    convert hxy using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue negative fmt.maxNormalMantissa eHigh +
            fmt.normalizedValue negative mLow eLow) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)
            (fmt.normalizedValue negative mLow eLow)) :=
    fmt.finiteRoundToEvenOp_add_max_sameSign_orderedExponent_error_finiteSystem_of_exponent_gap_gt_t
      hbeta ht hmLow heLow hgap hxy_order
  have hop :
      fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh) =
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue negative mLow eLow) := by
    simp [finiteRoundToEvenOp, BasicOp.exact, add_comm]
  rw [hop]
  convert hfin using 1
  ring
/-- Positive same-sign normalized ordered-exponent addition has finite local
roundoff error at the exact half-ulp tie when the high operand is
`maxNormalMantissa`.

The adjacent right endpoint is the smallest normalized mantissa in the next
binade.  At the tie, source round-to-even may select either endpoint; the
residual is the finite lower operand or its negation. -/
theorem sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) - y) := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa eHigh
  let b := fmt.normalizedValue false fmt.minNormalMantissa (eHigh + 1)
  let low := fmt.normalizedValue false mLow eLow
  have hlow_eq : low = (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh := by
    simpa [low] using hlow
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.normalizedValue_false_pos hmLow
  have hulp_pos : 0 < fmt.ulpAtExponent eHigh := fmt.ulpAtExponent_pos eHigh
  have hlow_lt_ulp : low < fmt.ulpAtExponent eHigh := by
    rw [hlow_eq]
    linarith
  have hb_sub_a : b - a = fmt.ulpAtExponent eHigh := by
    dsimp [a, b]
    simpa [ulpAtExponent, signValue] using
      (fmt.normalizedValue_boundary_sub false eHigh)
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, eHigh, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hsource_between : a ≤ a + low ∧ a + low ≤ b := by
    constructor <;> linarith
  have hlow_fin : fmt.finiteSystem low :=
    Or.inr (Or.inl ⟨false, mLow, eLow, hmLow, heLow, rfl⟩)
  rcases
      fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
        hpolicy hadj hsource_between with hy | hy
  · rw [hy]
    convert hlow_fin using 1
    dsimp [a, low]
    ring
  · rw [hy]
    have hfin_neg := fmt.finiteSystem_neg hlow_fin
    convert hfin_neg using 1
    have hres : (a + low) - b = -low := by
      linarith
    rw [hres]
/-- Operation-level positive same-sign normalized ordered-exponent addition has
finite representable local roundoff error at the exact half-ulp boundary tie
where the high operand is `maxNormalMantissa`. -/
theorem finiteRoundToEvenOp_add_positive_max_sameSign_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
      hmLow heLow hlow hpolicy
/-- Negative same-sign normalized ordered-exponent addition has finite local
roundoff error at the exact half-ulp boundary tie by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_max_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) - y) := by
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    rw [add_comm]
    convert hneg using 1
    simp [fmt.normalizedValue_true_eq_neg_false]
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
            fmt.normalizedValue false mLow eLow) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
      hmLow heLow hlow hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [fmt.normalizedValue_true_eq_neg_false]
  ring
/-- Operation-level negative same-sign normalized ordered-exponent addition has
finite representable local roundoff error at the exact half-ulp boundary tie
where the high operand is `maxNormalMantissa`. -/
theorem finiteRoundToEvenOp_add_negative_max_sameSign_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_max_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
      hbeta ht hmLow heLow hlow hpolicy
/-- Positive same-sign normalized ordered-exponent addition is exact at the
max-mantissa exponent boundary when the lower addend is exactly one ulp at the
higher exponent.

The exact source sum is the next-binade minimum endpoint.  The finite-normal
range hypothesis supplies the needed bounded-exponent certificate for that
endpoint. -/
theorem finiteRoundToEvenOp_add_positive_max_sameSign_orderedExponent_eq_exact_of_low_eq_ulp
    {fmt : FloatingPointFormat}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (_hmLow : fmt.normalizedMantissa mLow)
    (hlow :
      fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue false fmt.maxNormalMantissa eHigh)
        (fmt.normalizedValue false mLow eLow) =
      fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
        fmt.normalizedValue false mLow eLow := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa eHigh
  let b := fmt.normalizedValue false fmt.minNormalMantissa (eHigh + 1)
  let low := fmt.normalizedValue false mLow eLow
  have hb_sub_a : b - a = fmt.ulpAtExponent eHigh := by
    dsimp [a, b]
    simpa [ulpAtExponent, signValue] using
      (fmt.normalizedValue_boundary_sub false eHigh)
  have hsource_eq : a + low = b := by
    dsimp [low]
    linarith
  have hb_unbounded : fmt.unboundedNormalizedSystem b :=
    ⟨false, fmt.minNormalMantissa, eHigh + 1,
      fmt.minNormalMantissa_normalized, rfl⟩
  have hb_range : fmt.finiteNormalRange b := by
    change fmt.finiteNormalRange (a + low) at hxy
    rwa [hsource_eq] at hxy
  have hb_norm : fmt.normalizedSystem b :=
    fmt.unboundedNormalizedSystem_normalizedSystem_of_finiteNormalRange
      hb_unbounded hb_range
  have hfin_source :
      fmt.finiteSystem
        (fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) := by
    change fmt.finiteSystem (a + low)
    rw [hsource_eq]
    exact Or.inr (Or.inl hb_norm)
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue false fmt.maxNormalMantissa eHigh)
      (y := fmt.normalizedValue false mLow eLow)
      hfin_source)
/-- The positive max-mantissa exact-successor boundary branch has zero local
roundoff error, hence a finite representable error. -/
theorem finiteRoundToEvenOp_add_positive_max_sameSign_orderedExponent_error_finiteSystem_of_low_eq_ulp
    {fmt : FloatingPointFormat}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (hlow :
      fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  rw [
    finiteRoundToEvenOp_add_positive_max_sameSign_orderedExponent_eq_exact_of_low_eq_ulp
      hmLow hlow hxy]
  simpa using fmt.finiteSystem_zero
/-- Negative same-sign normalized ordered-exponent addition is exact at the
max-mantissa exponent boundary when the positive magnitude of the lower addend
is exactly one ulp at the higher exponent. -/
theorem finiteRoundToEvenOp_add_negative_max_sameSign_orderedExponent_eq_exact_of_low_eq_ulp
    {fmt : FloatingPointFormat}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (_hmLow : fmt.normalizedMantissa mLow)
    (hlow :
      fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue true fmt.maxNormalMantissa eHigh)
        (fmt.normalizedValue true mLow eLow) =
      fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
        fmt.normalizedValue true mLow eLow := by
  let a := fmt.normalizedValue true fmt.maxNormalMantissa eHigh
  let b := fmt.normalizedValue true fmt.minNormalMantissa (eHigh + 1)
  let lowNeg := fmt.normalizedValue true mLow eLow
  have hb_sub_a : b - a = -fmt.ulpAtExponent eHigh := by
    dsimp [a, b]
    simpa [ulpAtExponent, signValue] using
      (fmt.normalizedValue_boundary_sub true eHigh)
  have hlowNeg : lowNeg = -fmt.ulpAtExponent eHigh := by
    dsimp [lowNeg]
    rw [fmt.normalizedValue_true_eq_neg_false, hlow]
  have hsource_eq : a + lowNeg = b := by
    linarith
  have hb_unbounded : fmt.unboundedNormalizedSystem b :=
    ⟨true, fmt.minNormalMantissa, eHigh + 1,
      fmt.minNormalMantissa_normalized, rfl⟩
  have hb_range : fmt.finiteNormalRange b := by
    change fmt.finiteNormalRange (a + lowNeg) at hxy
    rwa [hsource_eq] at hxy
  have hb_norm : fmt.normalizedSystem b :=
    fmt.unboundedNormalizedSystem_normalizedSystem_of_finiteNormalRange
      hb_unbounded hb_range
  have hfin_source :
      fmt.finiteSystem
        (fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) := by
    change fmt.finiteSystem (a + lowNeg)
    rw [hsource_eq]
    exact Or.inr (Or.inl hb_norm)
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue true fmt.maxNormalMantissa eHigh)
      (y := fmt.normalizedValue true mLow eLow)
      hfin_source)
/-- The negative max-mantissa exact-successor boundary branch has zero local
roundoff error, hence a finite representable error. -/
theorem finiteRoundToEvenOp_add_negative_max_sameSign_orderedExponent_error_finiteSystem_of_low_eq_ulp
    {fmt : FloatingPointFormat}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (hlow :
      fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  rw [
    finiteRoundToEvenOp_add_negative_max_sameSign_orderedExponent_eq_exact_of_low_eq_ulp
      hmLow hlow hxy]
  simpa using fmt.finiteSystem_zero
/-- Positive same-sign normalized ordered-exponent addition has finite local
roundoff error in the strict right half-cell boundary branch where the high
operand is `maxNormalMantissa`.

The adjacent right endpoint is the smallest normalized mantissa in the next
binade.  If the lower operand lies strictly between one half ulp and one ulp at
the high exponent, source round-to-even selects that next-binade endpoint; the
residual is a finite scaled-integer difference on the lower operand lattice. -/
theorem sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
        fmt.normalizedValue false mLow eLow)
    (hulp :
      fmt.normalizedValue false mLow eLow < fmt.ulpAtExponent eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) - y) := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa eHigh
  let b := fmt.normalizedValue false fmt.minNormalMantissa (eHigh + 1)
  let low := fmt.normalizedValue false mLow eLow
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.normalizedValue_false_pos hmLow
  have hb_sub_a : b - a = fmt.ulpAtExponent eHigh := by
    dsimp [a, b]
    simpa [ulpAtExponent, signValue] using
      (fmt.normalizedValue_boundary_sub false eHigh)
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, eHigh, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have ha_lt_source : a < a + low := by
    linarith
  have hsource_lt_b : a + low < b := by
    linarith
  have hleft_abs : |(a + low) - a| = low := by
    have hsub : (a + low) - a = low := by ring
    rw [hsub, abs_of_pos hlow_pos]
  have hright_abs :
      |(a + low) - b| = fmt.ulpAtExponent eHigh - low := by
    have hsub : (a + low) - b = low - fmt.ulpAtExponent eHigh := by
      linarith
    have hneg : low - fmt.ulpAtExponent eHigh < 0 := by
      linarith
    rw [hsub, abs_of_neg hneg]
    ring
  have hrightCloser : |(a + low) - b| < |(a + low) - a| := by
    rw [hleft_abs, hright_abs]
    linarith
  have hy : y = b := by
    exact
      fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
        hpolicy hadj ⟨ha_lt_source, hsource_lt_b⟩ hrightCloser
  have hulp_lattice :
      fmt.ulpAtExponent eHigh =
        ((fmt.beta ^ fmt.t : ℕ) : ℝ) *
          fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
    calc
      fmt.ulpAtExponent eHigh =
          fmt.betaR ^ (eLow + (fmt.t : ℤ) - (fmt.t : ℤ)) := by
        rw [ulpAtExponent, hexp]
      _ = fmt.betaR ^ eLow := by
        congr 1
        ring
      _ = fmt.betaR ^ fmt.t * fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
        exact (fmt.mantissaBound_scale_eq eLow).symm
      _ = ((fmt.beta ^ fmt.t : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
        simp [betaR, Nat.cast_pow]
  have hdiff :
      (((mLow : ℤ) - ((fmt.beta ^ fmt.t : ℕ) : ℤ)).natAbs <
        fmt.beta ^ fmt.t) := by
    have hm_lt : mLow < fmt.beta ^ fmt.t := hmLow.2
    have hm_pos : 0 < mLow := fmt.normalizedMantissa_pos hmLow
    have hgap_nonneg :
        0 ≤ ((fmt.beta ^ fmt.t : ℕ) : ℤ) - (mLow : ℤ) := by
      omega
    have hnatabs :
        ((((mLow : ℤ) - ((fmt.beta ^ fmt.t : ℕ) : ℤ)).natAbs : ℤ) =
          ((fmt.beta ^ fmt.t : ℕ) : ℤ) - (mLow : ℤ)) := by
      rw [← Int.natAbs_neg]
      have h := Int.natAbs_of_nonneg hgap_nonneg
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    omega
  have hfin_scaled :
      fmt.finiteSystem
        (fmt.signValue false * ((mLow : ℤ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ)) -
          fmt.signValue false * ((((fmt.beta ^ fmt.t : ℕ) : ℤ) : ℝ)) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) :=
    fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := false) (k := (mLow : ℤ))
      (l := ((fmt.beta ^ fmt.t : ℕ) : ℤ)) (e := eLow) heLow hdiff
  rw [hy]
  change fmt.finiteSystem ((a + low) - b)
  convert hfin_scaled using 1
  have hres : (a + low) - b = low - fmt.ulpAtExponent eHigh := by
    linarith
  rw [hres, hulp_lattice]
  dsimp [low]
  simp [normalizedValue, signValue]
/-- Operation-level positive same-sign normalized ordered-exponent addition has
finite representable local roundoff error in the strict right half-cell
boundary branch where the high operand is `maxNormalMantissa`. -/
theorem finiteRoundToEvenOp_add_positive_max_sameSign_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
        fmt.normalizedValue false mLow eLow)
    (hulp :
      fmt.normalizedValue false mLow eLow < fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hmLow heLow hexp hhalf hulp hpolicy
/-- Negative same-sign normalized ordered-exponent addition has finite local
roundoff error in the strict right half-cell boundary branch by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_max_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
        fmt.normalizedValue false mLow eLow)
    (hulp :
      fmt.normalizedValue false mLow eLow < fmt.ulpAtExponent eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) - y) := by
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    rw [add_comm]
    convert hneg using 1
    simp [fmt.normalizedValue_true_eq_neg_false]
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false fmt.maxNormalMantissa eHigh +
            fmt.normalizedValue false mLow eLow) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hmLow heLow hexp hhalf hulp hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [fmt.normalizedValue_true_eq_neg_false]
  ring
/-- Operation-level negative same-sign normalized ordered-exponent addition has
finite representable local roundoff error in the strict right half-cell
boundary branch where the high operand is `maxNormalMantissa`. -/
theorem finiteRoundToEvenOp_add_negative_max_sameSign_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
        fmt.normalizedValue false mLow eLow)
    (hulp :
      fmt.normalizedValue false mLow eLow < fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_max_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hbeta ht hmLow heLow hexp hhalf hulp hpolicy
/-- Positive same-sign normalized ordered-exponent addition has finite local
roundoff error at the exact half-ulp tie around the high operand.

Round-to-even may choose either adjacent endpoint at the tie; the residual is
the lower finite operand or its negation, hence finite representable in either
case. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow) - y) := by
  let a := fmt.normalizedValue false mHigh eHigh
  let b := fmt.normalizedValue false (mHigh + 1) eHigh
  let low := fmt.normalizedValue false mLow eLow
  have hlow_eq : low = (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh := by
    simpa [low] using hlow
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.normalizedValue_false_pos hmLow
  have hulp_pos : 0 < fmt.ulpAtExponent eHigh := fmt.ulpAtExponent_pos eHigh
  have hlow_lt_ulp : low < fmt.ulpAtExponent eHigh := by
    rw [hlow_eq]
    linarith
  have hb_sub_a : b - a = fmt.ulpAtExponent eHigh := by
    dsimp [a, b]
    simpa [ulpAtExponent, signValue] using
      (fmt.normalizedValue_succ_sub_sameExponent false mHigh eHigh)
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, mHigh, eHigh, hmHigh, hmHighSucc, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hsource_between : a ≤ a + low ∧ a + low ≤ b := by
    constructor <;> linarith
  have hlow_fin : fmt.finiteSystem low :=
    Or.inr (Or.inl ⟨false, mLow, eLow, hmLow, heLow, rfl⟩)
  rcases
      fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
        hpolicy hadj hsource_between with hy | hy
  · rw [hy]
    convert hlow_fin using 1
    dsimp [a, low]
    ring
  · rw [hy]
    have hfin_neg := fmt.finiteSystem_neg hlow_fin
    convert hfin_neg using 1
    have hres : (a + low) - b = -low := by
      linarith
    rw [hres]
/-- Operation-level positive same-sign normalized ordered-exponent addition
has finite representable local roundoff error at the exact half-ulp tie. -/
theorem finiteRoundToEvenOp_add_positive_sameSign_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
      hmHigh hmHighSucc hmLow heLow hlow hpolicy
/-- Negative same-sign normalized ordered-exponent addition has finite local
roundoff error at the exact half-ulp tie by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue true mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue true mLow eLow) - y) := by
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    rw [add_comm]
    convert hneg using 1
    simp [fmt.normalizedValue_true_eq_neg_false]
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false mHigh eHigh +
            fmt.normalizedValue false mLow eLow) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
      hmHigh hmHighSucc hmLow heLow hlow hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [fmt.normalizedValue_true_eq_neg_false]
  ring
/-- Operation-level negative same-sign normalized ordered-exponent addition
has finite representable local roundoff error at the exact half-ulp tie. -/
theorem finiteRoundToEvenOp_add_negative_sameSign_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow =
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue true mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
      hbeta ht hmHigh hmHighSucc hmLow heLow hlow hpolicy
/-- Positive same-sign normalized ordered-exponent addition has finite local
roundoff error in the strict right half-cell branch around the high operand.

If the lower addend lies strictly between half an ulp and one ulp at the high
exponent, and that high ulp is on the lower operand's scaled-integer lattice,
source round-to-even selects the high operand's same-exponent successor.  The
local residual is the signed lattice gap between the lower operand and one high
ulp, hence is finite representable. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
        fmt.normalizedValue false mLow eLow)
    (hulp :
      fmt.normalizedValue false mLow eLow < fmt.ulpAtExponent eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow) - y) := by
  let a := fmt.normalizedValue false mHigh eHigh
  let b := fmt.normalizedValue false (mHigh + 1) eHigh
  let low := fmt.normalizedValue false mLow eLow
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.normalizedValue_false_pos hmLow
  have hb_sub_a : b - a = fmt.ulpAtExponent eHigh := by
    dsimp [a, b]
    simpa [ulpAtExponent, signValue] using
      (fmt.normalizedValue_succ_sub_sameExponent false mHigh eHigh)
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, mHigh, eHigh, hmHigh, hmHighSucc, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have ha_lt_source : a < a + low := by
    linarith
  have hsource_lt_b : a + low < b := by
    linarith
  have hleft_abs : |(a + low) - a| = low := by
    have hsub : (a + low) - a = low := by ring
    rw [hsub, abs_of_pos hlow_pos]
  have hright_abs :
      |(a + low) - b| = fmt.ulpAtExponent eHigh - low := by
    have hsub : (a + low) - b = low - fmt.ulpAtExponent eHigh := by
      linarith
    have hneg : low - fmt.ulpAtExponent eHigh < 0 := by
      linarith
    rw [hsub, abs_of_neg hneg]
    ring
  have hrightCloser : |(a + low) - b| < |(a + low) - a| := by
    rw [hleft_abs, hright_abs]
    linarith
  have hy : y = b := by
    exact
      fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
        hpolicy hadj ⟨ha_lt_source, hsource_lt_b⟩ hrightCloser
  have hulp_lattice :
      fmt.ulpAtExponent eHigh =
        ((fmt.beta ^ fmt.t : ℕ) : ℝ) *
          fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
    calc
      fmt.ulpAtExponent eHigh =
          fmt.betaR ^ (eLow + (fmt.t : ℤ) - (fmt.t : ℤ)) := by
        rw [ulpAtExponent, hexp]
      _ = fmt.betaR ^ eLow := by
        congr 1
        ring
      _ = fmt.betaR ^ fmt.t * fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
        exact (fmt.mantissaBound_scale_eq eLow).symm
      _ = ((fmt.beta ^ fmt.t : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
        simp [betaR, Nat.cast_pow]
  have hdiff :
      (((mLow : ℤ) - ((fmt.beta ^ fmt.t : ℕ) : ℤ)).natAbs <
        fmt.beta ^ fmt.t) := by
    have hm_lt : mLow < fmt.beta ^ fmt.t := hmLow.2
    have hm_pos : 0 < mLow := fmt.normalizedMantissa_pos hmLow
    have hgap_nonneg :
        0 ≤ ((fmt.beta ^ fmt.t : ℕ) : ℤ) - (mLow : ℤ) := by
      omega
    have hnatabs :
        ((((mLow : ℤ) - ((fmt.beta ^ fmt.t : ℕ) : ℤ)).natAbs : ℤ) =
          ((fmt.beta ^ fmt.t : ℕ) : ℤ) - (mLow : ℤ)) := by
      rw [← Int.natAbs_neg]
      have h := Int.natAbs_of_nonneg hgap_nonneg
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    omega
  have hfin_scaled :
      fmt.finiteSystem
        (fmt.signValue false * ((mLow : ℤ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ)) -
          fmt.signValue false * ((((fmt.beta ^ fmt.t : ℕ) : ℤ) : ℝ)) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) :=
    fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := false) (k := (mLow : ℤ))
      (l := ((fmt.beta ^ fmt.t : ℕ) : ℤ)) (e := eLow) heLow hdiff
  rw [hy]
  change fmt.finiteSystem ((a + low) - b)
  convert hfin_scaled using 1
  have hres : (a + low) - b = low - fmt.ulpAtExponent eHigh := by
    linarith
  rw [hres, hulp_lattice]
  dsimp [low]
  simp [normalizedValue, signValue]
/-- Operation-level positive same-sign normalized ordered-exponent addition
has finite representable local roundoff error in the strict right half-cell
branch. -/
theorem finiteRoundToEvenOp_add_positive_sameSign_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
        fmt.normalizedValue false mLow eLow)
    (hulp :
      fmt.normalizedValue false mLow eLow < fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hmHigh hmHighSucc hmLow heLow hexp hhalf hulp hpolicy
/-- Negative same-sign normalized ordered-exponent addition has finite local
roundoff error in the strict right half-cell branch by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
        fmt.normalizedValue false mLow eLow)
    (hulp :
      fmt.normalizedValue false mLow eLow < fmt.ulpAtExponent eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue true mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue true mLow eLow) - y) := by
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    rw [add_comm]
    convert hneg using 1
    simp [fmt.normalizedValue_true_eq_neg_false]
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false mHigh eHigh +
            fmt.normalizedValue false mLow eLow) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hmHigh hmHighSucc hmLow heLow hexp hhalf hulp hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [fmt.normalizedValue_true_eq_neg_false]
  ring
/-- Operation-level negative same-sign normalized ordered-exponent addition
has finite representable local roundoff error in the strict right half-cell
branch. -/
theorem finiteRoundToEvenOp_add_negative_sameSign_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
        fmt.normalizedValue false mLow eLow)
    (hulp :
      fmt.normalizedValue false mLow eLow < fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue true mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hbeta ht hmHigh hmHighSucc hmLow heLow hexp hhalf hulp hpolicy
/-- Positive same-sign normalized ordered-exponent addition is exact when the
lower addend is exactly one ulp at the higher exponent and the high mantissa has
a same-exponent successor.  This is the endpoint case immediately above the
strict left half-cell branch. -/
theorem finiteRoundToEvenOp_add_positive_sameSign_orderedExponent_eq_exact_of_low_eq_ulp
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (_hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (_hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (hlow :
      fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue false mHigh eHigh)
        (fmt.normalizedValue false mLow eLow) =
      fmt.normalizedValue false mHigh eHigh +
        fmt.normalizedValue false mLow eLow := by
  let a := fmt.normalizedValue false mHigh eHigh
  let b := fmt.normalizedValue false (mHigh + 1) eHigh
  let low := fmt.normalizedValue false mLow eLow
  have hb_sub_a : b - a = fmt.ulpAtExponent eHigh := by
    dsimp [a, b]
    simpa [ulpAtExponent, signValue] using
      (fmt.normalizedValue_succ_sub_sameExponent false mHigh eHigh)
  have hsource_eq : a + low = b := by
    dsimp [low]
    linarith
  have hfin_b : fmt.finiteSystem b :=
    Or.inr (Or.inl ⟨false, mHigh + 1, eHigh, hmHighSucc, heHigh, rfl⟩)
  have hfin_source :
      fmt.finiteSystem
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow) := by
    change fmt.finiteSystem (a + low)
    rw [hsource_eq]
    exact hfin_b
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue false mHigh eHigh)
      (y := fmt.normalizedValue false mLow eLow)
      hfin_source)
/-- The exact-successor ordered-exponent add branch has zero local roundoff
error, hence a finite representable error. -/
theorem finiteRoundToEvenOp_add_positive_sameSign_orderedExponent_error_finiteSystem_of_low_eq_ulp
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (hlow :
      fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  rw [
    finiteRoundToEvenOp_add_positive_sameSign_orderedExponent_eq_exact_of_low_eq_ulp
      hmHigh hmHighSucc hmLow heHigh hlow]
  simpa using fmt.finiteSystem_zero
/-- Negative same-sign normalized ordered-exponent addition is exact when the
positive magnitude of the lower addend is exactly one ulp at the higher
exponent and the high mantissa has a same-exponent successor. -/
theorem finiteRoundToEvenOp_add_negative_sameSign_orderedExponent_eq_exact_of_low_eq_ulp
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (_hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (_hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (hlow :
      fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue true mHigh eHigh)
        (fmt.normalizedValue true mLow eLow) =
      fmt.normalizedValue true mHigh eHigh +
        fmt.normalizedValue true mLow eLow := by
  let a := fmt.normalizedValue true mHigh eHigh
  let b := fmt.normalizedValue true (mHigh + 1) eHigh
  let low := fmt.normalizedValue false mLow eLow
  let lowNeg := fmt.normalizedValue true mLow eLow
  have hb_sub_a : b - a = -fmt.ulpAtExponent eHigh := by
    dsimp [a, b]
    simpa [ulpAtExponent, signValue] using
      (fmt.normalizedValue_succ_sub_sameExponent true mHigh eHigh)
  have hlowNeg : lowNeg = -fmt.ulpAtExponent eHigh := by
    dsimp [lowNeg]
    rw [fmt.normalizedValue_true_eq_neg_false, hlow]
  have hsource_eq : a + lowNeg = b := by
    linarith
  have hfin_b : fmt.finiteSystem b :=
    Or.inr (Or.inl ⟨true, mHigh + 1, eHigh, hmHighSucc, heHigh, rfl⟩)
  have hfin_source :
      fmt.finiteSystem
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue true mLow eLow) := by
    change fmt.finiteSystem (a + lowNeg)
    rw [hsource_eq]
    exact hfin_b
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue true mHigh eHigh)
      (y := fmt.normalizedValue true mLow eLow)
      hfin_source)
/-- The negative exact-successor ordered-exponent add branch has zero local
roundoff error, hence a finite representable error. -/
theorem finiteRoundToEvenOp_add_negative_sameSign_orderedExponent_error_finiteSystem_of_low_eq_ulp
    {fmt : FloatingPointFormat}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (hlow :
      fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  rw [
    finiteRoundToEvenOp_add_negative_sameSign_orderedExponent_eq_exact_of_low_eq_ulp
      hmHigh hmHighSucc hmLow heHigh hlow]
  simpa using fmt.finiteSystem_zero
/-- Dispatcher for the same-sign normalized ordered-exponent low-cell split.

This packages the strict-left, half-ulp tie, strict-right, and exact-successor
branches for an ordinary high mantissa with a same-exponent successor.  The
strict-right branch keeps the explicit lower-lattice condition
`eHigh = eLow + t`. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_low_cell_cases
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hcell :
      fmt.normalizedValue false mLow eLow <
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        fmt.normalizedValue false mLow eLow =
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
            fmt.normalizedValue false mLow eLow ∧
          fmt.normalizedValue false mLow eLow <
            fmt.ulpAtExponent eHigh) ∨
        fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  rcases hcell with hlt | hrest
  · cases negative
    · exact
        fmt.finiteRoundToEvenOp_add_positive_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
          hmHigh hmHighSucc hmLow heLow hlt hxy
    · exact
        fmt.finiteRoundToEvenOp_add_negative_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
          hbeta ht hmHigh hmHighSucc hmLow heLow hlt hxy
  · rcases hrest with heq | hrest
    · cases negative
      · exact
          fmt.finiteRoundToEvenOp_add_positive_sameSign_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
            hmHigh hmHighSucc hmLow heLow heq hxy
      · exact
          fmt.finiteRoundToEvenOp_add_negative_sameSign_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
            hbeta ht hmHigh hmHighSucc hmLow heLow heq hxy
    · rcases hrest with hright | hulp
      · cases negative
        · exact
            fmt.finiteRoundToEvenOp_add_positive_sameSign_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
              hmHigh hmHighSucc hmLow heLow hexp hright.1 hright.2 hxy
        · exact
            fmt.finiteRoundToEvenOp_add_negative_sameSign_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
              hbeta ht hmHigh hmHighSucc hmLow heLow hexp hright.1 hright.2 hxy
      · cases negative
        · exact
            fmt.finiteRoundToEvenOp_add_positive_sameSign_orderedExponent_error_finiteSystem_of_low_eq_ulp
              hmHigh hmHighSucc hmLow heHigh hulp
        · exact
            fmt.finiteRoundToEvenOp_add_negative_sameSign_orderedExponent_error_finiteSystem_of_low_eq_ulp
              hmHigh hmHighSucc hmLow heHigh hulp
/-- Commuted dispatcher for the same-sign normalized ordered-exponent low-cell
split. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_low_cell_cases
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hcell :
      fmt.normalizedValue false mLow eLow <
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        fmt.normalizedValue false mLow eLow =
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
            fmt.normalizedValue false mLow eLow ∧
          fmt.normalizedValue false mLow eLow <
            fmt.ulpAtExponent eHigh) ∨
        fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
  have hxy_order :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) := by
    convert hxy using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue negative mHigh eHigh +
            fmt.normalizedValue negative mLow eLow) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.normalizedValue negative mHigh eHigh)
            (fmt.normalizedValue negative mLow eLow)) :=
    finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_low_cell_cases
      (fmt := fmt)
      hbeta ht hmHigh hmHighSucc hmLow heHigh heLow hexp hcell hxy_order
  have hop :
      fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh) =
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow) := by
    simp [finiteRoundToEvenOp, BasicOp.exact, add_comm]
  rw [hop]
  convert hfin using 1
  ring
/-- Dispatcher for the same-sign max-mantissa normalized ordered-exponent
low-cell split. -/
theorem finiteRoundToEvenOp_add_max_sameSign_orderedExponent_error_finiteSystem_of_low_cell_cases
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hcell :
      fmt.normalizedValue false mLow eLow <
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        fmt.normalizedValue false mLow eLow =
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
            fmt.normalizedValue false mLow eLow ∧
          fmt.normalizedValue false mLow eLow <
            fmt.ulpAtExponent eHigh) ∨
        fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  rcases hcell with hlt | hrest
  · cases negative
    · exact
        fmt.finiteRoundToEvenOp_add_positive_max_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
          hmLow heLow hlt hxy
    · exact
        fmt.finiteRoundToEvenOp_add_negative_max_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
          hbeta ht hmLow heLow hlt hxy
  · rcases hrest with heq | hrest
    · cases negative
      · exact
          fmt.finiteRoundToEvenOp_add_positive_max_sameSign_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
            hmLow heLow heq hxy
      · exact
          fmt.finiteRoundToEvenOp_add_negative_max_sameSign_orderedExponent_error_finiteSystem_of_low_eq_half_ulp
            hbeta ht hmLow heLow heq hxy
    · rcases hrest with hright | hulp
      · cases negative
        · exact
            fmt.finiteRoundToEvenOp_add_positive_max_sameSign_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
              hmLow heLow hexp hright.1 hright.2 hxy
        · exact
            fmt.finiteRoundToEvenOp_add_negative_max_sameSign_orderedExponent_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
              hbeta ht hmLow heLow hexp hright.1 hright.2 hxy
      · cases negative
        · exact
            fmt.finiteRoundToEvenOp_add_positive_max_sameSign_orderedExponent_error_finiteSystem_of_low_eq_ulp
              hmLow hulp hxy
        · exact
            fmt.finiteRoundToEvenOp_add_negative_max_sameSign_orderedExponent_error_finiteSystem_of_low_eq_ulp
              hmLow hulp hxy
/-- Commuted dispatcher for the same-sign max-mantissa normalized
ordered-exponent low-cell split. -/
theorem finiteRoundToEvenOp_add_max_sameSign_orderedExponent_comm_error_finiteSystem_of_low_cell_cases
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hcell :
      fmt.normalizedValue false mLow eLow <
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        fmt.normalizedValue false mLow eLow =
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
            fmt.normalizedValue false mLow eLow ∧
          fmt.normalizedValue false mLow eLow <
            fmt.ulpAtExponent eHigh) ∨
        fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative fmt.maxNormalMantissa eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)) := by
  have hxy_order :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue negative mLow eLow) := by
    convert hxy using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue negative fmt.maxNormalMantissa eHigh +
            fmt.normalizedValue negative mLow eLow) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)
            (fmt.normalizedValue negative mLow eLow)) :=
    finiteRoundToEvenOp_add_max_sameSign_orderedExponent_error_finiteSystem_of_low_cell_cases
      (fmt := fmt)
      hbeta ht hmLow heLow hexp hcell hxy_order
  have hop :
      fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh) =
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue negative mLow eLow) := by
    simp [finiteRoundToEvenOp, BasicOp.exact, add_comm]
  rw [hop]
  convert hfin using 1
  ring
/-- At exactly one precision-width exponent gap in base `2`, a normalized lower
operand falls into the half-ulp/right-half low-cell split around the high
operand.

The minimum normalized mantissa is exactly one half ulp at the higher exponent;
every larger normalized mantissa is strictly between half an ulp and one ulp.
This derives the source-cell hypothesis used by the ordered-exponent C4.4/
FastTwoSum low-cell dispatcher. -/
theorem normalizedValue_false_low_cell_cases_of_exponent_gap_eq_t
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ)) :
    fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
      fmt.normalizedValue false mLow eLow =
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
      ((1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
          fmt.normalizedValue false mLow eLow ∧
        fmt.normalizedValue false mLow eLow <
          fmt.ulpAtExponent eHigh) ∨
      fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh := by
  have hlow_pos : 0 < fmt.normalizedValue false mLow eLow :=
    fmt.normalizedValue_false_pos hmLow
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  have hbetaR : fmt.betaR = 2 := by
    simp [betaR, hbeta]
  have hulp_eq : fmt.ulpAtExponent eHigh = fmt.betaR ^ eLow := by
    rw [ulpAtExponent, hexp]
    congr 1
    ring
  have hz :
      fmt.betaR ^ eLow = fmt.betaR ^ (eLow - 1) * 2 := by
    calc
      fmt.betaR ^ eLow =
          fmt.betaR ^ ((eLow - 1) + (1 : ℤ)) := by
        congr 1
        ring
      _ = fmt.betaR ^ (eLow - 1) * fmt.betaR ^ (1 : ℤ) := by
        rw [zpow_add₀ hbase]
      _ = fmt.betaR ^ (eLow - 1) * 2 := by
        rw [zpow_one, hbetaR]
  have hhalf_eq_pow :
      (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh =
        fmt.betaR ^ (eLow - 1) := by
    rw [hulp_eq, hz]
    ring
  have hhalf_eq_min :
      (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh =
        fmt.normalizedValue false fmt.minNormalMantissa eLow := by
    rw [hhalf_eq_pow, fmt.normalizedValue_false_minNormalMantissa_eq]
  have hlow_lt_ulp :
      fmt.normalizedValue false mLow eLow < fmt.ulpAtExponent eHigh := by
    have h := fmt.normalizedValue_abs_lt_beta_pow
      (negative := false) (e := eLow) hmLow
    rw [hulp_eq]
    simpa [abs_of_pos hlow_pos] using h
  by_cases hmin : mLow = fmt.minNormalMantissa
  · right
    left
    rw [hmin]
    exact hhalf_eq_min.symm
  · right
    right
    left
    constructor
    · rw [hhalf_eq_min]
      have hmin_ne : fmt.minNormalMantissa ≠ mLow := by
        intro h
        exact hmin h.symm
      exact
        (fmt.normalizedValue_sameExponent_lt_iff_false
          fmt.minNormalMantissa mLow eLow).2
          (lt_of_le_of_ne hmLow.1 hmin_ne)
    · exact hlow_lt_ulp
/-- Positive normalized opposite-sign predecessor low-cell split derived from
the exact precision-window exponent gap. -/
theorem finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hgap : eHigh = eLow + (fmt.t : ℤ))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hcell :
      fmt.normalizedValue false mLow eLow <
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        fmt.normalizedValue false mLow eLow =
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
            fmt.normalizedValue false mLow eLow ∧
          fmt.normalizedValue false mLow eLow <
            fmt.ulpAtExponent eHigh) ∨
        fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh :=
    fmt.normalizedValue_false_low_cell_cases_of_exponent_gap_eq_t
      hbeta hmLow hgap
  exact
    fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_low_cell_cases
      hmHigh hneHighMin hmLow heHigh heLow hgap hcell hxy
/-- Negative normalized opposite-sign predecessor low-cell split derived from
the exact precision-window exponent gap. -/
theorem finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hgap : eHigh = eLow + (fmt.t : ℤ))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hcell :
      fmt.normalizedValue false mLow eLow <
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        fmt.normalizedValue false mLow eLow =
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
            fmt.normalizedValue false mLow eLow ∧
          fmt.normalizedValue false mLow eLow <
            fmt.ulpAtExponent eHigh) ∨
        fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh :=
    fmt.normalizedValue_false_low_cell_cases_of_exponent_gap_eq_t
      hbeta hmLow hgap
  exact
    fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_low_cell_cases
      hbeta ht hmHigh hneHighMin hmLow heHigh heLow hgap hcell hxy
/-- Operation-level positive high plus negative low normalized addition has
finite local error in either the exact-or-one-guard aligned-difference range
or the precision-window-or-larger exponent-gap range, provided the high
mantissa has a same-exponent predecessor. -/
theorem finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_two_mul_or_exponent_gap_ge_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hcase :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
          2 * fmt.beta ^ fmt.t ∨
        eLow + (fmt.t : ℤ) ≤ eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  rcases hcase with hhi | hgap
  · exact
      fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_two_mul_mantissaBound
        hbeta hmHigh hmLow heHigh heLow hle hcoeff_le hhi hxy
  · rcases lt_or_eq_of_le hgap with hlt | heq
    · exact
        fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_exponent_gap_gt_t
          hbeta hmHigh hneHighMin hmLow heLow hlt hxy
    · exact
        fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t
          hbeta hmHigh hneHighMin hmLow heHigh heLow heq.symm hxy
/-- Operation-level negative high plus positive low normalized addition has
finite local error in either the exact-or-one-guard aligned-difference range
or the precision-window-or-larger exponent-gap range, provided the high
mantissa has a same-exponent predecessor. -/
theorem finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_two_mul_or_exponent_gap_ge_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hcase :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
          2 * fmt.beta ^ fmt.t ∨
        eLow + (fmt.t : ℤ) ≤ eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  rcases hcase with hhi | hgap
  · exact
      fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_two_mul_mantissaBound
        hbeta hmHigh hmLow heHigh heLow hle hcoeff_le hhi hxy
  · rcases lt_or_eq_of_le hgap with hlt | heq
    · exact
        fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_exponent_gap_gt_t
          hbeta ht hmHigh hneHighMin hmLow heLow hlt hxy
    · exact
        fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t
          hbeta ht hmHigh hneHighMin hmLow heHigh heLow heq.symm hxy
/-- Operation-level positive high plus negative low normalized addition has
finite local error throughout the non-minimum high-mantissa base-2 ordered-
exponent split. -/
theorem finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_baseTwo_nonMinHigh
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false mHigh eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  by_cases hcase :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
          2 * fmt.beta ^ fmt.t ∨
        eLow + (fmt.t : ℤ) ≤ eHigh
  · exact
      fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_two_mul_or_exponent_gap_ge_t
        hbeta hmHigh hneHighMin hmLow heHigh heLow hle hcoeff_le hcase hxy
  · have hlo :
        2 * fmt.beta ^ fmt.t ≤
          mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow := by
      exact le_of_not_gt (fun hk => hcase (Or.inl hk))
    have hwindow : eLow + (fmt.t : ℤ) > eHigh := by
      exact lt_of_not_ge (fun hgap => hcase (Or.inr hgap))
    exact
      fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_multiGuardComplementaryRegion
        hbeta hmHigh hmLow heHigh heLow hle hcoeff_le hlo hwindow hxy
/-- Operation-level negative high plus positive low normalized addition has
finite local error throughout the non-minimum high-mantissa base-2 ordered-
exponent split. -/
theorem finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_baseTwo_nonMinHigh
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true mHigh eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  by_cases hcase :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
          2 * fmt.beta ^ fmt.t ∨
        eLow + (fmt.t : ℤ) ≤ eHigh
  · exact
      fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_two_mul_or_exponent_gap_ge_t
        hbeta ht hmHigh hneHighMin hmLow heHigh heLow hle hcoeff_le hcase
        hxy
  · have hlo :
        2 * fmt.beta ^ fmt.t ≤
          mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow := by
      exact le_of_not_gt (fun hk => hcase (Or.inl hk))
    have hwindow : eLow + (fmt.t : ℤ) > eHigh := by
      exact lt_of_not_ge (fun hgap => hcase (Or.inr hgap))
    exact
      fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_multiGuardComplementaryRegion
        hbeta hmHigh hmLow heHigh heLow hle hcoeff_le hlo hwindow hxy
/-- Positive minimum-mantissa normalized opposite-sign boundary predecessor
low-cell split derived from the exact precision-window exponent gap. -/
theorem finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t_pred
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hgap : eHigh - 1 = eLow + (fmt.t : ℤ))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hcell :
      fmt.normalizedValue false mLow eLow <
          (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) ∨
        fmt.normalizedValue false mLow eLow =
          (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) <
            fmt.normalizedValue false mLow eLow ∧
          fmt.normalizedValue false mLow eLow <
            fmt.ulpAtExponent (eHigh - 1)) ∨
        fmt.normalizedValue false mLow eLow =
          fmt.ulpAtExponent (eHigh - 1) :=
    fmt.normalizedValue_false_low_cell_cases_of_exponent_gap_eq_t
      hbeta hmLow hgap
  exact
    fmt.finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_pred_low_cell_cases
      hmLow heLow hgap hcell hxy
/-- Negative minimum-mantissa normalized opposite-sign boundary predecessor
low-cell split derived from the exact precision-window exponent gap. -/
theorem finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t_pred
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hgap : eHigh - 1 = eLow + (fmt.t : ℤ))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hcell :
      fmt.normalizedValue false mLow eLow <
          (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) ∨
        fmt.normalizedValue false mLow eLow =
          (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) <
            fmt.normalizedValue false mLow eLow ∧
          fmt.normalizedValue false mLow eLow <
            fmt.ulpAtExponent (eHigh - 1)) ∨
        fmt.normalizedValue false mLow eLow =
          fmt.ulpAtExponent (eHigh - 1) :=
    fmt.normalizedValue_false_low_cell_cases_of_exponent_gap_eq_t
      hbeta hmLow hgap
  exact
    fmt.finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_pred_low_cell_cases
      hbeta ht hmLow heLow hgap hcell hxy
/-- Operation-level positive minimum high plus negative low normalized addition
has finite local error in either the exact-or-one-guard aligned-difference
range or the predecessor precision-window-or-larger range.

This is the minimum-mantissa companion to the ordinary non-minimum high
dispatcher, but its large-alignment alternative is stated relative to the
boundary predecessor exponent `eHigh - 1`.  The remaining binade-boundary
complement `eLow + t = eHigh` is intentionally not claimed here. -/
theorem finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_two_mul_or_pred_exponent_gap_ge_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ fmt.minNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hcase :
      fmt.minNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
          2 * fmt.beta ^ fmt.t ∨
        eLow + (fmt.t : ℤ) ≤ eHigh - 1)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  rcases hcase with hhi | hgap
  · exact
      fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_two_mul_mantissaBound
        hbeta fmt.minNormalMantissa_normalized hmLow heHigh heLow hle
        hcoeff_le hhi hxy
  · rcases lt_or_eq_of_le hgap with hlt | heq
    · exact
        fmt.finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_exponent_gap_gt_t_pred
          hbeta hmLow heLow hlt hxy
    · exact
        fmt.finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t_pred
          hbeta hmLow heLow heq.symm hxy
/-- Operation-level negative minimum high plus positive low normalized addition
has finite local error in either the exact-or-one-guard aligned-difference
range or the predecessor precision-window-or-larger range. -/
theorem finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_two_mul_or_pred_exponent_gap_ge_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ fmt.minNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hcase :
      fmt.minNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
          2 * fmt.beta ^ fmt.t ∨
        eLow + (fmt.t : ℤ) ≤ eHigh - 1)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  rcases hcase with hhi | hgap
  · exact
      fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_two_mul_mantissaBound
        hbeta fmt.minNormalMantissa_normalized hmLow heHigh heLow hle
        hcoeff_le hhi hxy
  · rcases lt_or_eq_of_le hgap with hlt | heq
    · exact
        fmt.finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_exponent_gap_gt_t_pred
          hbeta ht hmLow heLow hlt hxy
    · exact
        fmt.finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t_pred
          hbeta ht hmLow heLow heq.symm hxy
/-- At the minimum high mantissa and exact binade boundary `eHigh = eLow + t`,
the aligned difference coefficient is below the two-precision multi-guard
ceiling.

This supplies the upper bound missing from the ordinary complementary-region
wrapper, whose exponent-window hypothesis is strict. -/
theorem alignedDiffCoeff_minNormalMantissa_lt_two_precision_bound_of_exponent_gap_eq_t
    {fmt : FloatingPointFormat}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hgap : eHigh = eLow + (fmt.t : ℤ)) :
    fmt.minNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
      fmt.beta ^ (2 * fmt.t) := by
  have hshift : Int.toNat (eHigh - eLow) = fmt.t := by
    have hdiff : eHigh - eLow = (fmt.t : ℤ) := by omega
    rw [hdiff]
    simp
  have hprod :
      fmt.minNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow) <
        fmt.beta ^ (2 * fmt.t) := by
    rw [hshift]
    unfold minNormalMantissa
    rw [← pow_add]
    have hexp_lt : fmt.t - 1 + fmt.t < 2 * fmt.t := by
      have htpos := fmt.t_pos
      have hsub_lt : fmt.t - 1 < fmt.t := Nat.sub_lt htpos (by norm_num)
      have hsum_lt : fmt.t - 1 + fmt.t < fmt.t + fmt.t :=
        Nat.add_lt_add_right hsub_lt fmt.t
      simpa [two_mul] using hsum_lt
    exact Nat.pow_lt_pow_right fmt.one_lt_beta hexp_lt
  exact lt_of_le_of_lt (Nat.sub_le _ _) hprod
/-- Positive minimum high plus negative low normalized addition has finite
local error in the complementary multi-guard binade-boundary case
`eHigh = eLow + t`. -/
theorem finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t_multiGuard
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ fmt.minNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        fmt.minNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow)
    (hgap : eHigh = eLow + (fmt.t : ℤ))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  have hhi :
      fmt.minNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ (2 * fmt.t) :=
    fmt.alignedDiffCoeff_minNormalMantissa_lt_two_precision_bound_of_exponent_gap_eq_t
      (mLow := mLow) hgap
  exact
    fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_multiGuardCoefficientBounds
      hbeta fmt.minNormalMantissa_normalized hmLow heHigh heLow hle
      hcoeff_le hlo hhi hxy
/-- Negative minimum high plus positive low normalized addition has finite
local error in the complementary multi-guard binade-boundary case
`eHigh = eLow + t`. -/
theorem finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t_multiGuard
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ fmt.minNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        fmt.minNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow)
    (hgap : eHigh = eLow + (fmt.t : ℤ))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  have hhi :
      fmt.minNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ (2 * fmt.t) :=
    fmt.alignedDiffCoeff_minNormalMantissa_lt_two_precision_bound_of_exponent_gap_eq_t
      (mLow := mLow) hgap
  exact
    fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_multiGuardCoefficientBounds
      hbeta fmt.minNormalMantissa_normalized hmLow heHigh heLow hle
      hcoeff_le hlo hhi hxy
/-- Operation-level positive minimum high plus negative low normalized addition
has finite local error throughout the base-2 ordered-exponent split.

The proof combines the exact/one-guard branch, the predecessor-window branch,
the ordinary complementary multi-guard window, and the remaining binade-boundary
multi-guard case `eHigh = eLow + t`. -/
theorem finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ fmt.minNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue true mLow eLow)) := by
  by_cases hcase :
      fmt.minNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
          2 * fmt.beta ^ fmt.t ∨
        eLow + (fmt.t : ℤ) ≤ eHigh - 1
  · exact
      fmt.finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_two_mul_or_pred_exponent_gap_ge_t
        hbeta hmLow heHigh heLow hle hcoeff_le hcase hxy
  · have hlo :
        2 * fmt.beta ^ fmt.t ≤
          fmt.minNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow) -
            mLow := by
      exact le_of_not_gt (fun hk => hcase (Or.inl hk))
    have hnot_pred : ¬ eLow + (fmt.t : ℤ) ≤ eHigh - 1 := by
      intro hpred
      exact hcase (Or.inr hpred)
    have hboundary_le : eHigh ≤ eLow + (fmt.t : ℤ) := by
      omega
    rcases lt_or_eq_of_le hboundary_le with hwindow | hgap
    · exact
        fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_multiGuardComplementaryRegion
          hbeta fmt.minNormalMantissa_normalized hmLow heHigh heLow hle
          hcoeff_le hlo hwindow hxy
    · exact
        fmt.finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t_multiGuard
          hbeta hmLow heHigh heLow hle hcoeff_le hlo hgap hxy
/-- Operation-level negative minimum high plus positive low normalized addition
has finite local error throughout the base-2 ordered-exponent split. -/
theorem finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ fmt.minNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.normalizedValue false mLow eLow)) := by
  by_cases hcase :
      fmt.minNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
          2 * fmt.beta ^ fmt.t ∨
        eLow + (fmt.t : ℤ) ≤ eHigh - 1
  · exact
      fmt.finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_alignedDiffCoeff_lt_two_mul_or_pred_exponent_gap_ge_t
        hbeta ht hmLow heHigh heLow hle hcoeff_le hcase hxy
  · have hlo :
        2 * fmt.beta ^ fmt.t ≤
          fmt.minNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow) -
            mLow := by
      exact le_of_not_gt (fun hk => hcase (Or.inl hk))
    have hnot_pred : ¬ eLow + (fmt.t : ℤ) ≤ eHigh - 1 := by
      intro hpred
      exact hcase (Or.inr hpred)
    have hboundary_le : eHigh ≤ eLow + (fmt.t : ℤ) := by
      omega
    rcases lt_or_eq_of_le hboundary_le with hwindow | hgap
    · exact
        fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_multiGuardComplementaryRegion
          hbeta fmt.minNormalMantissa_normalized hmLow heHigh heLow hle
          hcoeff_le hlo hwindow hxy
    · exact
        fmt.finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t_multiGuard
          hbeta hmLow heHigh heLow hle hcoeff_le hlo hgap hxy
/-- Operation-level same-sign normalized ordered-exponent addition has finite
local error in the exact precision-gap branch.

At `eHigh = eLow + t`, the lower normalized operand supplies the required
low-cell alternative automatically: the minimum mantissa gives the half-ulp tie
and all larger mantissas give the strict right-half branch. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  have hcell :
      fmt.normalizedValue false mLow eLow <
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        fmt.normalizedValue false mLow eLow =
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
            fmt.normalizedValue false mLow eLow ∧
          fmt.normalizedValue false mLow eLow <
            fmt.ulpAtExponent eHigh) ∨
        fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh :=
    fmt.normalizedValue_false_low_cell_cases_of_exponent_gap_eq_t
      hbeta hmLow hexp
  exact
    finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_low_cell_cases
      (fmt := fmt)
      hbeta ht hmHigh hmHighSucc hmLow heHigh heLow hexp hcell hxy
/-- Commuted operation-level same-sign normalized ordered-exponent addition
has finite local error in the exact precision-gap branch. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_exponent_gap_eq_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
  have hcell :
      fmt.normalizedValue false mLow eLow <
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        fmt.normalizedValue false mLow eLow =
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
            fmt.normalizedValue false mLow eLow ∧
          fmt.normalizedValue false mLow eLow <
            fmt.ulpAtExponent eHigh) ∨
        fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh :=
    fmt.normalizedValue_false_low_cell_cases_of_exponent_gap_eq_t
      hbeta hmLow hexp
  exact
    finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_low_cell_cases
      (fmt := fmt)
      hbeta ht hmHigh hmHighSucc hmLow heHigh heLow hexp hcell hxy
/-- Operation-level same-sign normalized ordered-exponent addition has finite
local error in the exact precision-gap branch when the high operand is
`maxNormalMantissa`. -/
theorem finiteRoundToEvenOp_add_max_sameSign_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  have hcell :
      fmt.normalizedValue false mLow eLow <
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        fmt.normalizedValue false mLow eLow =
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
            fmt.normalizedValue false mLow eLow ∧
          fmt.normalizedValue false mLow eLow <
            fmt.ulpAtExponent eHigh) ∨
        fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh :=
    fmt.normalizedValue_false_low_cell_cases_of_exponent_gap_eq_t
      hbeta hmLow hexp
  exact
    finiteRoundToEvenOp_add_max_sameSign_orderedExponent_error_finiteSystem_of_low_cell_cases
      (fmt := fmt)
      hbeta ht hmLow heLow hexp hcell hxy
/-- Commuted operation-level same-sign normalized ordered-exponent addition
has finite local error in the exact precision-gap branch when the high operand
is `maxNormalMantissa`. -/
theorem finiteRoundToEvenOp_add_max_sameSign_orderedExponent_comm_error_finiteSystem_of_exponent_gap_eq_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hexp : eHigh = eLow + (fmt.t : ℤ))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative fmt.maxNormalMantissa eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)) := by
  have hcell :
      fmt.normalizedValue false mLow eLow <
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        fmt.normalizedValue false mLow eLow =
          (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent eHigh <
            fmt.normalizedValue false mLow eLow ∧
          fmt.normalizedValue false mLow eLow <
            fmt.ulpAtExponent eHigh) ∨
        fmt.normalizedValue false mLow eLow = fmt.ulpAtExponent eHigh :=
    fmt.normalizedValue_false_low_cell_cases_of_exponent_gap_eq_t
      hbeta hmLow hexp
  exact
    finiteRoundToEvenOp_add_max_sameSign_orderedExponent_comm_error_finiteSystem_of_low_cell_cases
      (fmt := fmt)
      hbeta ht hmLow heLow hexp hcell hxy
/-- Operation-level same-sign normalized ordered-exponent addition has finite
local error once the lower exponent is at least one precision window below the
higher exponent.

This packages the two closed large-alignment branches: strict gap
`eLow + t < eHigh`, where the lower operand is strictly inside the left
half-cell, and exact precision gap `eHigh = eLow + t`, where the lower mantissa
derives the half-ulp/right-half split. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_exponent_gap_ge_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hgap : eLow + (fmt.t : ℤ) ≤ eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  rcases lt_or_eq_of_le hgap with hlt | heq
  · exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_exponent_gap_gt_t
        hbeta ht hmHigh hmHighSucc hmLow heLow hlt hxy
  · exact
      finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t
        (fmt := fmt)
        hbeta ht hmHigh hmHighSucc hmLow heHigh heLow heq.symm hxy
/-- Commuted operation-level same-sign normalized ordered-exponent addition
has finite local error once the lower exponent is at least one precision window
below the higher exponent. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_exponent_gap_ge_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hgap : eLow + (fmt.t : ℤ) ≤ eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
  rcases lt_or_eq_of_le hgap with hlt | heq
  · exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_exponent_gap_gt_t
        hbeta ht hmHigh hmHighSucc hmLow heLow hlt hxy
  · exact
      finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_exponent_gap_eq_t
        (fmt := fmt)
        hbeta ht hmHigh hmHighSucc hmLow heHigh heLow heq.symm hxy
/-- Operation-level same-sign normalized ordered-exponent addition has finite
local error once the lower exponent is at least one precision window below the
higher exponent and the high operand is `maxNormalMantissa`. -/
theorem finiteRoundToEvenOp_add_max_sameSign_orderedExponent_error_finiteSystem_of_exponent_gap_ge_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hgap : eLow + (fmt.t : ℤ) ≤ eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  rcases lt_or_eq_of_le hgap with hlt | heq
  · exact
      fmt.finiteRoundToEvenOp_add_max_sameSign_orderedExponent_error_finiteSystem_of_exponent_gap_gt_t
        hbeta ht hmLow heLow hlt hxy
  · exact
      finiteRoundToEvenOp_add_max_sameSign_orderedExponent_error_finiteSystem_of_exponent_gap_eq_t
        (fmt := fmt)
        hbeta ht hmLow heLow heq.symm hxy
/-- Commuted operation-level same-sign normalized ordered-exponent addition
has finite local error once the lower exponent is at least one precision window
below the higher exponent and the high operand is `maxNormalMantissa`. -/
theorem finiteRoundToEvenOp_add_max_sameSign_orderedExponent_comm_error_finiteSystem_of_exponent_gap_ge_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hgap : eLow + (fmt.t : ℤ) ≤ eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative fmt.maxNormalMantissa eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)) := by
  rcases lt_or_eq_of_le hgap with hlt | heq
  · exact
      fmt.finiteRoundToEvenOp_add_max_sameSign_orderedExponent_comm_error_finiteSystem_of_exponent_gap_gt_t
        hbeta ht hmLow heLow hlt hxy
  · exact
      finiteRoundToEvenOp_add_max_sameSign_orderedExponent_comm_error_finiteSystem_of_exponent_gap_eq_t
        (fmt := fmt)
        hbeta ht hmLow heLow heq.symm hxy
/-- Operation-level same-sign normalized ordered-exponent addition has finite
local error in either of the two currently closed ordered-exponent regions:
the exact-or-one-guard aligned-coefficient range, or the precision-window-or-
larger exponent-gap range.

This is a reusable dispatcher for the C4.4/FastTwoSum broad split.  The
remaining normalized ordered-exponent work is the complementary region where
the aligned coefficient is at least `2*beta^t` while the exponent gap is still
less than one precision window. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_two_mul_or_exponent_gap_ge_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcase :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
          2 * fmt.beta ^ fmt.t ∨
        eLow + (fmt.t : ℤ) ≤ eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  rcases hcase with hhi | hgap
  · exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound
        hbeta hmHigh hmLow heHigh heLow hle hhi hxy
  · exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_exponent_gap_ge_t
        hbeta ht hmHigh hmHighSucc hmLow heHigh heLow hgap hxy
/-- Commuted operation-level same-sign normalized ordered-exponent addition has
finite local error in either the exact-or-one-guard aligned-coefficient range
or the precision-window-or-larger exponent-gap range. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_alignedCoeff_lt_two_mul_or_exponent_gap_ge_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcase :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
          2 * fmt.beta ^ fmt.t ∨
        eLow + (fmt.t : ℤ) ≤ eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
  rcases hcase with hhi | hgap
  · exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound
        hbeta hmHigh hmLow heHigh heLow hle hhi hxy
  · exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_exponent_gap_ge_t
        hbeta ht hmHigh hmHighSucc hmLow heHigh heLow hgap hxy
/-- Operation-level same-sign normalized ordered-exponent addition has finite
local error in the max-mantissa boundary case whenever either the aligned
coefficient is in the exact-or-one-guard range or the lower exponent is at
least one precision window below the higher exponent. -/
theorem finiteRoundToEvenOp_add_max_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_two_mul_or_exponent_gap_ge_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcase :
      fmt.maxNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
          2 * fmt.beta ^ fmt.t ∨
        eLow + (fmt.t : ℤ) ≤ eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  rcases hcase with hhi | hgap
  · exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound
        hbeta fmt.maxNormalMantissa_normalized hmLow heHigh heLow hle hhi hxy
  · exact
      fmt.finiteRoundToEvenOp_add_max_sameSign_orderedExponent_error_finiteSystem_of_exponent_gap_ge_t
        hbeta ht hmLow heLow hgap hxy
/-- Commuted operation-level same-sign normalized ordered-exponent addition has
finite local error in the max-mantissa boundary case whenever either the
aligned coefficient is in the exact-or-one-guard range or the lower exponent is
at least one precision window below the higher exponent. -/
theorem finiteRoundToEvenOp_add_max_sameSign_orderedExponent_comm_error_finiteSystem_of_alignedCoeff_lt_two_mul_or_exponent_gap_ge_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcase :
      fmt.maxNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
          2 * fmt.beta ^ fmt.t ∨
        eLow + (fmt.t : ℤ) ≤ eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative fmt.maxNormalMantissa eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)) := by
  rcases hcase with hhi | hgap
  · exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound
        hbeta fmt.maxNormalMantissa_normalized hmLow heHigh heLow hle hhi hxy
  · exact
      fmt.finiteRoundToEvenOp_add_max_sameSign_orderedExponent_comm_error_finiteSystem_of_exponent_gap_ge_t
        hbeta ht hmLow heLow hgap hxy
/-- Operation-level same-sign normalized ordered-exponent addition has finite
local error throughout the non-boundary high-mantissa base-2 split.

This combines the exact-or-one-guard/large-gap dispatcher with the
complementary multi-guard region, leaving only higher-level finite-operand and
opposite-sign integration outside this same-sign ordered-exponent surface. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  by_cases hcase :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
          2 * fmt.beta ^ fmt.t ∨
        eLow + (fmt.t : ℤ) ≤ eHigh
  · exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_two_mul_or_exponent_gap_ge_t
        hbeta ht hmHigh hmHighSucc hmLow heHigh heLow hle hcase hxy
  · have hlo :
        2 * fmt.beta ^ fmt.t ≤
          mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow := by
      exact le_of_not_gt (fun hk => hcase (Or.inl hk))
    have hwindow : eLow + (fmt.t : ℤ) > eHigh := by
      exact lt_of_not_ge (fun hgap => hcase (Or.inr hgap))
    exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardComplementaryRegion
        hbeta hmHigh hmLow heHigh heLow hle hlo hwindow hxy
/-- Commuted operation-level same-sign normalized ordered-exponent addition has
finite local error throughout the non-boundary high-mantissa base-2 split. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
  by_cases hcase :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
          2 * fmt.beta ^ fmt.t ∨
        eLow + (fmt.t : ℤ) ≤ eHigh
  · exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_alignedCoeff_lt_two_mul_or_exponent_gap_ge_t
        hbeta ht hmHigh hmHighSucc hmLow heHigh heLow hle hcase hxy
  · have hlo :
        2 * fmt.beta ^ fmt.t ≤
          mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow := by
      exact le_of_not_gt (fun hk => hcase (Or.inl hk))
    have hwindow : eLow + (fmt.t : ℤ) > eHigh := by
      exact lt_of_not_ge (fun hgap => hcase (Or.inr hgap))
    exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_multiGuardComplementaryRegion
        hbeta hmHigh hmLow heHigh heLow hle hlo hwindow hxy
/-- Operation-level same-sign normalized ordered-exponent addition has finite
local error throughout the max-mantissa base-2 split. -/
theorem finiteRoundToEvenOp_add_max_sameSign_orderedExponent_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative fmt.maxNormalMantissa eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  by_cases hcase :
      fmt.maxNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
          2 * fmt.beta ^ fmt.t ∨
        eLow + (fmt.t : ℤ) ≤ eHigh
  · exact
      fmt.finiteRoundToEvenOp_add_max_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_two_mul_or_exponent_gap_ge_t
        hbeta ht hmLow heHigh heLow hle hcase hxy
  · have hlo :
        2 * fmt.beta ^ fmt.t ≤
          fmt.maxNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow) +
            mLow := by
      exact le_of_not_gt (fun hk => hcase (Or.inl hk))
    have hwindow : eLow + (fmt.t : ℤ) > eHigh := by
      exact lt_of_not_ge (fun hgap => hcase (Or.inr hgap))
    exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardComplementaryRegion
        hbeta fmt.maxNormalMantissa_normalized hmLow heHigh heLow hle hlo
        hwindow hxy
/-- Commuted operation-level same-sign normalized ordered-exponent addition has
finite local error throughout the max-mantissa base-2 split. -/
theorem finiteRoundToEvenOp_add_max_sameSign_orderedExponent_comm_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative fmt.maxNormalMantissa eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative fmt.maxNormalMantissa eHigh)) := by
  by_cases hcase :
      fmt.maxNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
          2 * fmt.beta ^ fmt.t ∨
        eLow + (fmt.t : ℤ) ≤ eHigh
  · exact
      fmt.finiteRoundToEvenOp_add_max_sameSign_orderedExponent_comm_error_finiteSystem_of_alignedCoeff_lt_two_mul_or_exponent_gap_ge_t
        hbeta ht hmLow heHigh heLow hle hcase hxy
  · have hlo :
        2 * fmt.beta ^ fmt.t ≤
          fmt.maxNormalMantissa * fmt.beta ^ Int.toNat (eHigh - eLow) +
            mLow := by
      exact le_of_not_gt (fun hk => hcase (Or.inl hk))
    have hwindow : eLow + (fmt.t : ℤ) > eHigh := by
      exact lt_of_not_ge (fun hgap => hcase (Or.inr hgap))
    exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_multiGuardComplementaryRegion
        hbeta fmt.maxNormalMantissa_normalized hmLow heHigh heLow hle hlo
        hwindow hxy
/-- Operation-level same-sign normalized addition has finite local error for
arbitrary exponent order in the base-2 finite-normal branch.

This lifts the ordered-exponent same-sign dispatcher from explicit high/low
operand order to arbitrary normalized operands with the same sign. -/
theorem finiteRoundToEvenOp_add_sameSign_normalized_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {m n : ℕ} {e f : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e)
    (hf : fmt.exponentInRange f)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative m e +
          fmt.normalizedValue negative n f)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.normalizedValue negative n f) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.normalizedValue negative n f)) := by
  by_cases hef : e ≤ f
  · by_cases hnmax : n = fmt.maxNormalMantissa
    · subst n
      exact
        fmt.finiteRoundToEvenOp_add_max_sameSign_orderedExponent_comm_error_finiteSystem_of_baseTwo
          hbeta ht hm hf he hef hxy
    · have hnSucc : fmt.normalizedMantissa (n + 1) :=
        fmt.normalizedMantissa_succ_of_ne_maxNormalMantissa hn hnmax
      exact
        fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_baseTwo
          hbeta ht hn hnSucc hm hf he hef hxy
  · have hfe : f ≤ e := le_of_not_ge hef
    by_cases hmmax : m = fmt.maxNormalMantissa
    · subst m
      exact
        fmt.finiteRoundToEvenOp_add_max_sameSign_orderedExponent_error_finiteSystem_of_baseTwo
          hbeta ht hn he hf hfe hxy
    · have hmSucc : fmt.normalizedMantissa (m + 1) :=
        fmt.normalizedMantissa_succ_of_ne_maxNormalMantissa hm hmmax
      exact
        fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_baseTwo
          hbeta ht hm hmSucc hn he hf hfe hxy
/-- Same-sign normalized-system values have finite local add error in the
base-2 finite-normal branch, once same-sign normalized representations are
supplied for both operands. -/
theorem finiteRoundToEvenOp_add_sameSign_normalizedSystem_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {x y : ℝ}
    (hx :
      ∃ (m : ℕ) (e : ℤ),
        fmt.normalizedMantissa m ∧
        fmt.exponentInRange e ∧
        x = fmt.normalizedValue negative m e)
    (hy :
      ∃ (n : ℕ) (f : ℤ),
        fmt.normalizedMantissa n ∧
        fmt.exponentInRange f ∧
        y = fmt.normalizedValue negative n f)
    (hxy : fmt.finiteNormalRange (x + y)) :
    fmt.finiteSystem
      ((x + y) - fmt.finiteRoundToEvenOp BasicOp.add x y) := by
  rcases hx with ⟨m, e, hm, he, rfl⟩
  rcases hy with ⟨n, f, hn, hf, rfl⟩
  exact
    fmt.finiteRoundToEvenOp_add_sameSign_normalized_error_finiteSystem_of_baseTwo
      hbeta ht hm hn he hf hxy
/-- Opposite-sign, same-exponent normalized addition is exact for the concrete
finite round-to-even operation wrapper.  This is the same-exponent subtraction
branch of the remaining C4.4/FastTwoSum sign split. -/
theorem finiteRoundToEvenOp_add_oppositeSign_sameExponent_eq_exact
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue negative m e)
        (fmt.normalizedValue (!negative) n e) =
      fmt.normalizedValue negative m e +
        fmt.normalizedValue (!negative) n e := by
  have hfin_sub :
      fmt.finiteSystem
        (fmt.normalizedValue negative m e -
          fmt.normalizedValue negative n e) :=
    fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedMantissas
      (negative := negative) (m := m) (n := n) (e := e) hm hn he
  have hfin_add :
      fmt.finiteSystem
        (fmt.normalizedValue negative m e +
          fmt.normalizedValue (!negative) n e) := by
    simpa [fmt.normalizedValue_not_eq_neg negative n e, sub_eq_add_neg]
      using hfin_sub
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue negative m e)
      (y := fmt.normalizedValue (!negative) n e) hfin_add)
/-- Opposite-sign, same-exponent normalized addition has zero local roundoff
error, hence a finite representable error. -/
theorem finiteRoundToEvenOp_add_oppositeSign_sameExponent_error_finiteSystem
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.normalizedValue (!negative) n e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.normalizedValue (!negative) n e)) := by
  rw [finiteRoundToEvenOp_add_oppositeSign_sameExponent_eq_exact hm hn he]
  simpa using fmt.finiteSystem_zero
/-- Arbitrary positive normalized plus negative normalized operands have finite
local add roundoff error in the base-2 finite-normal branch.

The proof first splits off the same-exponent exact branch.  For a strict
exponent order, the higher-exponent operand dominates on the aligned
coefficient lattice, so the ordered-exponent opposite-sign dispatchers apply. -/
theorem finiteRoundToEvenOp_add_positive_neg_normalized_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e f : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e)
    (hf : fmt.exponentInRange f)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false m e +
          fmt.normalizedValue true n f)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.normalizedValue true n f) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.normalizedValue true n f)) := by
  by_cases hef : e = f
  · subst f
    exact
      fmt.finiteRoundToEvenOp_add_oppositeSign_sameExponent_error_finiteSystem
        (negative := false) hm hn he
  · by_cases hfe : f < e
    · have hcoeff_le :
          n ≤ m * fmt.beta ^ Int.toNat (e - f) :=
        fmt.normalizedMantissa_le_scaled_of_exponent_lt hm hn hfe
      by_cases hmMin : m = fmt.minNormalMantissa
      · subst m
        exact
          fmt.finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_baseTwo
            hbeta hn he hf (le_of_lt hfe) hcoeff_le hxy
      · exact
          fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_baseTwo_nonMinHigh
            hbeta hm hmMin hn he hf (le_of_lt hfe) hcoeff_le hxy
    · have hef_lt : e < f := by omega
      have hxy' :
          fmt.finiteNormalRange
            (fmt.normalizedValue true n f +
              fmt.normalizedValue false m e) := by
        simpa [add_comm] using hxy
      have hcoeff_le :
          m ≤ n * fmt.beta ^ Int.toNat (f - e) :=
        fmt.normalizedMantissa_le_scaled_of_exponent_lt hn hm hef_lt
      have hfin :
          fmt.finiteSystem
            ((fmt.normalizedValue true n f +
                fmt.normalizedValue false m e) -
              fmt.finiteRoundToEvenOp BasicOp.add
                (fmt.normalizedValue true n f)
                (fmt.normalizedValue false m e)) := by
        by_cases hnMin : n = fmt.minNormalMantissa
        · subst n
          exact
            fmt.finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_baseTwo
              hbeta ht hm hf he (le_of_lt hef_lt) hcoeff_le hxy'
        · exact
            fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_baseTwo_nonMinHigh
              hbeta ht hn hnMin hm hf he (le_of_lt hef_lt) hcoeff_le hxy'
      have hop :
          fmt.finiteRoundToEvenOp BasicOp.add
              (fmt.normalizedValue false m e)
              (fmt.normalizedValue true n f) =
            fmt.finiteRoundToEvenOp BasicOp.add
              (fmt.normalizedValue true n f)
              (fmt.normalizedValue false m e) := by
        simp [finiteRoundToEvenOp, BasicOp.exact, add_comm]
      rw [hop]
      convert hfin using 1
      ring
/-- Arbitrary negative normalized plus positive normalized operands have finite
local add roundoff error in the base-2 finite-normal branch. -/
theorem finiteRoundToEvenOp_add_negative_pos_normalized_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e f : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e)
    (hf : fmt.exponentInRange f)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true m e +
          fmt.normalizedValue false n f)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e +
          fmt.normalizedValue false n f) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.normalizedValue false n f)) := by
  by_cases hef : e = f
  · subst f
    exact
      fmt.finiteRoundToEvenOp_add_oppositeSign_sameExponent_error_finiteSystem
        (negative := true) hm hn he
  · by_cases hfe : f < e
    · have hcoeff_le :
          n ≤ m * fmt.beta ^ Int.toNat (e - f) :=
        fmt.normalizedMantissa_le_scaled_of_exponent_lt hm hn hfe
      by_cases hmMin : m = fmt.minNormalMantissa
      · subst m
        exact
          fmt.finiteRoundToEvenOp_add_negative_min_pos_orderedExponent_error_finiteSystem_of_baseTwo
            hbeta ht hn he hf (le_of_lt hfe) hcoeff_le hxy
      · exact
          fmt.finiteRoundToEvenOp_add_negative_pos_orderedExponent_error_finiteSystem_of_baseTwo_nonMinHigh
            hbeta ht hm hmMin hn he hf (le_of_lt hfe) hcoeff_le hxy
    · have hef_lt : e < f := by omega
      have hxy' :
          fmt.finiteNormalRange
            (fmt.normalizedValue false n f +
              fmt.normalizedValue true m e) := by
        simpa [add_comm] using hxy
      have hcoeff_le :
          m ≤ n * fmt.beta ^ Int.toNat (f - e) :=
        fmt.normalizedMantissa_le_scaled_of_exponent_lt hn hm hef_lt
      have hfin :
          fmt.finiteSystem
            ((fmt.normalizedValue false n f +
                fmt.normalizedValue true m e) -
              fmt.finiteRoundToEvenOp BasicOp.add
                (fmt.normalizedValue false n f)
                (fmt.normalizedValue true m e)) := by
        by_cases hnMin : n = fmt.minNormalMantissa
        · subst n
          exact
            fmt.finiteRoundToEvenOp_add_positive_min_neg_orderedExponent_error_finiteSystem_of_baseTwo
              hbeta hm hf he (le_of_lt hef_lt) hcoeff_le hxy'
        · exact
            fmt.finiteRoundToEvenOp_add_positive_neg_orderedExponent_error_finiteSystem_of_baseTwo_nonMinHigh
              hbeta hn hnMin hm hf he (le_of_lt hef_lt) hcoeff_le hxy'
      have hop :
          fmt.finiteRoundToEvenOp BasicOp.add
              (fmt.normalizedValue true m e)
              (fmt.normalizedValue false n f) =
            fmt.finiteRoundToEvenOp BasicOp.add
              (fmt.normalizedValue false n f)
              (fmt.normalizedValue true m e) := by
        simp [finiteRoundToEvenOp, BasicOp.exact, add_comm]
      rw [hop]
      convert hfin using 1
      ring
/-- Positive normalized-system plus negative normalized-system operands have
finite local add roundoff error in the base-2 finite-normal branch, once the
signed normalized representations are supplied. -/
theorem finiteRoundToEvenOp_add_pos_neg_normalizedSystem_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {x y : ℝ}
    (hx :
      ∃ (m : ℕ) (e : ℤ),
        fmt.normalizedMantissa m ∧
        fmt.exponentInRange e ∧
        x = fmt.normalizedValue false m e)
    (hy :
      ∃ (n : ℕ) (f : ℤ),
        fmt.normalizedMantissa n ∧
        fmt.exponentInRange f ∧
        y = fmt.normalizedValue true n f)
    (hxy : fmt.finiteNormalRange (x + y)) :
    fmt.finiteSystem
      ((x + y) - fmt.finiteRoundToEvenOp BasicOp.add x y) := by
  rcases hx with ⟨m, e, hm, he, rfl⟩
  rcases hy with ⟨n, f, hn, hf, rfl⟩
  exact
    fmt.finiteRoundToEvenOp_add_positive_neg_normalized_error_finiteSystem_of_baseTwo
      hbeta ht hm hn he hf hxy
/-- Negative normalized-system plus positive normalized-system operands have
finite local add roundoff error in the base-2 finite-normal branch, once the
signed normalized representations are supplied. -/
theorem finiteRoundToEvenOp_add_neg_pos_normalizedSystem_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {x y : ℝ}
    (hx :
      ∃ (m : ℕ) (e : ℤ),
        fmt.normalizedMantissa m ∧
        fmt.exponentInRange e ∧
        x = fmt.normalizedValue true m e)
    (hy :
      ∃ (n : ℕ) (f : ℤ),
        fmt.normalizedMantissa n ∧
        fmt.exponentInRange f ∧
        y = fmt.normalizedValue false n f)
    (hxy : fmt.finiteNormalRange (x + y)) :
    fmt.finiteSystem
      ((x + y) - fmt.finiteRoundToEvenOp BasicOp.add x y) := by
  rcases hx with ⟨m, e, hm, he, rfl⟩
  rcases hy with ⟨n, f, hn, hf, rfl⟩
  exact
    fmt.finiteRoundToEvenOp_add_negative_pos_normalized_error_finiteSystem_of_baseTwo
      hbeta ht hm hn he hf hxy
/-- Same-sign subnormal addition is exact for the concrete finite
round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_add_sameSign_subnormal_eq_exact
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ}
    (hm : fmt.subnormalMantissa m)
    (hn : fmt.subnormalMantissa n) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.subnormalValue negative m)
        (fmt.subnormalValue negative n) =
      fmt.subnormalValue negative m + fmt.subnormalValue negative n := by
  have hfin :
      fmt.finiteSystem
        (fmt.subnormalValue negative m +
          fmt.subnormalValue negative n) :=
    fmt.subnormalValue_add_sameSign_finiteSystem_of_subnormalMantissas
      (negative := negative) hm hn
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.subnormalValue negative m)
      (y := fmt.subnormalValue negative n) hfin)
/-- Same-sign subnormal addition has zero local roundoff error, hence a finite
representable error. -/
theorem finiteRoundToEvenOp_add_sameSign_subnormal_error_finiteSystem
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ}
    (hm : fmt.subnormalMantissa m)
    (hn : fmt.subnormalMantissa n) :
    fmt.finiteSystem
      ((fmt.subnormalValue negative m +
          fmt.subnormalValue negative n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative m)
          (fmt.subnormalValue negative n)) := by
  rw [finiteRoundToEvenOp_add_sameSign_subnormal_eq_exact hm hn]
  simpa using fmt.finiteSystem_zero
/-- Opposite-sign subnormal addition is exact for the concrete finite
round-to-even operation wrapper, reducing to same-sign subnormal subtraction on
the common lattice. -/
theorem finiteRoundToEvenOp_add_oppositeSign_subnormal_eq_exact
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ}
    (hm : fmt.subnormalMantissa m)
    (hn : fmt.subnormalMantissa n) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.subnormalValue negative m)
        (fmt.subnormalValue (!negative) n) =
      fmt.subnormalValue negative m + fmt.subnormalValue (!negative) n := by
  have hfin_sub :
      fmt.finiteSystem
        (fmt.subnormalValue negative m -
          fmt.subnormalValue negative n) :=
    fmt.subnormalValue_sub_sameSign_finiteSystem_of_subnormalMantissas
      (negative := negative) (m := m) (n := n) hm hn
  have hfin_add :
      fmt.finiteSystem
        (fmt.subnormalValue negative m +
          fmt.subnormalValue (!negative) n) := by
    simpa [fmt.subnormalValue_not_eq_neg negative n, sub_eq_add_neg]
      using hfin_sub
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.subnormalValue negative m)
      (y := fmt.subnormalValue (!negative) n) hfin_add)
/-- Opposite-sign subnormal addition has zero local roundoff error, hence a
finite representable error. -/
theorem finiteRoundToEvenOp_add_oppositeSign_subnormal_error_finiteSystem
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ}
    (hm : fmt.subnormalMantissa m)
    (hn : fmt.subnormalMantissa n) :
    fmt.finiteSystem
      ((fmt.subnormalValue negative m +
          fmt.subnormalValue (!negative) n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative m)
          (fmt.subnormalValue (!negative) n)) := by
  rw [finiteRoundToEvenOp_add_oppositeSign_subnormal_eq_exact hm hn]
  simpa using fmt.finiteSystem_zero
/-- Arbitrary-sign subnormal addition is exact for the concrete finite
round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_add_subnormal_eq_exact
    {fmt : FloatingPointFormat} {negativeX negativeY : Bool} {m n : ℕ}
    (hm : fmt.subnormalMantissa m)
    (hn : fmt.subnormalMantissa n) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.subnormalValue negativeX m)
        (fmt.subnormalValue negativeY n) =
      fmt.subnormalValue negativeX m + fmt.subnormalValue negativeY n := by
  cases negativeX <;> cases negativeY
  · exact fmt.finiteRoundToEvenOp_add_sameSign_subnormal_eq_exact hm hn
  · exact fmt.finiteRoundToEvenOp_add_oppositeSign_subnormal_eq_exact hm hn
  · exact fmt.finiteRoundToEvenOp_add_oppositeSign_subnormal_eq_exact
      (negative := true) hm hn
  · exact fmt.finiteRoundToEvenOp_add_sameSign_subnormal_eq_exact hm hn
/-- Arbitrary-sign subnormal addition has zero local roundoff error, hence a
finite representable error. -/
theorem finiteRoundToEvenOp_add_subnormal_error_finiteSystem
    {fmt : FloatingPointFormat} {negativeX negativeY : Bool} {m n : ℕ}
    (hm : fmt.subnormalMantissa m)
    (hn : fmt.subnormalMantissa n) :
    fmt.finiteSystem
      ((fmt.subnormalValue negativeX m +
          fmt.subnormalValue negativeY n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negativeX m)
          (fmt.subnormalValue negativeY n)) := by
  rw [finiteRoundToEvenOp_add_subnormal_eq_exact hm hn]
  simpa using fmt.finiteSystem_zero
/-- Ordinary subnormal-system operands add exactly under the concrete finite
round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_add_subnormalSystem_eq_exact
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.subnormalSystem x)
    (hy : fmt.subnormalSystem y) :
    fmt.finiteRoundToEvenOp BasicOp.add x y = x + y := by
  rcases hx with ⟨negativeX, m, hm, rfl⟩
  rcases hy with ⟨negativeY, n, hn, rfl⟩
  exact fmt.finiteRoundToEvenOp_add_subnormal_eq_exact hm hn
/-- Ordinary subnormal-system operands have finite local add roundoff error. -/
theorem finiteRoundToEvenOp_add_subnormalSystem_error_finiteSystem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.subnormalSystem x)
    (hy : fmt.subnormalSystem y) :
    fmt.finiteSystem
      ((x + y) - fmt.finiteRoundToEvenOp BasicOp.add x y) := by
  rw [fmt.finiteRoundToEvenOp_add_subnormalSystem_eq_exact hx hy]
  simpa using fmt.finiteSystem_zero
/-- Same-sign mixed normal/subnormal addition is exact for the concrete finite
round-to-even operation wrapper when the aligned coefficient already fits in
`t` radix digits. -/
theorem finiteRoundToEvenOp_add_normalized_sameSign_subnormal_eq_exact_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n < fmt.beta ^ fmt.t) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue negative m e)
        (fmt.subnormalValue negative n) =
      fmt.normalizedValue negative m e + fmt.subnormalValue negative n := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) :=
    fmt.normalizedValue_add_sameSign_subnormal_finiteSystem_of_alignedCoeff_lt_mantissaBound
      (negative := negative) hm hn he hcoeff
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue negative m e)
      (y := fmt.subnormalValue negative n) hfin)
/-- Same-sign mixed normal/subnormal addition has zero local roundoff error in
the aligned exact branch. -/
theorem finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.subnormalValue negative n)) := by
  rw [
    finiteRoundToEvenOp_add_normalized_sameSign_subnormal_eq_exact_of_alignedCoeff_lt_mantissaBound
      hm hn he hcoeff]
  simpa using fmt.finiteSystem_zero
/-- Commuted same-sign mixed subnormal/normal exact-add branch for the concrete
finite round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_add_subnormal_sameSign_normalized_eq_exact_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n < fmt.beta ^ fmt.t) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.subnormalValue negative n)
        (fmt.normalizedValue negative m e) =
      fmt.subnormalValue negative n + fmt.normalizedValue negative m e := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) :=
    fmt.normalizedValue_add_sameSign_subnormal_finiteSystem_of_alignedCoeff_lt_mantissaBound
      (negative := negative) hm hn he hcoeff
  have hfin_comm :
      fmt.finiteSystem
        (fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e) := by
    convert hfin using 1
    ring
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.subnormalValue negative n)
      (y := fmt.normalizedValue negative m e) hfin_comm)
/-- Commuted same-sign mixed subnormal/normal addition has zero local roundoff
error in the aligned exact branch. -/
theorem finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      ((fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative m e)) := by
  rw [
    finiteRoundToEvenOp_add_subnormal_sameSign_normalized_eq_exact_of_alignedCoeff_lt_mantissaBound
      hm hn he hcoeff]
  simpa using fmt.finiteSystem_zero
/-- Operation-level same-sign mixed normal/subnormal addition has finite
representable local roundoff error in the binary one-guard-word branch. -/
theorem finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hlo :
      fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) + n)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.subnormalValue negative n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.subnormalValue negative n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_guardCoeffBounds
      hbeta hm hn he hlo hhi hpolicy
/-- Commuted operation-level same-sign mixed subnormal/normal addition has
finite representable local roundoff error in the binary one-guard-word branch. -/
theorem finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hlo :
      fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) + n)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative m e)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative m e)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative m e)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue negative m e +
            fmt.subnormalValue negative n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.subnormalValue negative n)
            (fmt.normalizedValue negative m e)) :=
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_guardCoeffBounds
      hbeta hm hn he hlo hhi hpolicy
  convert hfin using 1
  ring
/-- Operation-level same-sign mixed normal/subnormal addition has finite
representable local roundoff error throughout the exact-or-one-guard range
`alignedCoeff < 2*beta^t`. -/
theorem finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.subnormalValue negative n)) := by
  by_cases hsmall :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        fmt.beta ^ fmt.t
  · exact
      fmt.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_alignedCoeff_lt_mantissaBound
        hm hn he hsmall
  · have hlo :
        fmt.beta ^ fmt.t ≤
          m * fmt.beta ^ Int.toNat (e - fmt.emin) + n :=
      le_of_not_gt hsmall
    exact
      fmt.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_guardCoeffBounds
        hbeta hm hn he hlo hhi hxy
/-- Commuted operation-level same-sign mixed subnormal/normal addition has
finite representable local roundoff error throughout the exact-or-one-guard
range `alignedCoeff < 2*beta^t`. -/
theorem finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative m e)) := by
  by_cases hsmall :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        fmt.beta ^ fmt.t
  · exact
      fmt.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_alignedCoeff_lt_mantissaBound
        hm hn he hsmall
  · have hlo :
        fmt.beta ^ fmt.t ≤
          m * fmt.beta ^ Int.toNat (e - fmt.emin) + n :=
      le_of_not_gt hsmall
    exact
      fmt.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_guardCoeffBounds
        hbeta hm hn he hlo hhi hxy
/-- Operation-level same-sign mixed normal/subnormal addition has finite local
roundoff error at the minimum normal exponent in binary.

At `emin`, the aligned coefficient is `m + n`; the normalized and subnormal
mantissa bounds put it below `2*beta^t`, so the closed exact-or-one-guard
dispatcher applies with no extra coefficient hypothesis. -/
theorem finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_at_emin_of_baseTwo
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {m n : ℕ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative m fmt.emin +
          fmt.subnormalValue negative n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m fmt.emin +
          fmt.subnormalValue negative n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m fmt.emin)
          (fmt.subnormalValue negative n)) := by
  have he : fmt.exponentInRange fmt.emin :=
    ⟨le_rfl, fmt.emin_le_emax⟩
  have hm_bound : m < fmt.beta ^ fmt.t := hm.2
  have hn_bound : n < fmt.beta ^ fmt.t :=
    lt_trans hn.2 fmt.minNormalMantissa_lt_mantissaBound
  have hsum : m + n < 2 * fmt.beta ^ fmt.t := by
    omega
  have hshift : Int.toNat (fmt.emin - fmt.emin) = 0 := by
    simp
  have hhi :
      m * fmt.beta ^ Int.toNat (fmt.emin - fmt.emin) + n <
        2 * fmt.beta ^ fmt.t := by
    simpa [hshift] using hsum
  exact
    fmt.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound
      hbeta hm hn he hhi hxy
/-- Commuted operation-level same-sign mixed subnormal/normal addition has
finite local roundoff error at the minimum normal exponent in binary. -/
theorem finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_at_emin_of_baseTwo
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {m n : ℕ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue negative n +
          fmt.normalizedValue negative m fmt.emin)) :
    fmt.finiteSystem
      ((fmt.subnormalValue negative n +
          fmt.normalizedValue negative m fmt.emin) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative m fmt.emin)) := by
  have he : fmt.exponentInRange fmt.emin :=
    ⟨le_rfl, fmt.emin_le_emax⟩
  have hm_bound : m < fmt.beta ^ fmt.t := hm.2
  have hn_bound : n < fmt.beta ^ fmt.t :=
    lt_trans hn.2 fmt.minNormalMantissa_lt_mantissaBound
  have hsum : m + n < 2 * fmt.beta ^ fmt.t := by
    omega
  have hshift : Int.toNat (fmt.emin - fmt.emin) = 0 := by
    simp
  have hhi :
      m * fmt.beta ^ Int.toNat (fmt.emin - fmt.emin) + n <
        2 * fmt.beta ^ fmt.t := by
    simpa [hshift] using hsum
  exact
    fmt.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound
      hbeta hm hn he hhi hxy
/-- Positive normal plus negative subnormal is finite representable when the
aligned subnormal-lattice coefficient difference has fewer than `t` radix
digits. -/
theorem normalizedValue_add_positive_neg_subnormal_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {m n : ℕ} {e : ℤ}
    (_hm : fmt.normalizedMantissa m)
    (_hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hdiff :
      (((m * fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ) -
          (n : ℤ)).natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      (fmt.normalizedValue false m e + fmt.subnormalValue true n) := by
  let q := Int.toNat (e - fmt.emin)
  have hq_cast : ((q : ℕ) : ℤ) = e - fmt.emin := by
    have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr he.1
    simpa [q] using Int.toNat_of_nonneg hnonneg
  have hq_endpoint : e - (q : ℤ) = fmt.emin := by
    omega
  have hshift :
      fmt.normalizedValue false m e =
        fmt.subnormalValue false (m * fmt.beta ^ q) :=
    fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
      false m q e hq_endpoint
  have hfin :
      fmt.finiteSystem
        (fmt.signValue false *
          ((((m * fmt.beta ^ q : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) :=
    fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := false)
      (k := (((m * fmt.beta ^ q : ℕ) : ℤ) - (n : ℤ)))
      (e := fmt.emin)
      ⟨le_rfl, fmt.emin_le_emax⟩
      (by simpa [q] using hdiff)
  convert hfin using 1
  rw [hshift]
  simp [subnormalValue, signValue, Nat.cast_mul, Nat.cast_pow]
  ring
/-- Negative normal plus positive subnormal is finite representable when the
aligned subnormal-lattice coefficient difference has fewer than `t` radix
digits. -/
theorem normalizedValue_add_negative_pos_subnormal_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hdiff :
      (((m * fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ) -
          (n : ℤ)).natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      (fmt.normalizedValue true m e + fmt.subnormalValue false n) := by
  have hpos :
      fmt.finiteSystem
        (fmt.normalizedValue false m e + fmt.subnormalValue true n) :=
    fmt.normalizedValue_add_positive_neg_subnormal_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
      hm hn he hdiff
  have hneg := fmt.finiteSystem_neg hpos
  convert hneg using 1
  simp [normalizedValue, subnormalValue, signValue]
  ring
/-- Positive normal plus negative subnormal rounds exactly in the aligned
finite-difference branch. -/
theorem finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_eq_exact_of_alignedDiffCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hdiff :
      (((m * fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ) -
          (n : ℤ)).natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue false m e)
        (fmt.subnormalValue true n) =
      fmt.normalizedValue false m e + fmt.subnormalValue true n := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue false m e + fmt.subnormalValue true n) :=
    fmt.normalizedValue_add_positive_neg_subnormal_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
      hm hn he hdiff
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue false m e)
      (y := fmt.subnormalValue true n) hfin)
/-- Positive normal plus negative subnormal has zero local error in the aligned
finite-difference branch. -/
theorem finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hdiff :
      (((m * fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ) -
          (n : ℤ)).natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue true n)) := by
  rw [
    fmt.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_eq_exact_of_alignedDiffCoeff_lt_mantissaBound
      hm hn he hdiff]
  simpa using fmt.finiteSystem_zero
/-- Negative normal plus positive subnormal rounds exactly in the aligned
finite-difference branch. -/
theorem finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_eq_exact_of_alignedDiffCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hdiff :
      (((m * fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ) -
          (n : ℤ)).natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue true m e)
        (fmt.subnormalValue false n) =
      fmt.normalizedValue true m e + fmt.subnormalValue false n := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue true m e + fmt.subnormalValue false n) :=
    fmt.normalizedValue_add_negative_pos_subnormal_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
      hm hn he hdiff
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue true m e)
      (y := fmt.subnormalValue false n) hfin)
/-- Negative normal plus positive subnormal has zero local error in the aligned
finite-difference branch. -/
theorem finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hdiff :
      (((m * fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ) -
          (n : ℤ)).natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue false n)) := by
  rw [
    fmt.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_eq_exact_of_alignedDiffCoeff_lt_mantissaBound
      hm hn he hdiff]
  simpa using fmt.finiteSystem_zero
/-- Commuted negative subnormal plus positive normal rounds exactly in the
aligned finite-difference branch. -/
theorem finiteRoundToEvenOp_add_negative_subnormal_pos_normalized_eq_exact_of_alignedDiffCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hdiff :
      (((m * fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ) -
          (n : ℤ)).natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.subnormalValue true n)
        (fmt.normalizedValue false m e) =
      fmt.subnormalValue true n + fmt.normalizedValue false m e := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue false m e + fmt.subnormalValue true n) :=
    fmt.normalizedValue_add_positive_neg_subnormal_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
      hm hn he hdiff
  have hfin_comm :
      fmt.finiteSystem
        (fmt.subnormalValue true n + fmt.normalizedValue false m e) := by
    convert hfin using 1
    ring
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.subnormalValue true n)
      (y := fmt.normalizedValue false m e) hfin_comm)
/-- Commuted negative subnormal plus positive normal has zero local error in
the aligned finite-difference branch. -/
theorem finiteRoundToEvenOp_add_negative_subnormal_pos_normalized_error_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hdiff :
      (((m * fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ) -
          (n : ℤ)).natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      ((fmt.subnormalValue true n +
          fmt.normalizedValue false m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue false m e)) := by
  rw [
    fmt.finiteRoundToEvenOp_add_negative_subnormal_pos_normalized_eq_exact_of_alignedDiffCoeff_lt_mantissaBound
      hm hn he hdiff]
  simpa using fmt.finiteSystem_zero
/-- Commuted positive subnormal plus negative normal rounds exactly in the
aligned finite-difference branch. -/
theorem finiteRoundToEvenOp_add_positive_subnormal_neg_normalized_eq_exact_of_alignedDiffCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hdiff :
      (((m * fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ) -
          (n : ℤ)).natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.subnormalValue false n)
        (fmt.normalizedValue true m e) =
      fmt.subnormalValue false n + fmt.normalizedValue true m e := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue true m e + fmt.subnormalValue false n) :=
    fmt.normalizedValue_add_negative_pos_subnormal_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
      hm hn he hdiff
  have hfin_comm :
      fmt.finiteSystem
        (fmt.subnormalValue false n + fmt.normalizedValue true m e) := by
    convert hfin using 1
    ring
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.subnormalValue false n)
      (y := fmt.normalizedValue true m e) hfin_comm)
/-- Commuted positive subnormal plus negative normal has zero local error in
the aligned finite-difference branch. -/
theorem finiteRoundToEvenOp_add_positive_subnormal_neg_normalized_error_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hdiff :
      (((m * fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ) -
          (n : ℤ)).natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      ((fmt.subnormalValue false n +
          fmt.normalizedValue true m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue true m e)) := by
  rw [
    fmt.finiteRoundToEvenOp_add_positive_subnormal_neg_normalized_eq_exact_of_alignedDiffCoeff_lt_mantissaBound
      hm hn he hdiff]
  simpa using fmt.finiteSystem_zero
/-- Convert a natural subtraction bound into the signed `natAbs` coefficient
form used by the finite scaled-integer constructors. -/
theorem natAbs_int_sub_lt_of_nat_sub_lt {a b B : ℕ}
    (hba : b ≤ a) (h : a - b < B) :
    (((a : ℤ) - (b : ℤ)).natAbs < B) := by
  have hnonneg : 0 ≤ (a : ℤ) - (b : ℤ) := by
    omega
  have habs_int :
      ((((a : ℤ) - (b : ℤ)).natAbs : ℤ) =
        (a : ℤ) - (b : ℤ)) :=
    Int.natAbs_of_nonneg hnonneg
  have hsub_cast :
      (((a - b : ℕ) : ℤ) = (a : ℤ) - (b : ℤ)) := by
    exact_mod_cast
      (Nat.cast_sub hba : ((a - b : ℕ) : ℤ) = (a : ℤ) - (b : ℤ))
  exact_mod_cast h
/-- If the signed `natAbs` form of a nonnegative natural subtraction is not
below a bound, then the natural subtraction itself is at least that bound. -/
theorem nat_sub_le_of_not_natAbs_int_sub_lt {a b B : ℕ}
    (hba : b ≤ a)
    (hnot : ¬ (((a : ℤ) - (b : ℤ)).natAbs < B)) :
    B ≤ a - b := by
  have hnonneg : 0 ≤ (a : ℤ) - (b : ℤ) := by
    omega
  have habs_int :
      ((((a : ℤ) - (b : ℤ)).natAbs : ℤ) =
        (a : ℤ) - (b : ℤ)) :=
    Int.natAbs_of_nonneg hnonneg
  have hsub_cast :
      (((a - b : ℕ) : ℤ) = (a : ℤ) - (b : ℤ)) := by
    exact_mod_cast
      (Nat.cast_sub hba : ((a - b : ℕ) : ℤ) = (a : ℤ) - (b : ℤ))
  have h_eq : ((a : ℤ) - (b : ℤ)).natAbs = a - b := by
    exact Nat.cast_inj.mp (by rw [habs_int, hsub_cast])
  rw [h_eq] at hnot
  exact le_of_not_gt hnot
/-- A subnormal mantissa is dominated by any normalized mantissa after the
normal operand is shifted onto the subnormal `emin` lattice. -/
theorem subnormalMantissa_le_aligned_normalizedCoeff
    {fmt : FloatingPointFormat} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n) :
    n ≤ m * fmt.beta ^ Int.toNat (e - fmt.emin) := by
  have hn_le_m : n ≤ m :=
    le_trans (Nat.le_of_lt hn.2) hm.1
  have hpow_pos :
      0 < fmt.beta ^ Int.toNat (e - fmt.emin) :=
    Nat.pow_pos (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hpow_ge :
      1 ≤ fmt.beta ^ Int.toNat (e - fmt.emin) :=
    Nat.succ_le_of_lt hpow_pos
  have hm_le : m ≤ m * fmt.beta ^ Int.toNat (e - fmt.emin) := by
    simpa using Nat.mul_le_mul_left m hpow_ge
  exact le_trans hn_le_m hm_le
/-- Positive mixed normal/subnormal opposite-sign addition has finite local
error under source round-to-even evidence in the binary one-guard-word
aligned-difference branch. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_subnormal_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {m n : ℕ} {e : ℤ}
    (_hm : fmt.normalizedMantissa m)
    (_hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff_le :
      n ≤ m * fmt.beta ^ Int.toNat (e - fmt.emin))
    (hlo :
      fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) - n)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) - n <
        2 * fmt.beta ^ fmt.t)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e + fmt.subnormalValue true n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e + fmt.subnormalValue true n) - y) := by
  let shift := Int.toNat (e - fmt.emin)
  let k : ℕ := m * fmt.beta ^ shift - n
  let q : ℕ := k / fmt.beta
  let r : ℕ := k % fmt.beta
  have hshift_cast : ((shift : ℕ) : ℤ) = e - fmt.emin := by
    have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr he.1
    simpa [shift] using Int.toNat_of_nonneg hnonneg
  have hshift_endpoint : e - (shift : ℤ) = fmt.emin := by
    omega
  have hcoeff_le' : n ≤ m * fmt.beta ^ shift := by
    simpa [shift] using hcoeff_le
  have hshift :
      fmt.normalizedValue false m e =
        fmt.subnormalValue false (m * fmt.beta ^ shift) :=
    fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
      (negative := false) (m := m) (shift := shift) (e := e)
      hshift_endpoint
  have hk : k = fmt.beta * q + r := by
    rw [show q = k / fmt.beta by rfl, show r = k % fmt.beta by rfl]
    exact (Nat.div_add_mod k fmt.beta).symm
  have hr : r < fmt.beta := by
    rw [show r = k % fmt.beta by rfl]
    exact Nat.mod_lt k (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hlo' : fmt.beta ^ fmt.t ≤ k := by
    simpa [k, shift] using hlo
  have hhi' : k < 2 * fmt.beta ^ fmt.t := by
    simpa [k, shift] using hhi
  have hemin : fmt.exponentInRange fmt.emin :=
    ⟨le_rfl, fmt.emin_le_emax⟩
  have hsource :
      fmt.normalizedValue false m e + fmt.subnormalValue true n =
        ((k : ℕ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
    rw [hshift]
    simp [k, subnormalValue, signValue, Nat.cast_sub hcoeff_le',
      Nat.cast_mul, Nat.cast_pow]
    ring
  have hpolicy' :
      fmt.sourceRoundToEvenEvidence
        (((k : ℕ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) y := by
    simpa [hsource] using hpolicy
  have hfin :
      fmt.finiteSystem
        ((((k : ℕ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) - y) :=
    fmt.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_guardCoeffBounds
      hbeta hemin hk hr hlo' hhi' hpolicy'
  simpa [hsource] using hfin
/-- Negative mixed normal/subnormal opposite-sign addition has finite local
error in the binary one-guard-word aligned-difference branch. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_subnormal_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {m n : ℕ} {e : ℤ}
    (_hm : fmt.normalizedMantissa m)
    (_hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff_le :
      n ≤ m * fmt.beta ^ Int.toNat (e - fmt.emin))
    (hlo :
      fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) - n)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) - n <
        2 * fmt.beta ^ fmt.t)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e + fmt.subnormalValue false n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e + fmt.subnormalValue false n) - y) := by
  let shift := Int.toNat (e - fmt.emin)
  let k : ℕ := m * fmt.beta ^ shift - n
  let q : ℕ := k / fmt.beta
  let r : ℕ := k % fmt.beta
  have hshift_cast : ((shift : ℕ) : ℤ) = e - fmt.emin := by
    have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr he.1
    simpa [shift] using Int.toNat_of_nonneg hnonneg
  have hshift_endpoint : e - (shift : ℤ) = fmt.emin := by
    omega
  have hcoeff_le' : n ≤ m * fmt.beta ^ shift := by
    simpa [shift] using hcoeff_le
  have hshift :
      fmt.normalizedValue true m e =
        fmt.subnormalValue true (m * fmt.beta ^ shift) :=
    fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
      (negative := true) (m := m) (shift := shift) (e := e)
      hshift_endpoint
  have hk : k = fmt.beta * q + r := by
    rw [show q = k / fmt.beta by rfl, show r = k % fmt.beta by rfl]
    exact (Nat.div_add_mod k fmt.beta).symm
  have hr : r < fmt.beta := by
    rw [show r = k % fmt.beta by rfl]
    exact Nat.mod_lt k (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hlo' : fmt.beta ^ fmt.t ≤ k := by
    simpa [k, shift] using hlo
  have hhi' : k < 2 * fmt.beta ^ fmt.t := by
    simpa [k, shift] using hhi
  have hemin : fmt.exponentInRange fmt.emin :=
    ⟨le_rfl, fmt.emin_le_emax⟩
  have hsource :
      fmt.normalizedValue true m e + fmt.subnormalValue false n =
        fmt.signValue true * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
    rw [hshift]
    simp [k, subnormalValue, signValue, Nat.cast_sub hcoeff_le',
      Nat.cast_mul, Nat.cast_pow]
    ring
  have hpolicy' :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) y := by
    simpa [hsource] using hpolicy
  have hfin :
      fmt.finiteSystem
        ((fmt.signValue true * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) - y) :=
    fmt.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_guardCoeffBounds
      hbeta hemin hk hr hlo' hhi' hpolicy'
  simpa [hsource] using hfin
/-- Operation-level positive mixed normal/subnormal opposite-sign addition has
finite local error in the one-guard aligned-difference branch. -/
theorem finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff_le :
      n ≤ m * fmt.beta ^ Int.toNat (e - fmt.emin))
    (hlo :
      fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) - n)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) - n <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false m e + fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e + fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue true n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e + fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue true n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_subnormal_error_finiteSystem_of_guardCoeffBounds
      hbeta hm hn he hcoeff_le hlo hhi hpolicy
/-- Operation-level negative mixed normal/subnormal opposite-sign addition has
finite local error in the one-guard aligned-difference branch. -/
theorem finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff_le :
      n ≤ m * fmt.beta ^ Int.toNat (e - fmt.emin))
    (hlo :
      fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) - n)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) - n <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true m e + fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e + fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue false n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e + fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue false n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_subnormal_error_finiteSystem_of_guardCoeffBounds
      hbeta hm hn he hcoeff_le hlo hhi hpolicy
/-- Positive mixed normal/subnormal opposite-sign addition has finite local
error under source evidence from a supplied multi-guard scaled range. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_subnormal_error_finiteSystem_of_multiGuardScaleRange
    {fmt : FloatingPointFormat}
    {y : ℝ} {m n d : ℕ} {e : ℤ}
    (_hm : fmt.normalizedMantissa m)
    (_hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff_le :
      n ≤ m * fmt.beta ^ Int.toNat (e - fmt.emin))
    (hdle : d ≤ fmt.t)
    (hlo :
      fmt.beta ^ d * fmt.minNormalMantissa ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) - n)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) - n <
        fmt.beta ^ d * (fmt.maxNormalMantissa + 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e + fmt.subnormalValue true n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e + fmt.subnormalValue true n) - y) := by
  let shift := Int.toNat (e - fmt.emin)
  let k : ℕ := m * fmt.beta ^ shift - n
  let q : ℕ := k / fmt.beta ^ d
  let r : ℕ := k % fmt.beta ^ d
  have hpow_pos : 0 < fmt.beta ^ d :=
    Nat.pow_pos (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hshift_cast : ((shift : ℕ) : ℤ) = e - fmt.emin := by
    have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr he.1
    simpa [shift] using Int.toNat_of_nonneg hnonneg
  have hshift_endpoint : e - (shift : ℤ) = fmt.emin := by
    omega
  have hcoeff_le' : n ≤ m * fmt.beta ^ shift := by
    simpa [shift] using hcoeff_le
  have hshift :
      fmt.normalizedValue false m e =
        fmt.subnormalValue false (m * fmt.beta ^ shift) :=
    fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
      (negative := false) (m := m) (shift := shift) (e := e)
      hshift_endpoint
  have hk :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) - n =
        fmt.beta ^ d * q + r := by
    change k = fmt.beta ^ d * (k / fmt.beta ^ d) + k % fmt.beta ^ d
    exact (Nat.div_add_mod k (fmt.beta ^ d)).symm
  have hr : r < fmt.beta ^ d := by
    rw [show r = k % fmt.beta ^ d by rfl]
    exact Nat.mod_lt k hpow_pos
  have hlo' : fmt.beta ^ d * fmt.minNormalMantissa ≤ k := by
    simpa [k, shift] using hlo
  have hhi' : k < fmt.beta ^ d * (fmt.maxNormalMantissa + 1) := by
    simpa [k, shift] using hhi
  have hemin : fmt.exponentInRange fmt.emin :=
    ⟨le_rfl, fmt.emin_le_emax⟩
  have hsource :
      fmt.normalizedValue false m e + fmt.subnormalValue true n =
        ((k : ℕ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
    rw [hshift]
    simp [k, subnormalValue, signValue, Nat.cast_sub hcoeff_le',
      Nat.cast_mul, Nat.cast_pow]
    ring
  have hpolicy' :
      fmt.sourceRoundToEvenEvidence
        (((k : ℕ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) y := by
    simpa [hsource] using hpolicy
  have hfin :
      fmt.finiteSystem
        ((((k : ℕ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) - y) :=
    fmt.sourceRoundToEvenEvidence_positive_multiGuard_error_finiteSystem_of_scaledMantissaRange
      hemin hdle hk hr hlo' hhi' hpolicy'
  simpa [hsource] using hfin
/-- Negative mixed normal/subnormal opposite-sign addition has finite local
error under source evidence from a supplied multi-guard scaled range. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_subnormal_error_finiteSystem_of_multiGuardScaleRange
    {fmt : FloatingPointFormat}
    {y : ℝ} {m n d : ℕ} {e : ℤ}
    (_hm : fmt.normalizedMantissa m)
    (_hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff_le :
      n ≤ m * fmt.beta ^ Int.toNat (e - fmt.emin))
    (hdle : d ≤ fmt.t)
    (hlo :
      fmt.beta ^ d * fmt.minNormalMantissa ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) - n)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) - n <
        fmt.beta ^ d * (fmt.maxNormalMantissa + 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e + fmt.subnormalValue false n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e + fmt.subnormalValue false n) - y) := by
  let shift := Int.toNat (e - fmt.emin)
  let k : ℕ := m * fmt.beta ^ shift - n
  let q : ℕ := k / fmt.beta ^ d
  let r : ℕ := k % fmt.beta ^ d
  have hpow_pos : 0 < fmt.beta ^ d :=
    Nat.pow_pos (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hshift_cast : ((shift : ℕ) : ℤ) = e - fmt.emin := by
    have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr he.1
    simpa [shift] using Int.toNat_of_nonneg hnonneg
  have hshift_endpoint : e - (shift : ℤ) = fmt.emin := by
    omega
  have hcoeff_le' : n ≤ m * fmt.beta ^ shift := by
    simpa [shift] using hcoeff_le
  have hshift :
      fmt.normalizedValue true m e =
        fmt.subnormalValue true (m * fmt.beta ^ shift) :=
    fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
      (negative := true) (m := m) (shift := shift) (e := e)
      hshift_endpoint
  have hk :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) - n =
        fmt.beta ^ d * q + r := by
    change k = fmt.beta ^ d * (k / fmt.beta ^ d) + k % fmt.beta ^ d
    exact (Nat.div_add_mod k (fmt.beta ^ d)).symm
  have hr : r < fmt.beta ^ d := by
    rw [show r = k % fmt.beta ^ d by rfl]
    exact Nat.mod_lt k hpow_pos
  have hlo' : fmt.beta ^ d * fmt.minNormalMantissa ≤ k := by
    simpa [k, shift] using hlo
  have hhi' : k < fmt.beta ^ d * (fmt.maxNormalMantissa + 1) := by
    simpa [k, shift] using hhi
  have hemin : fmt.exponentInRange fmt.emin :=
    ⟨le_rfl, fmt.emin_le_emax⟩
  have hsource :
      fmt.normalizedValue true m e + fmt.subnormalValue false n =
        fmt.signValue true * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
    rw [hshift]
    simp [k, subnormalValue, signValue, Nat.cast_sub hcoeff_le',
      Nat.cast_mul, Nat.cast_pow]
    ring
  have hpolicy' :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) y := by
    simpa [hsource] using hpolicy
  have hfin :
      fmt.finiteSystem
        ((fmt.signValue true * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) - y) :=
    fmt.sourceRoundToEvenEvidence_negative_multiGuard_error_finiteSystem_of_scaledMantissaRange
      hemin hdle hk hr hlo' hhi' hpolicy'
  simpa [hsource] using hfin
/-- Positive mixed opposite-sign addition has finite local error in the base-2
multi-guard coefficient range. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_subnormal_error_finiteSystem_of_multiGuardCoefficientBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff_le :
      n ≤ m * fmt.beta ^ Int.toNat (e - fmt.emin))
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) - n)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) - n <
        fmt.beta ^ (2 * fmt.t))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e + fmt.subnormalValue true n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e + fmt.subnormalValue true n) - y) := by
  rcases fmt.multiGuardScaleRange_exists_of_baseTwo_bounds hbeta hlo hhi with
    ⟨d, hdle, hrange_lo, hrange_hi⟩
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_subnormal_error_finiteSystem_of_multiGuardScaleRange
      hm hn he hcoeff_le hdle hrange_lo hrange_hi hpolicy
/-- Negative mixed opposite-sign addition has finite local error in the base-2
multi-guard coefficient range. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_subnormal_error_finiteSystem_of_multiGuardCoefficientBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff_le :
      n ≤ m * fmt.beta ^ Int.toNat (e - fmt.emin))
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) - n)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) - n <
        fmt.beta ^ (2 * fmt.t))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e + fmt.subnormalValue false n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e + fmt.subnormalValue false n) - y) := by
  rcases fmt.multiGuardScaleRange_exists_of_baseTwo_bounds hbeta hlo hhi with
    ⟨d, hdle, hrange_lo, hrange_hi⟩
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_subnormal_error_finiteSystem_of_multiGuardScaleRange
      hm hn he hcoeff_le hdle hrange_lo hrange_hi hpolicy
/-- Base-two upper bound for the mixed opposite-sign aligned-difference
coefficient inside the subnormal precision window. -/
theorem mixedAlignedDiffCoeff_lt_two_precision_bound_of_normalized_subnormal_window
    {fmt : FloatingPointFormat}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hwindow : fmt.emin + (fmt.t : ℤ) > e) :
    m * fmt.beta ^ Int.toNat (e - fmt.emin) - n <
      fmt.beta ^ (2 * fmt.t) := by
  have hplus :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        fmt.beta ^ (2 * fmt.t) :=
    fmt.mixedAlignedCoeff_lt_two_precision_bound_of_normalized_subnormal_window
      hm hn he hwindow
  calc
    m * fmt.beta ^ Int.toNat (e - fmt.emin) - n
        ≤ m * fmt.beta ^ Int.toNat (e - fmt.emin) := Nat.sub_le _ _
    _ ≤ m * fmt.beta ^ Int.toNat (e - fmt.emin) + n :=
        Nat.le_add_right _ _
    _ < fmt.beta ^ (2 * fmt.t) := hplus
/-- Positive mixed opposite-sign addition has finite local error in the
complementary multi-guard precision-window region. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_subnormal_error_finiteSystem_of_multiGuardComplementaryRegion
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff_le :
      n ≤ m * fmt.beta ^ Int.toNat (e - fmt.emin))
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) - n)
    (hwindow : fmt.emin + (fmt.t : ℤ) > e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e + fmt.subnormalValue true n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e + fmt.subnormalValue true n) - y) := by
  have hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) - n <
        fmt.beta ^ (2 * fmt.t) :=
    fmt.mixedAlignedDiffCoeff_lt_two_precision_bound_of_normalized_subnormal_window
      hm hn he hwindow
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_subnormal_error_finiteSystem_of_multiGuardCoefficientBounds
      hbeta hm hn he hcoeff_le hlo hhi hpolicy
/-- Negative mixed opposite-sign addition has finite local error in the
complementary multi-guard precision-window region. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_subnormal_error_finiteSystem_of_multiGuardComplementaryRegion
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff_le :
      n ≤ m * fmt.beta ^ Int.toNat (e - fmt.emin))
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) - n)
    (hwindow : fmt.emin + (fmt.t : ℤ) > e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e + fmt.subnormalValue false n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e + fmt.subnormalValue false n) - y) := by
  have hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) - n <
        fmt.beta ^ (2 * fmt.t) :=
    fmt.mixedAlignedDiffCoeff_lt_two_precision_bound_of_normalized_subnormal_window
      hm hn he hwindow
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_subnormal_error_finiteSystem_of_multiGuardCoefficientBounds
      hbeta hm hn he hcoeff_le hlo hhi hpolicy
/-- Operation-level positive mixed opposite-sign addition has finite local
error in the complementary multi-guard precision-window region. -/
theorem finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_multiGuardComplementaryRegion
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff_le :
      n ≤ m * fmt.beta ^ Int.toNat (e - fmt.emin))
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) - n)
    (hwindow : fmt.emin + (fmt.t : ℤ) > e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false m e + fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e + fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue true n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e + fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue true n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_subnormal_error_finiteSystem_of_multiGuardComplementaryRegion
      hbeta hm hn he hcoeff_le hlo hwindow hpolicy
/-- Operation-level negative mixed opposite-sign addition has finite local
error in the complementary multi-guard precision-window region. -/
theorem finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_multiGuardComplementaryRegion
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff_le :
      n ≤ m * fmt.beta ^ Int.toNat (e - fmt.emin))
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) - n)
    (hwindow : fmt.emin + (fmt.t : ℤ) > e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true m e + fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e + fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue false n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e + fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue false n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_subnormal_error_finiteSystem_of_multiGuardComplementaryRegion
      hbeta hm hn he hcoeff_le hlo hwindow hpolicy
/-- Positive same-sign mixed normal/subnormal addition has finite local error
when the subnormal addend lies strictly inside the left half-cell of the normal
operand.

This is the mixed large-alignment analogue of the normalized/normalized
strict-left branch: source round-to-even selects the normal operand, and the
local error is exactly the finite subnormal addend. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue false n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.subnormalValue false n) - y) := by
  let a := fmt.normalizedValue false m e
  let b := fmt.normalizedValue false (m + 1) e
  let low := fmt.subnormalValue false n
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.subnormalValue_false_pos hn
  have hulp_pos : 0 < fmt.ulpAtExponent e := fmt.ulpAtExponent_pos e
  have hlow_lt_ulp : low < fmt.ulpAtExponent e := by
    linarith
  have hb_sub_a : b - a = fmt.ulpAtExponent e := by
    dsimp [a, b]
    simpa [ulpAtExponent, signValue] using
      (fmt.normalizedValue_succ_sub_sameExponent false m e)
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, m, e, hm, hmSucc, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have ha_lt_source : a < a + low := by
    linarith
  have hsource_lt_b : a + low < b := by
    linarith
  have hleft_abs : |(a + low) - a| = low := by
    have hsub : (a + low) - a = low := by ring
    rw [hsub, abs_of_pos hlow_pos]
  have hright_abs :
      |(a + low) - b| = fmt.ulpAtExponent e - low := by
    have hsub : (a + low) - b = low - fmt.ulpAtExponent e := by
      linarith
    have hneg : low - fmt.ulpAtExponent e < 0 := by
      linarith
    rw [hsub, abs_of_neg hneg]
    ring
  have hleftCloser : |(a + low) - a| < |(a + low) - b| := by
    rw [hleft_abs, hright_abs]
    linarith
  have hy : y = a := by
    exact
      fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
        hpolicy hadj ⟨ha_lt_source, hsource_lt_b⟩ hleftCloser
  have hlow_fin : fmt.finiteSystem low :=
    Or.inr (Or.inr ⟨false, n, hn, rfl⟩)
  rw [hy]
  convert hlow_fin using 1
  dsimp [a, low]
  ring
/-- Operation-level positive same-sign mixed normal/subnormal addition has
finite representable local roundoff error in the strict left half-cell branch. -/
theorem finiteRoundToEvenOp_add_positive_normalized_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false m e +
          fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue false n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue false n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
      hm hmSucc hn hlow hpolicy
/-- Commuted operation-level positive same-sign mixed subnormal/normal addition
has finite representable local roundoff error in the strict left half-cell
branch. -/
theorem finiteRoundToEvenOp_add_positive_subnormal_sameSign_normalized_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue false n +
          fmt.normalizedValue false m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue false n +
          fmt.normalizedValue false m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue false m e)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.subnormalValue false n +
          fmt.normalizedValue false m e)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue false m e)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue false m e)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue false m e +
            fmt.subnormalValue false n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.subnormalValue false n)
            (fmt.normalizedValue false m e)) :=
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
      hm hmSucc hn hlow hpolicy
  convert hfin using 1
  ring
/-- Negative same-sign mixed normal/subnormal addition has finite local error in
the strict left half-cell branch by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e +
          fmt.subnormalValue true n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e +
          fmt.subnormalValue true n) - y) := by
  have hsource_neg :
      -(fmt.normalizedValue true m e + fmt.subnormalValue true n) =
        fmt.normalizedValue false m e + fmt.subnormalValue false n := by
    simp [normalizedValue, subnormalValue, signValue]
    ring
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue false n) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    simpa [hsource_neg] using hneg
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false m e +
            fmt.subnormalValue false n) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
      hm hmSucc hn hlow hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [normalizedValue, subnormalValue, signValue]
  ring
/-- Operation-level negative same-sign mixed normal/subnormal addition has
finite representable local roundoff error in the strict left half-cell branch. -/
theorem finiteRoundToEvenOp_add_negative_normalized_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true m e +
          fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue true n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e +
          fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue true n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
      hbeta ht hm hmSucc hn hlow hpolicy
/-- Commuted operation-level negative same-sign mixed subnormal/normal addition
has finite representable local roundoff error in the strict left half-cell
branch. -/
theorem finiteRoundToEvenOp_add_negative_subnormal_sameSign_normalized_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue true n +
          fmt.normalizedValue true m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue true n +
          fmt.normalizedValue true m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue true m e)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.subnormalValue true n +
          fmt.normalizedValue true m e)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue true m e)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e +
          fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue true m e)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue true m e +
            fmt.subnormalValue true n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.subnormalValue true n)
            (fmt.normalizedValue true m e)) :=
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
      hbeta ht hm hmSucc hn hlow hpolicy
  convert hfin using 1
  ring
/-- Positive same-sign mixed normal/subnormal addition has finite local error in
the strict left half-cell branch when the normal operand is the largest
mantissa of its exponent. -/
theorem sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n) - y) := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa e
  let b := fmt.normalizedValue false fmt.minNormalMantissa (e + 1)
  let low := fmt.subnormalValue false n
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.subnormalValue_false_pos hn
  have hulp_pos : 0 < fmt.ulpAtExponent e := fmt.ulpAtExponent_pos e
  have hlow_lt_ulp : low < fmt.ulpAtExponent e := by
    linarith
  have hb_sub_a : b - a = fmt.ulpAtExponent e := by
    dsimp [a, b]
    simpa [ulpAtExponent, signValue] using
      (fmt.normalizedValue_boundary_sub false e)
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, e, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have ha_lt_source : a < a + low := by
    linarith
  have hsource_lt_b : a + low < b := by
    linarith
  have hleft_abs : |(a + low) - a| = low := by
    have hsub : (a + low) - a = low := by ring
    rw [hsub, abs_of_pos hlow_pos]
  have hright_abs :
      |(a + low) - b| = fmt.ulpAtExponent e - low := by
    have hsub : (a + low) - b = low - fmt.ulpAtExponent e := by
      linarith
    have hneg : low - fmt.ulpAtExponent e < 0 := by
      linarith
    rw [hsub, abs_of_neg hneg]
    ring
  have hleftCloser : |(a + low) - a| < |(a + low) - b| := by
    rw [hleft_abs, hright_abs]
    linarith
  have hy : y = a := by
    exact
      fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
        hpolicy hadj ⟨ha_lt_source, hsource_lt_b⟩ hleftCloser
  have hlow_fin : fmt.finiteSystem low :=
    Or.inr (Or.inr ⟨false, n, hn, rfl⟩)
  rw [hy]
  convert hlow_fin using 1
  dsimp [a, low]
  ring
/-- Operation-level positive same-sign mixed max-normal/subnormal addition has
finite representable local roundoff error in the strict left half-cell branch. -/
theorem finiteRoundToEvenOp_add_positive_max_normalized_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat}
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.maxNormalMantissa e)
          (fmt.subnormalValue false n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.maxNormalMantissa e)
          (fmt.subnormalValue false n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
      hn hlow hpolicy
/-- Commuted operation-level positive same-sign mixed subnormal/max-normal
addition has finite representable local roundoff error in the strict left
half-cell branch. -/
theorem finiteRoundToEvenOp_add_positive_subnormal_sameSign_max_normalized_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat}
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue false n +
          fmt.normalizedValue false fmt.maxNormalMantissa e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue false n +
          fmt.normalizedValue false fmt.maxNormalMantissa e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue false fmt.maxNormalMantissa e)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.subnormalValue false n +
          fmt.normalizedValue false fmt.maxNormalMantissa e)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue false fmt.maxNormalMantissa e)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue false fmt.maxNormalMantissa e)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue false fmt.maxNormalMantissa e +
            fmt.subnormalValue false n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.subnormalValue false n)
            (fmt.normalizedValue false fmt.maxNormalMantissa e)) :=
    fmt.sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
      hn hlow hpolicy
  convert hfin using 1
  ring
/-- Negative same-sign mixed max-normal/subnormal addition has finite local
error in the strict left half-cell branch by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n) - y) := by
  have hsource_neg :
      -(fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n) =
        fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n := by
    simp [normalizedValue, subnormalValue, signValue]
    ring
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    simpa [hsource_neg] using hneg
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false fmt.maxNormalMantissa e +
            fmt.subnormalValue false n) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
      hn hlow hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [normalizedValue, subnormalValue, signValue]
  ring
/-- Operation-level negative same-sign mixed max-normal/subnormal addition has
finite representable local roundoff error in the strict left half-cell branch. -/
theorem finiteRoundToEvenOp_add_negative_max_normalized_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.maxNormalMantissa e)
          (fmt.subnormalValue true n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.maxNormalMantissa e)
          (fmt.subnormalValue true n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
      hbeta ht hn hlow hpolicy
/-- Commuted operation-level negative same-sign mixed subnormal/max-normal
addition has finite representable local roundoff error in the strict left
half-cell branch. -/
theorem finiteRoundToEvenOp_add_negative_subnormal_sameSign_max_normalized_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue true n +
          fmt.normalizedValue true fmt.maxNormalMantissa e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue true n +
          fmt.normalizedValue true fmt.maxNormalMantissa e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue true fmt.maxNormalMantissa e)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.subnormalValue true n +
          fmt.normalizedValue true fmt.maxNormalMantissa e)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue true fmt.maxNormalMantissa e)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue true fmt.maxNormalMantissa e)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue true fmt.maxNormalMantissa e +
            fmt.subnormalValue true n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.subnormalValue true n)
            (fmt.normalizedValue true fmt.maxNormalMantissa e)) :=
    fmt.sourceRoundToEvenEvidence_negative_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
      hbeta ht hn hlow hpolicy
  convert hfin using 1
  ring
/-- A positive subnormal addend is strictly inside the left half-cell of any
normal exponent at least one precision window above `emin`.

At `e = emin + t`, one half ulp is exactly the smallest normal magnitude; for
larger exponents it is still larger.  Every subnormal is strictly below that
boundary. -/
theorem subnormalValue_false_lt_half_ulpAtExponent_of_exponent_gap_ge_t
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hgap : fmt.emin + (fmt.t : ℤ) ≤ e) :
    fmt.subnormalValue false n <
      (1 / 2 : ℝ) * fmt.ulpAtExponent e := by
  have hlow_pos : 0 < fmt.subnormalValue false n :=
    fmt.subnormalValue_false_pos hn
  have hlow_lt_min :
      fmt.subnormalValue false n < fmt.betaR ^ (fmt.emin - 1) := by
    have h := fmt.subnormalValue_abs_lt_min_normal
      (negative := false) hn
    simpa [abs_of_pos hlow_pos] using h
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  have hbetaR : fmt.betaR = 2 := by
    simp [betaR, hbeta]
  have hpow_le :
      fmt.betaR ^ (fmt.emin - 1) ≤
        fmt.betaR ^ (e - (fmt.t : ℤ) - 1) :=
    fmt.betaR_zpow_le_zpow_of_le (by omega)
  have hhalf_eq :
      (1 / 2 : ℝ) * fmt.ulpAtExponent e =
        fmt.betaR ^ (e - (fmt.t : ℤ) - 1) := by
    rw [ulpAtExponent]
    rw [show e - (fmt.t : ℤ) =
      (e - (fmt.t : ℤ) - 1) + (1 : ℤ) by ring]
    rw [zpow_add₀ hbase, zpow_one, hbetaR]
    rw [show e - (fmt.t : ℤ) - 1 + 1 - 1 =
      e - (fmt.t : ℤ) - 1 by ring]
    rw [mul_comm (2 ^ (e - (fmt.t : ℤ) - 1)) 2]
    rw [← mul_assoc]
    norm_num
    change (1 : ℝ) * 2 ^ (e - (fmt.t : ℤ) - 1) =
      2 ^ (e - (fmt.t : ℤ) - 1)
    rw [one_mul]
  exact lt_of_lt_of_le hlow_lt_min (by rw [hhalf_eq]; exact hpow_le)
/-- Positive normal plus negative subnormal has finite local error in the
strict predecessor half-cell, provided the high normal has a same-exponent
predecessor. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_subnormal_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue true n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.subnormalValue true n) - y) := by
  let a := fmt.normalizedValue false (m - 1) e
  let b := fmt.normalizedValue false m e
  let low := fmt.subnormalValue false n
  have hmPred : fmt.normalizedMantissa (m - 1) :=
    fmt.normalizedMantissa_pred_of_ne_minNormalMantissa hm hneMin
  have hm_pos : 0 < m := fmt.normalizedMantissa_pos hm
  have hpred_succ : (m - 1) + 1 = m := by
    omega
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.subnormalValue_false_pos hn
  have hlow_lt_ulp : low < fmt.ulpAtExponent e := by
    have hulp_pos : 0 < fmt.ulpAtExponent e := fmt.ulpAtExponent_pos e
    linarith
  have hb_sub_a : b - a = fmt.ulpAtExponent e := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_succ_sub_sameExponent false (m - 1) e)
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, m - 1, e, hmPred, ?_, Or.inl ?_⟩
    · simpa [hpred_succ] using hm
    · exact ⟨rfl, by dsimp [b]; rw [hpred_succ]⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hsource_eq :
      fmt.normalizedValue false m e + fmt.subnormalValue true n =
        b - low := by
    dsimp [b, low]
    simp [subnormalValue, signValue]
    ring
  have hpolicy' : fmt.sourceRoundToEvenEvidence (b - low) y := by
    simpa [hsource_eq] using hpolicy
  have ha_lt_source : a < b - low := by
    linarith
  have hsource_lt_b : b - low < b := by
    linarith
  have hright_abs : |(b - low) - b| = low := by
    have hsub : (b - low) - b = -low := by ring
    rw [hsub, abs_neg, abs_of_pos hlow_pos]
  have hleft_abs :
      |(b - low) - a| = fmt.ulpAtExponent e - low := by
    have hsub : (b - low) - a = fmt.ulpAtExponent e - low := by
      linarith
    have hpos : 0 < fmt.ulpAtExponent e - low := by
      linarith
    rw [hsub, abs_of_pos hpos]
  have hrightCloser : |(b - low) - b| < |(b - low) - a| := by
    rw [hright_abs, hleft_abs]
    linarith
  have hy : y = b := by
    exact
      fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
        hpolicy' hadj ⟨ha_lt_source, hsource_lt_b⟩ hrightCloser
  have hlow_fin : fmt.finiteSystem low :=
    Or.inr (Or.inr ⟨false, n, hn, rfl⟩)
  have hneg_low_fin := fmt.finiteSystem_neg hlow_fin
  rw [hy]
  convert hneg_low_fin using 1
  dsimp [b, low]
  simp [subnormalValue, signValue]
/-- Operation-level positive normal plus negative subnormal has finite local
error in the strict predecessor half-cell. -/
theorem finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false m e +
          fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue true n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue true n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_subnormal_error_finiteSystem_of_low_lt_half_ulp
      hm hneMin hn hlow hpolicy
/-- Negative normal plus positive subnormal has finite local error in the
strict predecessor half-cell by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_subnormal_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e +
          fmt.subnormalValue false n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e +
          fmt.subnormalValue false n) - y) := by
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue true n) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    convert hneg using 1
    simp [normalizedValue, subnormalValue, signValue]
    ring
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false m e +
            fmt.subnormalValue true n) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_subnormal_error_finiteSystem_of_low_lt_half_ulp
      hm hneMin hn hlow hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [normalizedValue, subnormalValue, signValue]
  ring
/-- Operation-level negative normal plus positive subnormal has finite local
error in the strict predecessor half-cell. -/
theorem finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true m e +
          fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue false n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e +
          fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue false n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_subnormal_error_finiteSystem_of_low_lt_half_ulp
      hbeta ht hm hneMin hn hlow hpolicy
/-- Operation-level positive normal plus negative subnormal has finite local
error when the normal exponent is at least one precision window above
`emin`. -/
theorem finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_exponent_gap_ge_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (hgap : fmt.emin + (fmt.t : ℤ) ≤ e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false m e +
          fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue true n)) := by
  have hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e :=
    fmt.subnormalValue_false_lt_half_ulpAtExponent_of_exponent_gap_ge_t
      hbeta hn hgap
  exact
    fmt.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_low_lt_half_ulp
      hm hneMin hn hlow hxy
/-- Operation-level negative normal plus positive subnormal has finite local
error when the normal exponent is at least one precision window above
`emin`. -/
theorem finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_exponent_gap_ge_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (hgap : fmt.emin + (fmt.t : ℤ) ≤ e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true m e +
          fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue false n)) := by
  have hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e :=
    fmt.subnormalValue_false_lt_half_ulpAtExponent_of_exponent_gap_ge_t
      hbeta hn hgap
  exact
    fmt.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_low_lt_half_ulp
      hbeta ht hm hneMin hn hlow hxy
/-- Positive minimum normal plus negative subnormal has finite local error in
the strict half-cell around the boundary predecessor. -/
theorem sourceRoundToEvenEvidence_positive_min_normalizedValue_add_neg_subnormal_error_finiteSystem_of_low_lt_half_pred_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n) - y) := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa (eHigh - 1)
  let b := fmt.normalizedValue false fmt.minNormalMantissa eHigh
  let low := fmt.subnormalValue false n
  have hpred_succ : eHigh - 1 + 1 = eHigh := by
    ring
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.subnormalValue_false_pos hn
  have hlow_lt_ulp : low < fmt.ulpAtExponent (eHigh - 1) := by
    have hulp_pos : 0 < fmt.ulpAtExponent (eHigh - 1) :=
      fmt.ulpAtExponent_pos (eHigh - 1)
    linarith
  have hb_sub_a : b - a = fmt.ulpAtExponent (eHigh - 1) := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_boundary_sub false (eHigh - 1))
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, eHigh - 1, Or.inl ?_⟩
    exact ⟨rfl, by dsimp [b]; rw [hpred_succ]⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hsource_eq :
      fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n =
        b - low := by
    dsimp [b, low]
    simp [subnormalValue, signValue]
    ring
  have hpolicy' : fmt.sourceRoundToEvenEvidence (b - low) y := by
    simpa [hsource_eq] using hpolicy
  have ha_lt_source : a < b - low := by
    linarith
  have hsource_lt_b : b - low < b := by
    linarith
  have hright_abs : |(b - low) - b| = low := by
    have hsub : (b - low) - b = -low := by ring
    rw [hsub, abs_neg, abs_of_pos hlow_pos]
  have hleft_abs :
      |(b - low) - a| = fmt.ulpAtExponent (eHigh - 1) - low := by
    have hsub :
        (b - low) - a = fmt.ulpAtExponent (eHigh - 1) - low := by
      linarith
    have hpos : 0 < fmt.ulpAtExponent (eHigh - 1) - low := by
      linarith
    rw [hsub, abs_of_pos hpos]
  have hrightCloser : |(b - low) - b| < |(b - low) - a| := by
    rw [hright_abs, hleft_abs]
    linarith
  have hy : y = b := by
    exact
      fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
        hpolicy' hadj ⟨ha_lt_source, hsource_lt_b⟩ hrightCloser
  have hlow_fin : fmt.finiteSystem low :=
    Or.inr (Or.inr ⟨false, n, hn, rfl⟩)
  have hneg_low_fin := fmt.finiteSystem_neg hlow_fin
  rw [hy]
  convert hneg_low_fin using 1
  dsimp [b, low]
  simp [subnormalValue, signValue]
/-- Operation-level positive minimum normal plus negative subnormal has finite
local error in the strict boundary predecessor half-cell. -/
theorem finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_error_finiteSystem_of_low_lt_half_pred_ulp
    {fmt : FloatingPointFormat}
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue true n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue true n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_min_normalizedValue_add_neg_subnormal_error_finiteSystem_of_low_lt_half_pred_ulp
      hn hlow hpolicy
/-- Negative minimum normal plus positive subnormal has finite local error in
the strict boundary predecessor half-cell by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_min_normalizedValue_add_pos_subnormal_error_finiteSystem_of_low_lt_half_pred_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n) - y) := by
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    convert hneg using 1
    simp [normalizedValue, subnormalValue, signValue]
    ring
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
            fmt.subnormalValue true n) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_min_normalizedValue_add_neg_subnormal_error_finiteSystem_of_low_lt_half_pred_ulp
      hn hlow hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [normalizedValue, subnormalValue, signValue]
  ring
/-- Operation-level negative minimum normal plus positive subnormal has finite
local error in the strict boundary predecessor half-cell. -/
theorem finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_error_finiteSystem_of_low_lt_half_pred_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue false n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue false n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_min_normalizedValue_add_pos_subnormal_error_finiteSystem_of_low_lt_half_pred_ulp
      hbeta ht hn hlow hpolicy
/-- Operation-level positive minimum normal plus negative subnormal has finite
local error when the boundary predecessor exponent is at least one precision
window above `emin`. -/
theorem finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_error_finiteSystem_of_exponent_gap_ge_t_pred
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hgap : fmt.emin + (fmt.t : ℤ) ≤ eHigh - 1)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue true n)) := by
  have hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) :=
    fmt.subnormalValue_false_lt_half_ulpAtExponent_of_exponent_gap_ge_t
      hbeta hn hgap
  exact
    fmt.finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_error_finiteSystem_of_low_lt_half_pred_ulp
      hn hlow hxy
/-- Operation-level negative minimum normal plus positive subnormal has finite
local error when the boundary predecessor exponent is at least one precision
window above `emin`. -/
theorem finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_error_finiteSystem_of_exponent_gap_ge_t_pred
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hgap : fmt.emin + (fmt.t : ℤ) ≤ eHigh - 1)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue false n)) := by
  have hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) :=
    fmt.subnormalValue_false_lt_half_ulpAtExponent_of_exponent_gap_ge_t
      hbeta hn hgap
  exact
    fmt.finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_error_finiteSystem_of_low_lt_half_pred_ulp
      hbeta ht hn hlow hxy
/-- In the minimum-boundary mixed right half-cell branch, the residual
subnormal-lattice coefficient at the predecessor exponent has fewer than `t`
radix digits. -/
theorem subnormal_pred_right_half_coeff_gap_of_half_pred_ulp_lt
    {fmt : FloatingPointFormat} {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (heminPred : fmt.emin ≤ eHigh - 1)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) <
        fmt.subnormalValue false n) :
    (((n : ℤ) -
          ((fmt.beta ^ Int.toNat ((eHigh - 1) - fmt.emin) : ℕ) : ℤ)).natAbs <
        fmt.beta ^ fmt.t) := by
  let d := Int.toNat ((eHigh - 1) - fmt.emin)
  let s := fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))
  have hs_pos : 0 < s := by
    dsimp [s]
    exact fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ))
  have hd_cast : ((d : ℕ) : ℤ) = (eHigh - 1) - fmt.emin := by
    have hnonneg : 0 ≤ (eHigh - 1) - fmt.emin := sub_nonneg.mpr heminPred
    simpa [d] using Int.toNat_of_nonneg hnonneg
  have hulp_lattice :
      fmt.ulpAtExponent (eHigh - 1) = ((fmt.beta ^ d : ℕ) : ℝ) * s := by
    have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
    have hpow :
        fmt.betaR ^ ((d : ℕ) : ℤ) =
          ((fmt.beta ^ d : ℕ) : ℝ) := by
      rw [zpow_natCast]
      simp [betaR, Nat.cast_pow, d]
    calc
      fmt.ulpAtExponent (eHigh - 1) =
          fmt.betaR ^ ((eHigh - 1) - (fmt.t : ℤ)) := by
        rfl
      _ = fmt.betaR ^ (((d : ℕ) : ℤ) + (fmt.emin - (fmt.t : ℤ))) := by
        congr 1
        omega
      _ = fmt.betaR ^ ((d : ℕ) : ℤ) * s := by
        dsimp [s]
        rw [zpow_add₀ hbase]
      _ = ((fmt.beta ^ d : ℕ) : ℝ) * s := by
        rw [hpow]
  have hlow_lattice :
      fmt.subnormalValue false n = (n : ℝ) * s := by
    dsimp [s]
    simp [subnormalValue, signValue]
  have hhalf_scaled :
      (1 / 2 : ℝ) * ((fmt.beta ^ d : ℕ) : ℝ) < (n : ℝ) := by
    have hscaled :
        ((1 / 2 : ℝ) * ((fmt.beta ^ d : ℕ) : ℝ)) * s <
          (n : ℝ) * s := by
      simpa [hulp_lattice, hlow_lattice, mul_assoc, mul_comm, mul_left_comm]
        using hhalf
    nlinarith [hscaled, hs_pos]
  have hpow_lt_two_n_real :
      ((fmt.beta ^ d : ℕ) : ℝ) < (2 : ℝ) * n := by
    nlinarith
  have hpow_lt_two_n : fmt.beta ^ d < 2 * n := by
    have htmp :
        ((fmt.beta ^ d : ℕ) : ℝ) < ((2 * n : ℕ) : ℝ) := by
      simpa [Nat.cast_mul] using hpow_lt_two_n_real
    exact Nat.cast_lt.mp htmp
  have htwo_n_lt_bound : 2 * n < fmt.beta ^ fmt.t := by
    have h2n_lt : 2 * n < 2 * fmt.minNormalMantissa :=
      Nat.mul_lt_mul_of_pos_left hn.2 (by decide : 0 < 2)
    have h2min_le : 2 * fmt.minNormalMantissa ≤ fmt.beta ^ fmt.t := by
      calc
        2 * fmt.minNormalMantissa ≤ fmt.beta * fmt.minNormalMantissa :=
          Nat.mul_le_mul_right fmt.minNormalMantissa fmt.beta_ge_two
        _ = fmt.beta ^ fmt.t := by
          rw [Nat.mul_comm]
          exact fmt.minNormalMantissa_mul_beta_eq_mantissaBound
    exact lt_of_lt_of_le h2n_lt h2min_le
  have hpow_lt_bound : fmt.beta ^ d < fmt.beta ^ fmt.t :=
    lt_trans hpow_lt_two_n htwo_n_lt_bound
  have hn_lt_bound : n < fmt.beta ^ fmt.t :=
    lt_trans hn.2 fmt.minNormalMantissa_lt_mantissaBound
  have hgap_int :
      ((((n : ℤ) - ((fmt.beta ^ d : ℕ) : ℤ)).natAbs : ℤ) <
        ((fmt.beta ^ fmt.t : ℕ) : ℤ)) := by
    by_cases hnonneg : 0 ≤ (n : ℤ) - ((fmt.beta ^ d : ℕ) : ℤ)
    · have hnatabs :
          ((((n : ℤ) - ((fmt.beta ^ d : ℕ) : ℤ)).natAbs : ℤ) =
            (n : ℤ) - ((fmt.beta ^ d : ℕ) : ℤ)) :=
        Int.natAbs_of_nonneg hnonneg
      omega
    · have hnonneg' : 0 ≤ ((fmt.beta ^ d : ℕ) : ℤ) - (n : ℤ) := by
        omega
      have hnatabs :
          ((((n : ℤ) - ((fmt.beta ^ d : ℕ) : ℤ)).natAbs : ℤ) =
            ((fmt.beta ^ d : ℕ) : ℤ) - (n : ℤ)) := by
        rw [← Int.natAbs_neg]
        have h := Int.natAbs_of_nonneg hnonneg'
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
      omega
  exact_mod_cast hgap_int
/-- Positive minimum normal plus negative subnormal has finite local error at
the boundary predecessor half-ulp tie. -/
theorem sourceRoundToEvenEvidence_positive_min_normalizedValue_add_neg_subnormal_error_finiteSystem_of_low_eq_half_pred_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n) - y) := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa (eHigh - 1)
  let b := fmt.normalizedValue false fmt.minNormalMantissa eHigh
  let low := fmt.subnormalValue false n
  have hpred_succ : eHigh - 1 + 1 = eHigh := by
    ring
  have hlow_eq : low = (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) := by
    simpa [low] using hlow
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.subnormalValue_false_pos hn
  have hulp_pos : 0 < fmt.ulpAtExponent (eHigh - 1) :=
    fmt.ulpAtExponent_pos (eHigh - 1)
  have hlow_lt_ulp : low < fmt.ulpAtExponent (eHigh - 1) := by
    rw [hlow_eq]
    linarith
  have hb_sub_a : b - a = fmt.ulpAtExponent (eHigh - 1) := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_boundary_sub false (eHigh - 1))
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, eHigh - 1, Or.inl ?_⟩
    exact ⟨rfl, by dsimp [b]; rw [hpred_succ]⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hsource_eq :
      fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n =
        b - low := by
    dsimp [b, low]
    simp [subnormalValue, signValue]
    ring
  have hpolicy' : fmt.sourceRoundToEvenEvidence (b - low) y := by
    simpa [hsource_eq] using hpolicy
  have hsource_between : a ≤ b - low ∧ b - low ≤ b := by
    constructor <;> linarith
  have hlow_fin : fmt.finiteSystem low :=
    Or.inr (Or.inr ⟨false, n, hn, rfl⟩)
  rcases
      fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
        hpolicy' hadj hsource_between with hy | hy
  · rw [hy, hsource_eq]
    convert hlow_fin using 1
    have hres : (b - low) - a = low := by
      linarith
    rw [hres]
  · rw [hy, hsource_eq]
    have hneg_low_fin := fmt.finiteSystem_neg hlow_fin
    convert hneg_low_fin using 1
    have hres : (b - low) - b = -low := by
      ring
    rw [hres]
/-- Operation-level positive minimum normal plus negative subnormal has finite
local error at the boundary predecessor half-ulp tie. -/
theorem finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_error_finiteSystem_of_low_eq_half_pred_ulp
    {fmt : FloatingPointFormat}
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue true n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue true n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_min_normalizedValue_add_neg_subnormal_error_finiteSystem_of_low_eq_half_pred_ulp
      hn hlow hpolicy
/-- Negative minimum normal plus positive subnormal has finite local error at
the boundary predecessor half-ulp tie by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_min_normalizedValue_add_pos_subnormal_error_finiteSystem_of_low_eq_half_pred_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n) - y) := by
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    convert hneg using 1
    simp [normalizedValue, subnormalValue, signValue]
    ring
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
            fmt.subnormalValue true n) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_min_normalizedValue_add_neg_subnormal_error_finiteSystem_of_low_eq_half_pred_ulp
      hn hlow hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [normalizedValue, subnormalValue, signValue]
  ring
/-- Operation-level negative minimum normal plus positive subnormal has finite
local error at the boundary predecessor half-ulp tie. -/
theorem finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_error_finiteSystem_of_low_eq_half_pred_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue false n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue false n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_min_normalizedValue_add_pos_subnormal_error_finiteSystem_of_low_eq_half_pred_ulp
      hbeta ht hn hlow hpolicy
/-- Positive minimum normal plus negative subnormal has finite local error in
the strict right half-cell around the boundary predecessor. -/
theorem sourceRoundToEvenEvidence_positive_min_normalizedValue_add_neg_subnormal_error_finiteSystem_of_half_pred_ulp_lt_low_lt_pred_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (heminPred : fmt.emin ≤ eHigh - 1)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent (eHigh - 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n) - y) := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa (eHigh - 1)
  let b := fmt.normalizedValue false fmt.minNormalMantissa eHigh
  let low := fmt.subnormalValue false n
  have hpred_succ : eHigh - 1 + 1 = eHigh := by
    ring
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.subnormalValue_false_pos hn
  have hb_sub_a : b - a = fmt.ulpAtExponent (eHigh - 1) := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_boundary_sub false (eHigh - 1))
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, eHigh - 1, Or.inl ?_⟩
    exact ⟨rfl, by dsimp [b]; rw [hpred_succ]⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hsource_eq :
      fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n =
        b - low := by
    dsimp [b, low]
    simp [subnormalValue, signValue]
    ring
  have hpolicy' : fmt.sourceRoundToEvenEvidence (b - low) y := by
    simpa [hsource_eq] using hpolicy
  have ha_lt_source : a < b - low := by
    linarith
  have hsource_lt_b : b - low < b := by
    linarith
  have hright_abs : |(b - low) - b| = low := by
    have hsub : (b - low) - b = -low := by ring
    rw [hsub, abs_neg, abs_of_pos hlow_pos]
  have hleft_abs :
      |(b - low) - a| = fmt.ulpAtExponent (eHigh - 1) - low := by
    have hsub :
        (b - low) - a = fmt.ulpAtExponent (eHigh - 1) - low := by
      linarith
    have hpos : 0 < fmt.ulpAtExponent (eHigh - 1) - low := by
      linarith
    rw [hsub, abs_of_pos hpos]
  have hleftCloser : |(b - low) - a| < |(b - low) - b| := by
    rw [hright_abs, hleft_abs]
    linarith
  have hy : y = a := by
    exact
      fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
        hpolicy' hadj ⟨ha_lt_source, hsource_lt_b⟩ hleftCloser
  have hd_cast :
      ((Int.toNat ((eHigh - 1) - fmt.emin) : ℕ) : ℤ) =
        (eHigh - 1) - fmt.emin := by
    have hnonneg : 0 ≤ (eHigh - 1) - fmt.emin := sub_nonneg.mpr heminPred
    simpa using Int.toNat_of_nonneg hnonneg
  have hgap0 :
      (((n : ℤ) -
          ((fmt.beta ^ Int.toNat ((eHigh - 1) - fmt.emin) : ℕ) : ℤ)).natAbs <
        fmt.beta ^ fmt.t) :=
    fmt.subnormal_pred_right_half_coeff_gap_of_half_pred_ulp_lt
      hn heminPred hhalf
  have hgap :
      ((((fmt.beta ^ Int.toNat ((eHigh - 1) - fmt.emin) : ℕ) : ℤ) -
          (n : ℤ)).natAbs < fmt.beta ^ fmt.t) := by
    have h := hgap0
    rw [← Int.natAbs_neg] at h
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hulp_lattice :
      fmt.ulpAtExponent (eHigh - 1) =
        ((fmt.beta ^ Int.toNat ((eHigh - 1) - fmt.emin) : ℕ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
    have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
    have hpow :
        fmt.betaR ^ (((Int.toNat ((eHigh - 1) - fmt.emin) : ℕ) : ℤ)) =
          ((fmt.beta ^ Int.toNat ((eHigh - 1) - fmt.emin) : ℕ) : ℝ) := by
      rw [zpow_natCast]
      simp [betaR, Nat.cast_pow]
    calc
      fmt.ulpAtExponent (eHigh - 1) =
          fmt.betaR ^ ((eHigh - 1) - (fmt.t : ℤ)) := by
        rfl
      _ = fmt.betaR ^
            (((Int.toNat ((eHigh - 1) - fmt.emin) : ℕ) : ℤ) +
              (fmt.emin - (fmt.t : ℤ))) := by
        congr 1
        omega
      _ = fmt.betaR ^ (((Int.toNat ((eHigh - 1) - fmt.emin) : ℕ) : ℤ)) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
        rw [zpow_add₀ hbase]
      _ = ((fmt.beta ^ Int.toNat ((eHigh - 1) - fmt.emin) : ℕ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
        rw [hpow]
  have hfin_scaled :
      fmt.finiteSystem
        (fmt.signValue false *
            ((((fmt.beta ^ Int.toNat ((eHigh - 1) - fmt.emin) : ℕ) : ℤ) : ℝ)) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) -
          fmt.signValue false * ((n : ℤ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) :=
    fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := false)
      (k := ((fmt.beta ^ Int.toNat ((eHigh - 1) - fmt.emin) : ℕ) : ℤ))
      (l := (n : ℤ)) (e := fmt.emin)
      ⟨le_rfl, fmt.emin_le_emax⟩ hgap
  rw [hy, hsource_eq]
  change fmt.finiteSystem ((b - low) - a)
  convert hfin_scaled using 1
  have hres : (b - low) - a = fmt.ulpAtExponent (eHigh - 1) - low := by
    linarith
  rw [hres, hulp_lattice]
  dsimp [low]
  simp [subnormalValue, signValue]
/-- Operation-level positive minimum normal plus negative subnormal has finite
local error in the strict boundary predecessor right-half cell. -/
theorem finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_error_finiteSystem_of_half_pred_ulp_lt_low_lt_pred_ulp
    {fmt : FloatingPointFormat}
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (heminPred : fmt.emin ≤ eHigh - 1)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue true n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue true n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_min_normalizedValue_add_neg_subnormal_error_finiteSystem_of_half_pred_ulp_lt_low_lt_pred_ulp
      hn heminPred hhalf hulp hpolicy
/-- Negative minimum normal plus positive subnormal has finite local error in
the strict boundary predecessor right-half cell by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_min_normalizedValue_add_pos_subnormal_error_finiteSystem_of_half_pred_ulp_lt_low_lt_pred_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (heminPred : fmt.emin ≤ eHigh - 1)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent (eHigh - 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n) - y) := by
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    convert hneg using 1
    simp [normalizedValue, subnormalValue, signValue]
    ring
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
            fmt.subnormalValue true n) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_min_normalizedValue_add_neg_subnormal_error_finiteSystem_of_half_pred_ulp_lt_low_lt_pred_ulp
      hn heminPred hhalf hulp hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [normalizedValue, subnormalValue, signValue]
  ring
/-- Operation-level negative minimum normal plus positive subnormal has finite
local error in the strict boundary predecessor right-half cell. -/
theorem finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_error_finiteSystem_of_half_pred_ulp_lt_low_lt_pred_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (heminPred : fmt.emin ≤ eHigh - 1)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue false n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue false n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_min_normalizedValue_add_pos_subnormal_error_finiteSystem_of_half_pred_ulp_lt_low_lt_pred_ulp
      hbeta ht hn heminPred hhalf hulp hpolicy
/-- Positive minimum normal plus negative subnormal is exact when the subnormal
magnitude is exactly one boundary predecessor ulp. -/
theorem finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_eq_exact_of_low_eq_pred_ulp
    {fmt : FloatingPointFormat}
    {n : ℕ} {eHigh : ℤ}
    (_hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n = fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n)) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
        (fmt.subnormalValue true n) =
      fmt.normalizedValue false fmt.minNormalMantissa eHigh +
        fmt.subnormalValue true n := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa (eHigh - 1)
  let b := fmt.normalizedValue false fmt.minNormalMantissa eHigh
  let low := fmt.subnormalValue false n
  have hpred_succ : eHigh - 1 + 1 = eHigh := by
    ring
  have hb_sub_a : b - a = fmt.ulpAtExponent (eHigh - 1) := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_boundary_sub false (eHigh - 1))
  have hsource_eq :
      fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n =
        a := by
    dsimp [a, b, low]
    rw [show fmt.subnormalValue true n = -fmt.subnormalValue false n by
      simpa using fmt.subnormalValue_not_eq_neg false n]
    rw [hlow]
    linarith
  have ha_unbounded : fmt.unboundedNormalizedSystem a :=
    ⟨false, fmt.maxNormalMantissa, eHigh - 1,
      fmt.maxNormalMantissa_normalized, rfl⟩
  have ha_range : fmt.finiteNormalRange a := by
    simpa [hsource_eq] using hxy
  have ha_norm : fmt.normalizedSystem a :=
    fmt.unboundedNormalizedSystem_normalizedSystem_of_finiteNormalRange
      ha_unbounded ha_range
  have hfin_source :
      fmt.finiteSystem
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n) := by
    rw [hsource_eq]
    exact Or.inr (Or.inl ha_norm)
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue false fmt.minNormalMantissa eHigh)
      (y := fmt.subnormalValue true n)
      hfin_source)
/-- The positive minimum-boundary exact predecessor mixed branch has zero local
roundoff error. -/
theorem finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_error_finiteSystem_of_low_eq_pred_ulp
    {fmt : FloatingPointFormat}
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n = fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue true n)) := by
  rw [
    finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_eq_exact_of_low_eq_pred_ulp
      hn hlow hxy]
  simpa using fmt.finiteSystem_zero
/-- Negative minimum normal plus positive subnormal is exact when the subnormal
magnitude is exactly one boundary predecessor ulp. -/
theorem finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_eq_exact_of_low_eq_pred_ulp
    {fmt : FloatingPointFormat}
    {n : ℕ} {eHigh : ℤ}
    (_hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n = fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n)) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
        (fmt.subnormalValue false n) =
      fmt.normalizedValue true fmt.minNormalMantissa eHigh +
        fmt.subnormalValue false n := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa (eHigh - 1)
  let b := fmt.normalizedValue false fmt.minNormalMantissa eHigh
  have hpred_succ : eHigh - 1 + 1 = eHigh := by
    ring
  have hb_sub_a : b - a = fmt.ulpAtExponent (eHigh - 1) := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_boundary_sub false (eHigh - 1))
  have hsource_eq :
      fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n =
        fmt.normalizedValue true fmt.maxNormalMantissa (eHigh - 1) := by
    dsimp [a, b]
    rw [fmt.normalizedValue_true_eq_neg_false, hlow]
    rw [show fmt.normalizedValue true fmt.maxNormalMantissa (eHigh - 1) = -a by
      rw [fmt.normalizedValue_true_eq_neg_false]]
    linarith
  have ha_unbounded :
      fmt.unboundedNormalizedSystem
        (fmt.normalizedValue true fmt.maxNormalMantissa (eHigh - 1)) :=
    ⟨true, fmt.maxNormalMantissa, eHigh - 1,
      fmt.maxNormalMantissa_normalized, rfl⟩
  have ha_range :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.maxNormalMantissa (eHigh - 1)) := by
    simpa [hsource_eq] using hxy
  have ha_norm :
      fmt.normalizedSystem
        (fmt.normalizedValue true fmt.maxNormalMantissa (eHigh - 1)) :=
    fmt.unboundedNormalizedSystem_normalizedSystem_of_finiteNormalRange
      ha_unbounded ha_range
  have hfin_source :
      fmt.finiteSystem
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n) := by
    rw [hsource_eq]
    exact Or.inr (Or.inl ha_norm)
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue true fmt.minNormalMantissa eHigh)
      (y := fmt.subnormalValue false n)
      hfin_source)
/-- The negative minimum-boundary exact predecessor mixed branch has zero local
roundoff error. -/
theorem finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_error_finiteSystem_of_low_eq_pred_ulp
    {fmt : FloatingPointFormat}
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n = fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue false n)) := by
  rw [
    finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_eq_exact_of_low_eq_pred_ulp
      hn hlow hxy]
  simpa using fmt.finiteSystem_zero
/-- Dispatcher for the positive minimum-boundary mixed normal/subnormal
opposite-sign predecessor low-cell split. -/
theorem finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_error_finiteSystem_of_pred_low_cell_cases
    {fmt : FloatingPointFormat}
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (heminPred : fmt.emin ≤ eHigh - 1)
    (hcell :
      fmt.subnormalValue false n <
          (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) ∨
        fmt.subnormalValue false n =
          (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) <
            fmt.subnormalValue false n ∧
          fmt.subnormalValue false n < fmt.ulpAtExponent (eHigh - 1)) ∨
        fmt.subnormalValue false n =
          fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue true n)) := by
  rcases hcell with hlt | hrest
  · exact
      fmt.finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_error_finiteSystem_of_low_lt_half_pred_ulp
        hn hlt hxy
  · rcases hrest with heq | hrest
    · exact
        fmt.finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_error_finiteSystem_of_low_eq_half_pred_ulp
          hn heq hxy
    · rcases hrest with hright | hulp
      · exact
          fmt.finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_error_finiteSystem_of_half_pred_ulp_lt_low_lt_pred_ulp
            hn heminPred hright.1 hright.2 hxy
      · exact
          fmt.finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_error_finiteSystem_of_low_eq_pred_ulp
            hn hulp hxy
/-- Dispatcher for the negative minimum-boundary mixed normal/subnormal
opposite-sign predecessor low-cell split. -/
theorem finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_error_finiteSystem_of_pred_low_cell_cases
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (heminPred : fmt.emin ≤ eHigh - 1)
    (hcell :
      fmt.subnormalValue false n <
          (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) ∨
        fmt.subnormalValue false n =
          (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) <
            fmt.subnormalValue false n ∧
          fmt.subnormalValue false n < fmt.ulpAtExponent (eHigh - 1)) ∨
        fmt.subnormalValue false n =
          fmt.ulpAtExponent (eHigh - 1))
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue false n)) := by
  rcases hcell with hlt | hrest
  · exact
      fmt.finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_error_finiteSystem_of_low_lt_half_pred_ulp
        hbeta ht hn hlt hxy
  · rcases hrest with heq | hrest
    · exact
        fmt.finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_error_finiteSystem_of_low_eq_half_pred_ulp
          hbeta ht hn heq hxy
    · rcases hrest with hright | hulp
      · exact
          fmt.finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_error_finiteSystem_of_half_pred_ulp_lt_low_lt_pred_ulp
            hbeta ht hn heminPred hright.1 hright.2 hxy
      · exact
          fmt.finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_error_finiteSystem_of_low_eq_pred_ulp
            hn hulp hxy
/-- At the mixed minimum-boundary predecessor precision-window exponent, a
positive subnormal lies in the low cell adjacent to the boundary predecessor
ulp. -/
theorem subnormalValue_false_pred_low_cell_cases_of_exponent_eq_emin_add_t_sub_one
    {fmt : FloatingPointFormat}
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hexp : eHigh - 1 = fmt.emin + (fmt.t : ℤ) - 1) :
    fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) ∨
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) ∨
      ((1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) <
          fmt.subnormalValue false n ∧
        fmt.subnormalValue false n < fmt.ulpAtExponent (eHigh - 1)) ∨
      fmt.subnormalValue false n =
        fmt.ulpAtExponent (eHigh - 1) := by
  let low := fmt.subnormalValue false n
  let half := (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1)
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.subnormalValue_false_pos hn
  have hlow_lt_min :
      low < fmt.betaR ^ (fmt.emin - 1) := by
    have h := fmt.subnormalValue_abs_lt_min_normal
      (negative := false) hn
    simpa [low, abs_of_pos hlow_pos] using h
  have hulp_eq :
      fmt.ulpAtExponent (eHigh - 1) = fmt.betaR ^ (fmt.emin - 1) := by
    rw [ulpAtExponent, hexp]
    congr 1
    ring
  have hlow_lt_ulp : low < fmt.ulpAtExponent (eHigh - 1) := by
    simpa [hulp_eq] using hlow_lt_min
  rcases lt_trichotomy low half with hlt | heq | hgt
  · exact Or.inl (by simpa [low, half] using hlt)
  · exact Or.inr (Or.inl (by simpa [low, half] using heq))
  · exact Or.inr (Or.inr (Or.inl
      ⟨by simpa [low, half] using hgt,
       by simpa [low] using hlow_lt_ulp⟩))
/-- Positive minimum-boundary mixed normal/subnormal opposite-sign
precision-window branch. -/
theorem finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_error_finiteSystem_of_pred_exponent_eq_emin_add_t_sub_one
    {fmt : FloatingPointFormat}
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (ht : 1 < fmt.t)
    (hexp : eHigh - 1 = fmt.emin + (fmt.t : ℤ) - 1)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue true n)) := by
  have heminPred : fmt.emin ≤ eHigh - 1 := by
    rw [hexp]
    omega
  have hcell :
      fmt.subnormalValue false n <
          (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) ∨
        fmt.subnormalValue false n =
          (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) <
            fmt.subnormalValue false n ∧
          fmt.subnormalValue false n < fmt.ulpAtExponent (eHigh - 1)) ∨
        fmt.subnormalValue false n =
          fmt.ulpAtExponent (eHigh - 1) :=
    fmt.subnormalValue_false_pred_low_cell_cases_of_exponent_eq_emin_add_t_sub_one
      hn hexp
  exact
    fmt.finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_error_finiteSystem_of_pred_low_cell_cases
      hn heminPred hcell hxy
/-- Negative minimum-boundary mixed normal/subnormal opposite-sign
precision-window branch. -/
theorem finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_error_finiteSystem_of_pred_exponent_eq_emin_add_t_sub_one
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (ht : 1 < fmt.t)
    (hexp : eHigh - 1 = fmt.emin + (fmt.t : ℤ) - 1)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue false n)) := by
  have heminPred : fmt.emin ≤ eHigh - 1 := by
    rw [hexp]
    omega
  have hcell :
      fmt.subnormalValue false n <
          (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) ∨
        fmt.subnormalValue false n =
          (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1) <
            fmt.subnormalValue false n ∧
          fmt.subnormalValue false n < fmt.ulpAtExponent (eHigh - 1)) ∨
        fmt.subnormalValue false n =
          fmt.ulpAtExponent (eHigh - 1) :=
    fmt.subnormalValue_false_pred_low_cell_cases_of_exponent_eq_emin_add_t_sub_one
      hn hexp
  exact
    fmt.finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_error_finiteSystem_of_pred_low_cell_cases
      hbeta ht hn heminPred hcell hxy
/-- Positive normal plus negative subnormal has finite local error at the
predecessor half-ulp tie, provided the high normal has a same-exponent
predecessor. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_subnormal_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue true n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.subnormalValue true n) - y) := by
  let a := fmt.normalizedValue false (m - 1) e
  let b := fmt.normalizedValue false m e
  let low := fmt.subnormalValue false n
  have hmPred : fmt.normalizedMantissa (m - 1) :=
    fmt.normalizedMantissa_pred_of_ne_minNormalMantissa hm hneMin
  have hm_pos : 0 < m := fmt.normalizedMantissa_pos hm
  have hpred_succ : (m - 1) + 1 = m := by
    omega
  have hlow_eq : low = (1 / 2 : ℝ) * fmt.ulpAtExponent e := by
    simpa [low] using hlow
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.subnormalValue_false_pos hn
  have hulp_pos : 0 < fmt.ulpAtExponent e := fmt.ulpAtExponent_pos e
  have hb_sub_a : b - a = fmt.ulpAtExponent e := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_succ_sub_sameExponent false (m - 1) e)
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, m - 1, e, hmPred, ?_, Or.inl ?_⟩
    · simpa [hpred_succ] using hm
    · exact ⟨rfl, by dsimp [b]; rw [hpred_succ]⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hsource_eq :
      fmt.normalizedValue false m e + fmt.subnormalValue true n =
        b - low := by
    dsimp [b, low]
    simp [subnormalValue, signValue]
    ring
  have hpolicy' : fmt.sourceRoundToEvenEvidence (b - low) y := by
    simpa [hsource_eq] using hpolicy
  have hsource_between : a ≤ b - low ∧ b - low ≤ b := by
    constructor <;> linarith
  have hlow_fin : fmt.finiteSystem low :=
    Or.inr (Or.inr ⟨false, n, hn, rfl⟩)
  rcases
      fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
        hpolicy' hadj hsource_between with hy | hy
  · rw [hy, hsource_eq]
    convert hlow_fin using 1
    have hres : (b - low) - a = low := by
      linarith
    rw [hres]
  · rw [hy, hsource_eq]
    have hneg_low_fin := fmt.finiteSystem_neg hlow_fin
    convert hneg_low_fin using 1
    have hres : (b - low) - b = -low := by
      ring
    rw [hres]
/-- Operation-level positive normal plus negative subnormal has finite local
error at the predecessor half-ulp tie. -/
theorem finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false m e +
          fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue true n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue true n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_subnormal_error_finiteSystem_of_low_eq_half_ulp
      hm hneMin hn hlow hpolicy
/-- Negative normal plus positive subnormal has finite local error at the
predecessor half-ulp tie by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_subnormal_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e +
          fmt.subnormalValue false n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e +
          fmt.subnormalValue false n) - y) := by
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue true n) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    convert hneg using 1
    simp [normalizedValue, subnormalValue, signValue]
    ring
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false m e +
            fmt.subnormalValue true n) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_subnormal_error_finiteSystem_of_low_eq_half_ulp
      hm hneMin hn hlow hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [normalizedValue, subnormalValue, signValue]
  ring
/-- Operation-level negative normal plus positive subnormal has finite local
error at the predecessor half-ulp tie. -/
theorem finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true m e +
          fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue false n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e +
          fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue false n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_subnormal_error_finiteSystem_of_low_eq_half_ulp
      hbeta ht hm hneMin hn hlow hpolicy
/-- In the mixed normal/subnormal right half-cell branch, the residual
subnormal-lattice coefficient automatically has fewer than `t` radix digits.

If a positive subnormal value is already to the right of the half-ulp point at
normal exponent `e`, then the one-ulp coefficient `beta^(e-emin)` is less than
`2*n`.  Since the subnormal coefficient `n` is below the minimum normal
mantissa, both coefficients are below `beta^t`, so their integer gap also
fits. -/
theorem subnormal_right_half_coeff_gap_of_half_ulp_lt
    {fmt : FloatingPointFormat} {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hemin : fmt.emin ≤ e)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent e <
        fmt.subnormalValue false n) :
    (((n : ℤ) -
          ((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ)).natAbs <
        fmt.beta ^ fmt.t) := by
  let d := Int.toNat (e - fmt.emin)
  let s := fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))
  have hs_pos : 0 < s := by
    dsimp [s]
    exact fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ))
  have hd_cast : ((d : ℕ) : ℤ) = e - fmt.emin := by
    have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr hemin
    simpa [d] using Int.toNat_of_nonneg hnonneg
  have hulp_lattice :
      fmt.ulpAtExponent e = ((fmt.beta ^ d : ℕ) : ℝ) * s := by
    have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
    have hpow :
        fmt.betaR ^ ((d : ℕ) : ℤ) =
          ((fmt.beta ^ d : ℕ) : ℝ) := by
      rw [zpow_natCast]
      simp [betaR, Nat.cast_pow, d]
    calc
      fmt.ulpAtExponent e =
          fmt.betaR ^ (e - (fmt.t : ℤ)) := by
        rfl
      _ = fmt.betaR ^ (((d : ℕ) : ℤ) + (fmt.emin - (fmt.t : ℤ))) := by
        congr 1
        omega
      _ = fmt.betaR ^ ((d : ℕ) : ℤ) * s := by
        dsimp [s]
        rw [zpow_add₀ hbase]
      _ = ((fmt.beta ^ d : ℕ) : ℝ) * s := by
        rw [hpow]
  have hlow_lattice :
      fmt.subnormalValue false n = (n : ℝ) * s := by
    dsimp [s]
    simp [subnormalValue, signValue]
  have hhalf_scaled :
      (1 / 2 : ℝ) * ((fmt.beta ^ d : ℕ) : ℝ) < (n : ℝ) := by
    have hscaled :
        ((1 / 2 : ℝ) * ((fmt.beta ^ d : ℕ) : ℝ)) * s <
          (n : ℝ) * s := by
      simpa [hulp_lattice, hlow_lattice, mul_assoc, mul_comm, mul_left_comm]
        using hhalf
    nlinarith [hscaled, hs_pos]
  have hpow_lt_two_n_real :
      ((fmt.beta ^ d : ℕ) : ℝ) < (2 : ℝ) * n := by
    nlinarith
  have hpow_lt_two_n : fmt.beta ^ d < 2 * n := by
    have htmp :
        ((fmt.beta ^ d : ℕ) : ℝ) < ((2 * n : ℕ) : ℝ) := by
      simpa [Nat.cast_mul] using hpow_lt_two_n_real
    exact Nat.cast_lt.mp htmp
  have htwo_n_lt_bound : 2 * n < fmt.beta ^ fmt.t := by
    have h2n_lt : 2 * n < 2 * fmt.minNormalMantissa :=
      Nat.mul_lt_mul_of_pos_left hn.2 (by decide : 0 < 2)
    have h2min_le : 2 * fmt.minNormalMantissa ≤ fmt.beta ^ fmt.t := by
      calc
        2 * fmt.minNormalMantissa ≤ fmt.beta * fmt.minNormalMantissa :=
          Nat.mul_le_mul_right fmt.minNormalMantissa fmt.beta_ge_two
        _ = fmt.beta ^ fmt.t := by
          rw [Nat.mul_comm]
          exact fmt.minNormalMantissa_mul_beta_eq_mantissaBound
    exact lt_of_lt_of_le h2n_lt h2min_le
  have hpow_lt_bound : fmt.beta ^ d < fmt.beta ^ fmt.t :=
    lt_trans hpow_lt_two_n htwo_n_lt_bound
  have hn_lt_bound : n < fmt.beta ^ fmt.t :=
    lt_trans hn.2 fmt.minNormalMantissa_lt_mantissaBound
  have hgap_int :
      ((((n : ℤ) - ((fmt.beta ^ d : ℕ) : ℤ)).natAbs : ℤ) <
        ((fmt.beta ^ fmt.t : ℕ) : ℤ)) := by
    by_cases hnonneg : 0 ≤ (n : ℤ) - ((fmt.beta ^ d : ℕ) : ℤ)
    · have hnatabs :
          ((((n : ℤ) - ((fmt.beta ^ d : ℕ) : ℤ)).natAbs : ℤ) =
            (n : ℤ) - ((fmt.beta ^ d : ℕ) : ℤ)) :=
        Int.natAbs_of_nonneg hnonneg
      omega
    · have hnonneg' : 0 ≤ ((fmt.beta ^ d : ℕ) : ℤ) - (n : ℤ) := by
        omega
      have hnatabs :
          ((((n : ℤ) - ((fmt.beta ^ d : ℕ) : ℤ)).natAbs : ℤ) =
            ((fmt.beta ^ d : ℕ) : ℤ) - (n : ℤ)) := by
        rw [← Int.natAbs_neg]
        have h := Int.natAbs_of_nonneg hnonneg'
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
      omega
  exact_mod_cast hgap_int
/-- Positive normal plus negative subnormal has finite local error in the
strict predecessor right-half cell. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (hemin : fmt.emin ≤ e)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent e <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue true n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.subnormalValue true n) - y) := by
  let a := fmt.normalizedValue false (m - 1) e
  let b := fmt.normalizedValue false m e
  let low := fmt.subnormalValue false n
  have hmPred : fmt.normalizedMantissa (m - 1) :=
    fmt.normalizedMantissa_pred_of_ne_minNormalMantissa hm hneMin
  have hm_pos : 0 < m := fmt.normalizedMantissa_pos hm
  have hpred_succ : (m - 1) + 1 = m := by
    omega
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.subnormalValue_false_pos hn
  have hb_sub_a : b - a = fmt.ulpAtExponent e := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_succ_sub_sameExponent false (m - 1) e)
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, m - 1, e, hmPred, ?_, Or.inl ?_⟩
    · simpa [hpred_succ] using hm
    · exact ⟨rfl, by dsimp [b]; rw [hpred_succ]⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hsource_eq :
      fmt.normalizedValue false m e + fmt.subnormalValue true n =
        b - low := by
    dsimp [b, low]
    simp [subnormalValue, signValue]
    ring
  have hpolicy' : fmt.sourceRoundToEvenEvidence (b - low) y := by
    simpa [hsource_eq] using hpolicy
  have ha_lt_source : a < b - low := by
    linarith
  have hsource_lt_b : b - low < b := by
    linarith
  have hright_abs : |(b - low) - b| = low := by
    have hsub : (b - low) - b = -low := by ring
    rw [hsub, abs_neg, abs_of_pos hlow_pos]
  have hleft_abs :
      |(b - low) - a| = fmt.ulpAtExponent e - low := by
    have hsub : (b - low) - a = fmt.ulpAtExponent e - low := by
      linarith
    have hpos : 0 < fmt.ulpAtExponent e - low := by
      linarith
    rw [hsub, abs_of_pos hpos]
  have hleftCloser : |(b - low) - a| < |(b - low) - b| := by
    rw [hright_abs, hleft_abs]
    linarith
  have hy : y = a := by
    exact
      fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
        hpolicy' hadj ⟨ha_lt_source, hsource_lt_b⟩ hleftCloser
  have hd_cast :
      ((Int.toNat (e - fmt.emin) : ℕ) : ℤ) = e - fmt.emin := by
    have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr hemin
    simpa using Int.toNat_of_nonneg hnonneg
  have hgap0 :
      (((n : ℤ) -
          ((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ)).natAbs <
        fmt.beta ^ fmt.t) :=
    fmt.subnormal_right_half_coeff_gap_of_half_ulp_lt hn hemin hhalf
  have hgap :
      ((((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ) -
          (n : ℤ)).natAbs < fmt.beta ^ fmt.t) := by
    have h := hgap0
    rw [← Int.natAbs_neg] at h
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hulp_lattice :
      fmt.ulpAtExponent e =
        ((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
    have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
    have hpow :
        fmt.betaR ^ (((Int.toNat (e - fmt.emin) : ℕ) : ℤ)) =
          ((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℝ) := by
      rw [zpow_natCast]
      simp [betaR, Nat.cast_pow]
    calc
      fmt.ulpAtExponent e =
          fmt.betaR ^ (e - (fmt.t : ℤ)) := by
        rfl
      _ = fmt.betaR ^
            (((Int.toNat (e - fmt.emin) : ℕ) : ℤ) +
              (fmt.emin - (fmt.t : ℤ))) := by
        congr 1
        omega
      _ = fmt.betaR ^ (((Int.toNat (e - fmt.emin) : ℕ) : ℤ)) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
        rw [zpow_add₀ hbase]
      _ = ((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
        rw [hpow]
  have hfin_scaled :
      fmt.finiteSystem
        (fmt.signValue false *
            ((((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ) : ℝ)) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) -
          fmt.signValue false * ((n : ℤ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) :=
    fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := false)
      (k := ((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ))
      (l := (n : ℤ)) (e := fmt.emin)
      ⟨le_rfl, fmt.emin_le_emax⟩ hgap
  rw [hy, hsource_eq]
  change fmt.finiteSystem ((b - low) - a)
  convert hfin_scaled using 1
  have hres : (b - low) - a = fmt.ulpAtExponent e - low := by
    linarith
  rw [hres, hulp_lattice]
  dsimp [low]
  simp [subnormalValue, signValue]
/-- Operation-level positive normal plus negative subnormal has finite local
error in the strict predecessor right-half cell. -/
theorem finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (hemin : fmt.emin ≤ e)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent e <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false m e +
          fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue true n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue true n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hm hneMin hn hemin hhalf hulp hpolicy
/-- Negative normal plus positive subnormal has finite local error in the
strict predecessor right-half cell by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (hemin : fmt.emin ≤ e)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent e <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e +
          fmt.subnormalValue false n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e +
          fmt.subnormalValue false n) - y) := by
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue true n) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    convert hneg using 1
    simp [normalizedValue, subnormalValue, signValue]
    ring
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false m e +
            fmt.subnormalValue true n) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hm hneMin hn hemin hhalf hulp hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [normalizedValue, subnormalValue, signValue]
  ring
/-- Operation-level negative normal plus positive subnormal has finite local
error in the strict predecessor right-half cell. -/
theorem finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (hemin : fmt.emin ≤ e)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent e <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true m e +
          fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue false n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e +
          fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue false n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hbeta ht hm hneMin hn hemin hhalf hulp hpolicy
/-- Positive normal plus negative subnormal is exact when the subnormal
magnitude is exactly one ulp and the high normal has a same-exponent
predecessor. -/
theorem finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_eq_exact_of_low_eq_ulp
    {fmt : FloatingPointFormat}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (_hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hlow : fmt.subnormalValue false n = fmt.ulpAtExponent e) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue false m e)
        (fmt.subnormalValue true n) =
      fmt.normalizedValue false m e + fmt.subnormalValue true n := by
  let a := fmt.normalizedValue false (m - 1) e
  let b := fmt.normalizedValue false m e
  let low := fmt.subnormalValue false n
  have hmPred : fmt.normalizedMantissa (m - 1) :=
    fmt.normalizedMantissa_pred_of_ne_minNormalMantissa hm hneMin
  have hm_pos : 0 < m := fmt.normalizedMantissa_pos hm
  have hpred_succ : (m - 1) + 1 = m := by
    omega
  have hb_sub_a : b - a = fmt.ulpAtExponent e := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_succ_sub_sameExponent false (m - 1) e)
  have hsource_eq :
      fmt.normalizedValue false m e + fmt.subnormalValue true n = a := by
    dsimp [a, b]
    rw [show fmt.subnormalValue true n = -fmt.subnormalValue false n by
      simpa using fmt.subnormalValue_not_eq_neg false n]
    rw [hlow]
    linarith
  have hfin_source :
      fmt.finiteSystem
        (fmt.normalizedValue false m e + fmt.subnormalValue true n) := by
    rw [hsource_eq]
    exact Or.inr (Or.inl ⟨false, m - 1, e, hmPred, he, rfl⟩)
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue false m e)
      (y := fmt.subnormalValue true n) hfin_source)
/-- The positive exact-predecessor mixed branch has zero local roundoff error. -/
theorem finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_low_eq_ulp
    {fmt : FloatingPointFormat}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hlow : fmt.subnormalValue false n = fmt.ulpAtExponent e) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue true n)) := by
  rw [
    finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_eq_exact_of_low_eq_ulp
      hm hneMin hn he hlow]
  simpa using fmt.finiteSystem_zero
/-- Negative normal plus positive subnormal is exact when the subnormal
magnitude is exactly one ulp and the high normal has a same-exponent
predecessor. -/
theorem finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_eq_exact_of_low_eq_ulp
    {fmt : FloatingPointFormat}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (_hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hlow : fmt.subnormalValue false n = fmt.ulpAtExponent e) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue true m e)
        (fmt.subnormalValue false n) =
      fmt.normalizedValue true m e + fmt.subnormalValue false n := by
  let a := fmt.normalizedValue false (m - 1) e
  let b := fmt.normalizedValue false m e
  have hmPred : fmt.normalizedMantissa (m - 1) :=
    fmt.normalizedMantissa_pred_of_ne_minNormalMantissa hm hneMin
  have hm_pos : 0 < m := fmt.normalizedMantissa_pos hm
  have hpred_succ : (m - 1) + 1 = m := by
    omega
  have hb_sub_a : b - a = fmt.ulpAtExponent e := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_succ_sub_sameExponent false (m - 1) e)
  have hsource_eq :
      fmt.normalizedValue true m e + fmt.subnormalValue false n =
        fmt.normalizedValue true (m - 1) e := by
    dsimp [a, b]
    rw [fmt.normalizedValue_true_eq_neg_false, hlow]
    rw [show fmt.normalizedValue true (m - 1) e = -a by
      rw [fmt.normalizedValue_true_eq_neg_false]]
    linarith
  have hfin_source :
      fmt.finiteSystem
        (fmt.normalizedValue true m e + fmt.subnormalValue false n) := by
    rw [hsource_eq]
    exact Or.inr (Or.inl ⟨true, m - 1, e, hmPred, he, rfl⟩)
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue true m e)
      (y := fmt.subnormalValue false n) hfin_source)
/-- The negative exact-predecessor mixed branch has zero local roundoff error. -/
theorem finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_low_eq_ulp
    {fmt : FloatingPointFormat}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hlow : fmt.subnormalValue false n = fmt.ulpAtExponent e) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue false n)) := by
  rw [
    finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_eq_exact_of_low_eq_ulp
      hm hneMin hn he hlow]
  simpa using fmt.finiteSystem_zero
/-- Dispatcher for the ordinary positive mixed normal/subnormal opposite-sign
predecessor low-cell split. -/
theorem finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_low_cell_cases
    {fmt : FloatingPointFormat}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hemin : fmt.emin ≤ e)
    (hcell :
      fmt.subnormalValue false n <
          (1 / 2 : ℝ) * fmt.ulpAtExponent e ∨
        fmt.subnormalValue false n =
          (1 / 2 : ℝ) * fmt.ulpAtExponent e ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent e <
            fmt.subnormalValue false n ∧
          fmt.subnormalValue false n < fmt.ulpAtExponent e) ∨
        fmt.subnormalValue false n = fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false m e +
          fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue true n)) := by
  rcases hcell with hlt | hrest
  · exact
      fmt.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_low_lt_half_ulp
        hm hneMin hn hlt hxy
  · rcases hrest with heq | hrest
    · exact
        fmt.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_low_eq_half_ulp
          hm hneMin hn heq hxy
    · rcases hrest with hright | hulp
      · exact
          fmt.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
            hm hneMin hn hemin hright.1 hright.2 hxy
      · exact
          fmt.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_low_eq_ulp
            hm hneMin hn he hulp
/-- Dispatcher for the ordinary negative mixed normal/subnormal opposite-sign
predecessor low-cell split. -/
theorem finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_low_cell_cases
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hemin : fmt.emin ≤ e)
    (hcell :
      fmt.subnormalValue false n <
          (1 / 2 : ℝ) * fmt.ulpAtExponent e ∨
        fmt.subnormalValue false n =
          (1 / 2 : ℝ) * fmt.ulpAtExponent e ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent e <
            fmt.subnormalValue false n ∧
          fmt.subnormalValue false n < fmt.ulpAtExponent e) ∨
        fmt.subnormalValue false n = fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true m e +
          fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue false n)) := by
  rcases hcell with hlt | hrest
  · exact
      fmt.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_low_lt_half_ulp
        hbeta ht hm hneMin hn hlt hxy
  · rcases hrest with heq | hrest
    · exact
        fmt.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_low_eq_half_ulp
          hbeta ht hm hneMin hn heq hxy
    · rcases hrest with hright | hulp
      · exact
          fmt.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
            hbeta ht hm hneMin hn hemin hright.1 hright.2 hxy
      · exact
        fmt.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_low_eq_ulp
            hm hneMin hn he hulp
/-- At the mixed predecessor precision-window exponent `emin + t - 1`, a
positive subnormal lies in the low cell adjacent to one high-exponent ulp. -/
theorem subnormalValue_false_low_cell_cases_of_exponent_eq_emin_add_t_sub_one
    {fmt : FloatingPointFormat}
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hexp : e = fmt.emin + (fmt.t : ℤ) - 1) :
    fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e ∨
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent e ∨
      ((1 / 2 : ℝ) * fmt.ulpAtExponent e <
          fmt.subnormalValue false n ∧
        fmt.subnormalValue false n < fmt.ulpAtExponent e) ∨
      fmt.subnormalValue false n = fmt.ulpAtExponent e := by
  let low := fmt.subnormalValue false n
  let half := (1 / 2 : ℝ) * fmt.ulpAtExponent e
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.subnormalValue_false_pos hn
  have hlow_lt_min :
      low < fmt.betaR ^ (fmt.emin - 1) := by
    have h := fmt.subnormalValue_abs_lt_min_normal
      (negative := false) hn
    simpa [low, abs_of_pos hlow_pos] using h
  have hulp_eq :
      fmt.ulpAtExponent e = fmt.betaR ^ (fmt.emin - 1) := by
    rw [ulpAtExponent, hexp]
    congr 1
    ring
  have hlow_lt_ulp : low < fmt.ulpAtExponent e := by
    simpa [hulp_eq] using hlow_lt_min
  rcases lt_trichotomy low half with hlt | heq | hgt
  · exact Or.inl (by simpa [low, half] using hlt)
  · exact Or.inr (Or.inl (by simpa [low, half] using heq))
  · exact Or.inr (Or.inr (Or.inl
      ⟨by simpa [low, half] using hgt,
       by simpa [low] using hlow_lt_ulp⟩))
/-- Ordinary positive mixed normal/subnormal opposite-sign precision-window
branch at exponent `emin + t - 1`. -/
theorem finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_exponent_eq_emin_add_t_sub_one
    {fmt : FloatingPointFormat}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (ht : 1 < fmt.t)
    (hexp : e = fmt.emin + (fmt.t : ℤ) - 1)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false m e +
          fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue true n)) := by
  have hemin : fmt.emin ≤ e := by
    rw [hexp]
    omega
  have hcell :
      fmt.subnormalValue false n <
          (1 / 2 : ℝ) * fmt.ulpAtExponent e ∨
        fmt.subnormalValue false n =
          (1 / 2 : ℝ) * fmt.ulpAtExponent e ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent e <
            fmt.subnormalValue false n ∧
          fmt.subnormalValue false n < fmt.ulpAtExponent e) ∨
        fmt.subnormalValue false n = fmt.ulpAtExponent e :=
    fmt.subnormalValue_false_low_cell_cases_of_exponent_eq_emin_add_t_sub_one
      hn hexp
  exact
    fmt.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_low_cell_cases
      hm hneMin hn he hemin hcell hxy
/-- Ordinary negative mixed normal/subnormal opposite-sign precision-window
branch at exponent `emin + t - 1`. -/
theorem finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_exponent_eq_emin_add_t_sub_one
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (ht : 1 < fmt.t)
    (hexp : e = fmt.emin + (fmt.t : ℤ) - 1)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true m e +
          fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue false n)) := by
  have hemin : fmt.emin ≤ e := by
    rw [hexp]
    omega
  have hcell :
      fmt.subnormalValue false n <
          (1 / 2 : ℝ) * fmt.ulpAtExponent e ∨
        fmt.subnormalValue false n =
          (1 / 2 : ℝ) * fmt.ulpAtExponent e ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent e <
            fmt.subnormalValue false n ∧
          fmt.subnormalValue false n < fmt.ulpAtExponent e) ∨
        fmt.subnormalValue false n = fmt.ulpAtExponent e :=
    fmt.subnormalValue_false_low_cell_cases_of_exponent_eq_emin_add_t_sub_one
      hn hexp
  exact
    fmt.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_low_cell_cases
      hbeta ht hm hneMin hn he hemin hcell hxy
/-- Commuted positive normal plus negative subnormal strict-left mixed branch. -/
theorem finiteRoundToEvenOp_add_negative_subnormal_pos_normalized_error_finiteSystem_of_exponent_gap_ge_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (hgap : fmt.emin + (fmt.t : ℤ) ≤ e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue true n +
          fmt.normalizedValue false m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue true n +
          fmt.normalizedValue false m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue false m e)) := by
  have hxy' :
      fmt.finiteNormalRange
        (fmt.normalizedValue false m e +
          fmt.subnormalValue true n) := by
    simpa [add_comm] using hxy
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue false m e +
            fmt.subnormalValue true n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.normalizedValue false m e)
            (fmt.subnormalValue true n)) :=
    fmt.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_exponent_gap_ge_t
      hbeta hm hneMin hn hgap hxy'
  have hop :
      fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue false m e) =
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue true n) := by
    simp [finiteRoundToEvenOp, BasicOp.exact, add_comm]
  rw [hop]
  convert hfin using 1
  ring
/-- Commuted negative normal plus positive subnormal strict-left mixed branch. -/
theorem finiteRoundToEvenOp_add_positive_subnormal_neg_normalized_error_finiteSystem_of_exponent_gap_ge_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (hgap : fmt.emin + (fmt.t : ℤ) ≤ e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue false n +
          fmt.normalizedValue true m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue false n +
          fmt.normalizedValue true m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue true m e)) := by
  have hxy' :
      fmt.finiteNormalRange
        (fmt.normalizedValue true m e +
          fmt.subnormalValue false n) := by
    simpa [add_comm] using hxy
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue true m e +
            fmt.subnormalValue false n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.normalizedValue true m e)
            (fmt.subnormalValue false n)) :=
    fmt.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_exponent_gap_ge_t
      hbeta ht hm hneMin hn hgap hxy'
  have hop :
      fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue true m e) =
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue false n) := by
    simp [finiteRoundToEvenOp, BasicOp.exact, add_comm]
  rw [hop]
  convert hfin using 1
  ring
/-- Commuted ordinary positive normal plus negative subnormal precision-window
mixed branch. -/
theorem finiteRoundToEvenOp_add_negative_subnormal_pos_normalized_error_finiteSystem_of_exponent_eq_emin_add_t_sub_one
    {fmt : FloatingPointFormat}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (ht : 1 < fmt.t)
    (hexp : e = fmt.emin + (fmt.t : ℤ) - 1)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue true n +
          fmt.normalizedValue false m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue true n +
          fmt.normalizedValue false m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue false m e)) := by
  have hxy' :
      fmt.finiteNormalRange
        (fmt.normalizedValue false m e +
          fmt.subnormalValue true n) := by
    simpa [add_comm] using hxy
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue false m e +
            fmt.subnormalValue true n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.normalizedValue false m e)
            (fmt.subnormalValue true n)) :=
    fmt.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_exponent_eq_emin_add_t_sub_one
      hm hneMin hn he ht hexp hxy'
  have hop :
      fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue false m e) =
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue true n) := by
    simp [finiteRoundToEvenOp, BasicOp.exact, add_comm]
  rw [hop]
  convert hfin using 1
  ring
/-- Commuted ordinary negative normal plus positive subnormal precision-window
mixed branch. -/
theorem finiteRoundToEvenOp_add_positive_subnormal_neg_normalized_error_finiteSystem_of_exponent_eq_emin_add_t_sub_one
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hneMin : m ≠ fmt.minNormalMantissa)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (ht : 1 < fmt.t)
    (hexp : e = fmt.emin + (fmt.t : ℤ) - 1)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue false n +
          fmt.normalizedValue true m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue false n +
          fmt.normalizedValue true m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue true m e)) := by
  have hxy' :
      fmt.finiteNormalRange
        (fmt.normalizedValue true m e +
          fmt.subnormalValue false n) := by
    simpa [add_comm] using hxy
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue true m e +
            fmt.subnormalValue false n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.normalizedValue true m e)
            (fmt.subnormalValue false n)) :=
    fmt.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_exponent_eq_emin_add_t_sub_one
      hbeta hm hneMin hn he ht hexp hxy'
  have hop :
      fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue true m e) =
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue false n) := by
    simp [finiteRoundToEvenOp, BasicOp.exact, add_comm]
  rw [hop]
  convert hfin using 1
  ring
/-- Commuted positive minimum normal plus negative subnormal strict-left mixed
boundary branch. -/
theorem finiteRoundToEvenOp_add_negative_subnormal_pos_min_normalized_error_finiteSystem_of_exponent_gap_ge_t_pred
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hgap : fmt.emin + (fmt.t : ℤ) ≤ eHigh - 1)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue true n +
          fmt.normalizedValue false fmt.minNormalMantissa eHigh)) :
    fmt.finiteSystem
      ((fmt.subnormalValue true n +
          fmt.normalizedValue false fmt.minNormalMantissa eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)) := by
  have hxy' :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n) := by
    simpa [add_comm] using hxy
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
            fmt.subnormalValue true n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
            (fmt.subnormalValue true n)) :=
    fmt.finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_error_finiteSystem_of_exponent_gap_ge_t_pred
      hbeta hn hgap hxy'
  have hop :
      fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh) =
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue true n) := by
    simp [finiteRoundToEvenOp, BasicOp.exact, add_comm]
  rw [hop]
  convert hfin using 1
  ring
/-- Commuted negative minimum normal plus positive subnormal strict-left mixed
boundary branch. -/
theorem finiteRoundToEvenOp_add_positive_subnormal_neg_min_normalized_error_finiteSystem_of_exponent_gap_ge_t_pred
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hgap : fmt.emin + (fmt.t : ℤ) ≤ eHigh - 1)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue false n +
          fmt.normalizedValue true fmt.minNormalMantissa eHigh)) :
    fmt.finiteSystem
      ((fmt.subnormalValue false n +
          fmt.normalizedValue true fmt.minNormalMantissa eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)) := by
  have hxy' :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n) := by
    simpa [add_comm] using hxy
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
            fmt.subnormalValue false n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
            (fmt.subnormalValue false n)) :=
    fmt.finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_error_finiteSystem_of_exponent_gap_ge_t_pred
      hbeta ht hn hgap hxy'
  have hop :
      fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh) =
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue false n) := by
    simp [finiteRoundToEvenOp, BasicOp.exact, add_comm]
  rw [hop]
  convert hfin using 1
  ring
/-- Commuted positive minimum normal plus negative subnormal precision-window
mixed boundary branch. -/
theorem finiteRoundToEvenOp_add_negative_subnormal_pos_min_normalized_error_finiteSystem_of_pred_exponent_eq_emin_add_t_sub_one
    {fmt : FloatingPointFormat}
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (ht : 1 < fmt.t)
    (hexp : eHigh - 1 = fmt.emin + (fmt.t : ℤ) - 1)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue true n +
          fmt.normalizedValue false fmt.minNormalMantissa eHigh)) :
    fmt.finiteSystem
      ((fmt.subnormalValue true n +
          fmt.normalizedValue false fmt.minNormalMantissa eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)) := by
  have hxy' :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.subnormalValue true n) := by
    simpa [add_comm] using hxy
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
            fmt.subnormalValue true n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
            (fmt.subnormalValue true n)) :=
    fmt.finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_error_finiteSystem_of_pred_exponent_eq_emin_add_t_sub_one
      hn ht hexp hxy'
  have hop :
      fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh) =
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue true n) := by
    simp [finiteRoundToEvenOp, BasicOp.exact, add_comm]
  rw [hop]
  convert hfin using 1
  ring
/-- Commuted negative minimum normal plus positive subnormal precision-window
mixed boundary branch. -/
theorem finiteRoundToEvenOp_add_positive_subnormal_neg_min_normalized_error_finiteSystem_of_pred_exponent_eq_emin_add_t_sub_one
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {n : ℕ} {eHigh : ℤ}
    (hn : fmt.subnormalMantissa n)
    (ht : 1 < fmt.t)
    (hexp : eHigh - 1 = fmt.emin + (fmt.t : ℤ) - 1)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue false n +
          fmt.normalizedValue true fmt.minNormalMantissa eHigh)) :
    fmt.finiteSystem
      ((fmt.subnormalValue false n +
          fmt.normalizedValue true fmt.minNormalMantissa eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)) := by
  have hxy' :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.subnormalValue false n) := by
    simpa [add_comm] using hxy
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
            fmt.subnormalValue false n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
            (fmt.subnormalValue false n)) :=
    fmt.finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_error_finiteSystem_of_pred_exponent_eq_emin_add_t_sub_one
      hbeta hn ht hexp hxy'
  have hop :
      fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh) =
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.minNormalMantissa eHigh)
          (fmt.subnormalValue false n) := by
    simp [finiteRoundToEvenOp, BasicOp.exact, add_comm]
  rw [hop]
  convert hfin using 1
  ring
/-- Operation-level positive mixed normal/subnormal opposite-sign addition has
finite local error throughout the base-2 finite-normal branch. -/
theorem finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false m e + fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e + fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue true n)) := by
  have hcoeff_le :
      n ≤ m * fmt.beta ^ Int.toNat (e - fmt.emin) :=
    fmt.subnormalMantissa_le_aligned_normalizedCoeff hm hn
  by_cases hsmall :
      (((m * fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ) -
          (n : ℤ)).natAbs < fmt.beta ^ fmt.t
  · exact
      fmt.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
        hm hn he hsmall
  · have hlo_guard :
        fmt.beta ^ fmt.t ≤
          m * fmt.beta ^ Int.toNat (e - fmt.emin) - n :=
      nat_sub_le_of_not_natAbs_int_sub_lt hcoeff_le hsmall
    by_cases hguard :
        m * fmt.beta ^ Int.toNat (e - fmt.emin) - n <
          2 * fmt.beta ^ fmt.t
    · exact
        fmt.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_guardCoeffBounds
          hbeta hm hn he hcoeff_le hlo_guard hguard hxy
    · have hlo_multi :
          2 * fmt.beta ^ fmt.t ≤
            m * fmt.beta ^ Int.toNat (e - fmt.emin) - n :=
        le_of_not_gt hguard
      by_cases hwindow : fmt.emin + (fmt.t : ℤ) > e
      · exact
          fmt.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_multiGuardComplementaryRegion
            hbeta hm hn he hcoeff_le hlo_multi hwindow hxy
      · have hgap : fmt.emin + (fmt.t : ℤ) ≤ e := le_of_not_gt hwindow
        by_cases hmMin : m = fmt.minNormalMantissa
        · subst m
          by_cases hgapPred : fmt.emin + (fmt.t : ℤ) ≤ e - 1
          · exact
              fmt.finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_error_finiteSystem_of_exponent_gap_ge_t_pred
                hbeta hn hgapPred hxy
          · have hexp : e - 1 = fmt.emin + (fmt.t : ℤ) - 1 := by
              omega
            exact
              fmt.finiteRoundToEvenOp_add_positive_min_normalized_neg_subnormal_error_finiteSystem_of_pred_exponent_eq_emin_add_t_sub_one
                hn ht hexp hxy
        · exact
            fmt.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_exponent_gap_ge_t
              hbeta hm hmMin hn hgap hxy
/-- Operation-level negative mixed normal/subnormal opposite-sign addition has
finite local error throughout the base-2 finite-normal branch. -/
theorem finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true m e + fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e + fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue false n)) := by
  have hcoeff_le :
      n ≤ m * fmt.beta ^ Int.toNat (e - fmt.emin) :=
    fmt.subnormalMantissa_le_aligned_normalizedCoeff hm hn
  by_cases hsmall :
      (((m * fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ) -
          (n : ℤ)).natAbs < fmt.beta ^ fmt.t
  · exact
      fmt.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_alignedDiffCoeff_lt_mantissaBound
        hm hn he hsmall
  · have hlo_guard :
        fmt.beta ^ fmt.t ≤
          m * fmt.beta ^ Int.toNat (e - fmt.emin) - n :=
      nat_sub_le_of_not_natAbs_int_sub_lt hcoeff_le hsmall
    by_cases hguard :
        m * fmt.beta ^ Int.toNat (e - fmt.emin) - n <
          2 * fmt.beta ^ fmt.t
    · exact
        fmt.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_guardCoeffBounds
          hbeta hm hn he hcoeff_le hlo_guard hguard hxy
    · have hlo_multi :
          2 * fmt.beta ^ fmt.t ≤
            m * fmt.beta ^ Int.toNat (e - fmt.emin) - n :=
        le_of_not_gt hguard
      by_cases hwindow : fmt.emin + (fmt.t : ℤ) > e
      · exact
          fmt.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_multiGuardComplementaryRegion
            hbeta hm hn he hcoeff_le hlo_multi hwindow hxy
      · have hgap : fmt.emin + (fmt.t : ℤ) ≤ e := le_of_not_gt hwindow
        by_cases hmMin : m = fmt.minNormalMantissa
        · subst m
          by_cases hgapPred : fmt.emin + (fmt.t : ℤ) ≤ e - 1
          · exact
              fmt.finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_error_finiteSystem_of_exponent_gap_ge_t_pred
                hbeta ht hn hgapPred hxy
          · have hexp : e - 1 = fmt.emin + (fmt.t : ℤ) - 1 := by
              omega
            exact
              fmt.finiteRoundToEvenOp_add_negative_min_normalized_pos_subnormal_error_finiteSystem_of_pred_exponent_eq_emin_add_t_sub_one
                hbeta hn ht hexp hxy
        · exact
            fmt.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_exponent_gap_ge_t
              hbeta ht hm hmMin hn hgap hxy
/-- Commuted operation-level negative subnormal plus positive normal has finite
local error throughout the base-2 finite-normal branch. -/
theorem finiteRoundToEvenOp_add_negative_subnormal_pos_normalized_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue true n + fmt.normalizedValue false m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue true n + fmt.normalizedValue false m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue false m e)) := by
  have hxy' :
      fmt.finiteNormalRange
        (fmt.normalizedValue false m e + fmt.subnormalValue true n) := by
    simpa [add_comm] using hxy
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue false m e + fmt.subnormalValue true n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.normalizedValue false m e)
            (fmt.subnormalValue true n)) :=
    fmt.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_baseTwo
      hbeta ht hm hn he hxy'
  have hop :
      fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue false m e) =
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue true n) := by
    simp [finiteRoundToEvenOp, BasicOp.exact, add_comm]
  rw [hop]
  convert hfin using 1
  ring
/-- Commuted operation-level positive subnormal plus negative normal has finite
local error throughout the base-2 finite-normal branch. -/
theorem finiteRoundToEvenOp_add_positive_subnormal_neg_normalized_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue false n + fmt.normalizedValue true m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue false n + fmt.normalizedValue true m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue true m e)) := by
  have hxy' :
      fmt.finiteNormalRange
        (fmt.normalizedValue true m e + fmt.subnormalValue false n) := by
    simpa [add_comm] using hxy
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue true m e + fmt.subnormalValue false n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.normalizedValue true m e)
            (fmt.subnormalValue false n)) :=
    fmt.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_baseTwo
      hbeta ht hm hn he hxy'
  have hop :
      fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue true m e) =
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue false n) := by
    simp [finiteRoundToEvenOp, BasicOp.exact, add_comm]
  rw [hop]
  convert hfin using 1
  ring
/-- Operation-level same-sign mixed normal/subnormal addition has finite local
error when the normal exponent is at least one precision window above `emin`.

The subnormal operand is then automatically in the strict left half-cell of the
normal operand, and the proof dispatches to the non-boundary or max-mantissa
strict-left branch as appropriate. -/
theorem finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_exponent_gap_ge_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (_he : fmt.exponentInRange e)
    (hgap : fmt.emin + (fmt.t : ℤ) ≤ e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.subnormalValue negative n)) := by
  have hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e :=
    fmt.subnormalValue_false_lt_half_ulpAtExponent_of_exponent_gap_ge_t
      hbeta hn hgap
  by_cases hmmax : m = fmt.maxNormalMantissa
  · subst m
    cases negative
    · exact
        fmt.finiteRoundToEvenOp_add_positive_max_normalized_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
          hn hlow hxy
    · exact
        fmt.finiteRoundToEvenOp_add_negative_max_normalized_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
          hbeta ht hn hlow hxy
  · have hmSucc : fmt.normalizedMantissa (m + 1) :=
      fmt.normalizedMantissa_succ_of_ne_maxNormalMantissa hm hmmax
    cases negative
    · exact
        fmt.finiteRoundToEvenOp_add_positive_normalized_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
          hm hmSucc hn hlow hxy
    · exact
        fmt.finiteRoundToEvenOp_add_negative_normalized_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
          hbeta ht hm hmSucc hn hlow hxy
/-- Commuted operation-level same-sign mixed subnormal/normal addition has
finite local error when the normal exponent is at least one precision window
above `emin`. -/
theorem finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_exponent_gap_ge_t
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (_he : fmt.exponentInRange e)
    (hgap : fmt.emin + (fmt.t : ℤ) ≤ e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative m e)) := by
  have hlow :
      fmt.subnormalValue false n <
        (1 / 2 : ℝ) * fmt.ulpAtExponent e :=
    fmt.subnormalValue_false_lt_half_ulpAtExponent_of_exponent_gap_ge_t
      hbeta hn hgap
  by_cases hmmax : m = fmt.maxNormalMantissa
  · subst m
    cases negative
    · exact
        fmt.finiteRoundToEvenOp_add_positive_subnormal_sameSign_max_normalized_error_finiteSystem_of_low_lt_half_ulp
          hn hlow hxy
    · exact
        fmt.finiteRoundToEvenOp_add_negative_subnormal_sameSign_max_normalized_error_finiteSystem_of_low_lt_half_ulp
          hbeta ht hn hlow hxy
  · have hmSucc : fmt.normalizedMantissa (m + 1) :=
      fmt.normalizedMantissa_succ_of_ne_maxNormalMantissa hm hmmax
    cases negative
    · exact
        fmt.finiteRoundToEvenOp_add_positive_subnormal_sameSign_normalized_error_finiteSystem_of_low_lt_half_ulp
          hm hmSucc hn hlow hxy
    · exact
        fmt.finiteRoundToEvenOp_add_negative_subnormal_sameSign_normalized_error_finiteSystem_of_low_lt_half_ulp
          hbeta ht hm hmSucc hn hlow hxy
/-- Operation-level same-sign mixed normal/subnormal addition has finite local
error in the base-2 complementary multi-guard region. -/
theorem finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_multiGuardComplementaryRegion
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) + n)
    (hwindow : fmt.emin + (fmt.t : ℤ) > e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.subnormalValue negative n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.subnormalValue negative n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_multiGuardComplementaryRegion
      hbeta hm hn he hlo hwindow hpolicy
/-- Commuted operation-level same-sign mixed subnormal/normal addition has
finite local error in the base-2 complementary multi-guard region. -/
theorem finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_multiGuardComplementaryRegion
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2)
    {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) + n)
    (hwindow : fmt.emin + (fmt.t : ℤ) > e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative m e)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative m e)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative m e)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue negative m e +
            fmt.subnormalValue negative n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.subnormalValue negative n)
            (fmt.normalizedValue negative m e)) :=
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_multiGuardComplementaryRegion
      hbeta hm hn he hlo hwindow hpolicy
  convert hfin using 1
  ring
/-- Operation-level same-sign mixed normal/subnormal addition has finite local
error throughout the base-2 finite-normal branch.

This dispatches the mixed coefficient into the exact-or-one-guard range, the
complementary multi-guard precision window, or the large-alignment strict-left
branch. -/
theorem finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.subnormalValue negative n)) := by
  by_cases hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        2 * fmt.beta ^ fmt.t
  · exact
      fmt.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound
        hbeta hm hn he hhi hxy
  · have hlo :
        2 * fmt.beta ^ fmt.t ≤
          m * fmt.beta ^ Int.toNat (e - fmt.emin) + n :=
      le_of_not_gt hhi
    by_cases hwindow : fmt.emin + (fmt.t : ℤ) > e
    · exact
        fmt.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_multiGuardComplementaryRegion
          hbeta hm hn he hlo hwindow hxy
    · have hgap : fmt.emin + (fmt.t : ℤ) ≤ e := le_of_not_gt hwindow
      exact
        fmt.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_exponent_gap_ge_t
          hbeta ht hm hn he hgap hxy
/-- Commuted operation-level same-sign mixed subnormal/normal addition has
finite local error throughout the base-2 finite-normal branch. -/
theorem finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative m e)) := by
  by_cases hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        2 * fmt.beta ^ fmt.t
  · exact
      fmt.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound
        hbeta hm hn he hhi hxy
  · have hlo :
        2 * fmt.beta ^ fmt.t ≤
          m * fmt.beta ^ Int.toNat (e - fmt.emin) + n :=
      le_of_not_gt hhi
    by_cases hwindow : fmt.emin + (fmt.t : ℤ) > e
    · exact
        fmt.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_multiGuardComplementaryRegion
          hbeta hm hn he hlo hwindow hxy
    · have hgap : fmt.emin + (fmt.t : ℤ) ≤ e := le_of_not_gt hwindow
      exact
        fmt.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_exponent_gap_ge_t
          hbeta ht hm hn he hgap hxy
/-- Positive same-sign mixed normal/subnormal addition has finite local error
at the exact half-ulp tie around the normal operand.

Round-to-even may choose either adjacent endpoint at the tie; the residual is
the subnormal addend or its negation, hence finite representable in either
case. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue false n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.subnormalValue false n) - y) := by
  let a := fmt.normalizedValue false m e
  let b := fmt.normalizedValue false (m + 1) e
  let low := fmt.subnormalValue false n
  have hlow_eq : low = (1 / 2 : ℝ) * fmt.ulpAtExponent e := by
    simpa [low] using hlow
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.subnormalValue_false_pos hn
  have hulp_pos : 0 < fmt.ulpAtExponent e := fmt.ulpAtExponent_pos e
  have hlow_lt_ulp : low < fmt.ulpAtExponent e := by
    rw [hlow_eq]
    linarith
  have hb_sub_a : b - a = fmt.ulpAtExponent e := by
    dsimp [a, b]
    simpa [ulpAtExponent, signValue] using
      (fmt.normalizedValue_succ_sub_sameExponent false m e)
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, m, e, hm, hmSucc, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hsource_between : a ≤ a + low ∧ a + low ≤ b := by
    constructor <;> linarith
  have hlow_fin : fmt.finiteSystem low :=
    Or.inr (Or.inr ⟨false, n, hn, rfl⟩)
  rcases
      fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
        hpolicy hadj hsource_between with hy | hy
  · rw [hy]
    convert hlow_fin using 1
    dsimp [a, low]
    ring
  · rw [hy]
    have hfin_neg := fmt.finiteSystem_neg hlow_fin
    convert hfin_neg using 1
    have hres : (a + low) - b = -low := by
      linarith
    rw [hres]
/-- Operation-level positive same-sign mixed normal/subnormal addition has
finite representable local roundoff error at the exact half-ulp tie. -/
theorem finiteRoundToEvenOp_add_positive_normalized_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false m e +
          fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue false n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue false n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
      hm hmSucc hn hlow hpolicy
/-- Commuted operation-level positive same-sign mixed subnormal/normal addition
has finite representable local roundoff error at the exact half-ulp tie. -/
theorem finiteRoundToEvenOp_add_positive_subnormal_sameSign_normalized_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue false n +
          fmt.normalizedValue false m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue false n +
          fmt.normalizedValue false m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue false m e)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.subnormalValue false n +
          fmt.normalizedValue false m e)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue false m e)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue false m e)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue false m e +
            fmt.subnormalValue false n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.subnormalValue false n)
            (fmt.normalizedValue false m e)) :=
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
      hm hmSucc hn hlow hpolicy
  convert hfin using 1
  ring
/-- Negative same-sign mixed normal/subnormal addition has finite local error
at the exact half-ulp tie by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e +
          fmt.subnormalValue true n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e +
          fmt.subnormalValue true n) - y) := by
  have hsource_neg :
      -(fmt.normalizedValue true m e + fmt.subnormalValue true n) =
        fmt.normalizedValue false m e + fmt.subnormalValue false n := by
    simp [normalizedValue, subnormalValue, signValue]
    ring
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue false n) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    simpa [hsource_neg] using hneg
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false m e +
            fmt.subnormalValue false n) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
      hm hmSucc hn hlow hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [normalizedValue, subnormalValue, signValue]
  ring
/-- Operation-level negative same-sign mixed normal/subnormal addition has
finite representable local roundoff error at the exact half-ulp tie. -/
theorem finiteRoundToEvenOp_add_negative_normalized_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true m e +
          fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue true n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e +
          fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue true n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
      hbeta ht hm hmSucc hn hlow hpolicy
/-- Commuted operation-level negative same-sign mixed subnormal/normal addition
has finite representable local roundoff error at the exact half-ulp tie. -/
theorem finiteRoundToEvenOp_add_negative_subnormal_sameSign_normalized_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue true n +
          fmt.normalizedValue true m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue true n +
          fmt.normalizedValue true m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue true m e)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.subnormalValue true n +
          fmt.normalizedValue true m e)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue true m e)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e +
          fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue true m e)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue true m e +
            fmt.subnormalValue true n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.subnormalValue true n)
            (fmt.normalizedValue true m e)) :=
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
      hbeta ht hm hmSucc hn hlow hpolicy
  convert hfin using 1
  ring
/-- Positive same-sign mixed max-normal/subnormal addition has finite local
error at the exact half-ulp tie around the exponent-boundary endpoint. -/
theorem sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n) - y) := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa e
  let b := fmt.normalizedValue false fmt.minNormalMantissa (e + 1)
  let low := fmt.subnormalValue false n
  have hlow_eq : low = (1 / 2 : ℝ) * fmt.ulpAtExponent e := by
    simpa [low] using hlow
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.subnormalValue_false_pos hn
  have hulp_pos : 0 < fmt.ulpAtExponent e := fmt.ulpAtExponent_pos e
  have hlow_lt_ulp : low < fmt.ulpAtExponent e := by
    rw [hlow_eq]
    linarith
  have hb_sub_a : b - a = fmt.ulpAtExponent e := by
    dsimp [a, b]
    simpa [ulpAtExponent, signValue] using
      (fmt.normalizedValue_boundary_sub false e)
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, e, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hsource_between : a ≤ a + low ∧ a + low ≤ b := by
    constructor <;> linarith
  have hlow_fin : fmt.finiteSystem low :=
    Or.inr (Or.inr ⟨false, n, hn, rfl⟩)
  rcases
      fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
        hpolicy hadj hsource_between with hy | hy
  · rw [hy]
    convert hlow_fin using 1
    dsimp [a, low]
    ring
  · rw [hy]
    have hfin_neg := fmt.finiteSystem_neg hlow_fin
    convert hfin_neg using 1
    have hres : (a + low) - b = -low := by
      linarith
    rw [hres]
/-- Operation-level positive same-sign mixed max-normal/subnormal addition has
finite representable local roundoff error at the exact half-ulp tie. -/
theorem finiteRoundToEvenOp_add_positive_max_normalized_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat}
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.maxNormalMantissa e)
          (fmt.subnormalValue false n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.maxNormalMantissa e)
          (fmt.subnormalValue false n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
      hn hlow hpolicy
/-- Commuted operation-level positive same-sign mixed subnormal/max-normal
addition has finite representable local roundoff error at the exact half-ulp
tie. -/
theorem finiteRoundToEvenOp_add_positive_subnormal_sameSign_max_normalized_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat}
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue false n +
          fmt.normalizedValue false fmt.maxNormalMantissa e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue false n +
          fmt.normalizedValue false fmt.maxNormalMantissa e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue false fmt.maxNormalMantissa e)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.subnormalValue false n +
          fmt.normalizedValue false fmt.maxNormalMantissa e)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue false fmt.maxNormalMantissa e)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue false fmt.maxNormalMantissa e)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue false fmt.maxNormalMantissa e +
            fmt.subnormalValue false n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.subnormalValue false n)
            (fmt.normalizedValue false fmt.maxNormalMantissa e)) :=
    fmt.sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
      hn hlow hpolicy
  convert hfin using 1
  ring
/-- Negative same-sign mixed max-normal/subnormal addition has finite local
error at the exact half-ulp tie by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n) - y) := by
  have hsource_neg :
      -(fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n) =
        fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n := by
    simp [normalizedValue, subnormalValue, signValue]
    ring
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    simpa [hsource_neg] using hneg
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false fmt.maxNormalMantissa e +
            fmt.subnormalValue false n) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
      hn hlow hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [normalizedValue, subnormalValue, signValue]
  ring
/-- Operation-level negative same-sign mixed max-normal/subnormal addition has
finite representable local roundoff error at the exact half-ulp tie. -/
theorem finiteRoundToEvenOp_add_negative_max_normalized_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.maxNormalMantissa e)
          (fmt.subnormalValue true n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.maxNormalMantissa e)
          (fmt.subnormalValue true n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
      hbeta ht hn hlow hpolicy
/-- Commuted operation-level negative same-sign mixed subnormal/max-normal
addition has finite representable local roundoff error at the exact half-ulp
tie. -/
theorem finiteRoundToEvenOp_add_negative_subnormal_sameSign_max_normalized_error_finiteSystem_of_low_eq_half_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow :
      fmt.subnormalValue false n =
        (1 / 2 : ℝ) * fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue true n +
          fmt.normalizedValue true fmt.maxNormalMantissa e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue true n +
          fmt.normalizedValue true fmt.maxNormalMantissa e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue true fmt.maxNormalMantissa e)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.subnormalValue true n +
          fmt.normalizedValue true fmt.maxNormalMantissa e)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue true fmt.maxNormalMantissa e)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue true fmt.maxNormalMantissa e)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue true fmt.maxNormalMantissa e +
            fmt.subnormalValue true n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.subnormalValue true n)
            (fmt.normalizedValue true fmt.maxNormalMantissa e)) :=
    fmt.sourceRoundToEvenEvidence_negative_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
      hbeta ht hn hlow hpolicy
  convert hfin using 1
  ring
/-- Positive same-sign mixed normal/subnormal addition has finite local error
in a strict right half-cell.

This is the mixed analogue of the normalized/normalized right-half branch.  The
right-half inequality derives the coefficient gap required to prove that the
subnormal-lattice residual `subnormal - ulp(e)` is finite representable. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (hemin : fmt.emin ≤ e)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent e <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue false n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.subnormalValue false n) - y) := by
  let a := fmt.normalizedValue false m e
  let b := fmt.normalizedValue false (m + 1) e
  let low := fmt.subnormalValue false n
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.subnormalValue_false_pos hn
  have hb_sub_a : b - a = fmt.ulpAtExponent e := by
    dsimp [a, b]
    simpa [ulpAtExponent, signValue] using
      (fmt.normalizedValue_succ_sub_sameExponent false m e)
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, m, e, hm, hmSucc, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have ha_lt_source : a < a + low := by
    linarith
  have hsource_lt_b : a + low < b := by
    linarith
  have hleft_abs : |(a + low) - a| = low := by
    have hsub : (a + low) - a = low := by ring
    rw [hsub, abs_of_pos hlow_pos]
  have hright_abs :
      |(a + low) - b| = fmt.ulpAtExponent e - low := by
    have hsub : (a + low) - b = low - fmt.ulpAtExponent e := by
      linarith
    have hneg : low - fmt.ulpAtExponent e < 0 := by
      linarith
    rw [hsub, abs_of_neg hneg]
    ring
  have hrightCloser : |(a + low) - b| < |(a + low) - a| := by
    rw [hleft_abs, hright_abs]
    linarith
  have hy : y = b := by
    exact
      fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
        hpolicy hadj ⟨ha_lt_source, hsource_lt_b⟩ hrightCloser
  have hd_cast :
      ((Int.toNat (e - fmt.emin) : ℕ) : ℤ) = e - fmt.emin := by
    have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr hemin
    simpa using Int.toNat_of_nonneg hnonneg
  have hgap :
      (((n : ℤ) -
          ((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ)).natAbs <
        fmt.beta ^ fmt.t) :=
    fmt.subnormal_right_half_coeff_gap_of_half_ulp_lt hn hemin hhalf
  have hulp_lattice :
      fmt.ulpAtExponent e =
        ((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
    have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
    have hpow :
        fmt.betaR ^ (((Int.toNat (e - fmt.emin) : ℕ) : ℤ)) =
          ((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℝ) := by
      rw [zpow_natCast]
      simp [betaR, Nat.cast_pow]
    calc
      fmt.ulpAtExponent e =
          fmt.betaR ^ (e - (fmt.t : ℤ)) := by
        rfl
      _ = fmt.betaR ^
            (((Int.toNat (e - fmt.emin) : ℕ) : ℤ) +
              (fmt.emin - (fmt.t : ℤ))) := by
        congr 1
        omega
      _ = fmt.betaR ^ (((Int.toNat (e - fmt.emin) : ℕ) : ℤ)) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
        rw [zpow_add₀ hbase]
      _ = ((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
        rw [hpow]
  have hfin_scaled :
      fmt.finiteSystem
        (fmt.signValue false * ((n : ℤ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) -
          fmt.signValue false *
            ((((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ) : ℝ)) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) :=
    fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := false) (k := (n : ℤ))
      (l := ((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ))
      (e := fmt.emin) ⟨le_rfl, fmt.emin_le_emax⟩ hgap
  rw [hy]
  change fmt.finiteSystem ((a + low) - b)
  convert hfin_scaled using 1
  have hres : (a + low) - b = low - fmt.ulpAtExponent e := by
    linarith
  rw [hres, hulp_lattice]
  dsimp [low]
  simp [subnormalValue, signValue]
/-- Operation-level positive same-sign mixed normal/subnormal addition has
finite representable local roundoff error in the strict right half-cell
branch. -/
theorem finiteRoundToEvenOp_add_positive_normalized_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (hemin : fmt.emin ≤ e)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent e <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false m e +
          fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue false n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.subnormalValue false n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hm hmSucc hn hemin hhalf hulp hpolicy
/-- Commuted operation-level positive same-sign mixed subnormal/normal addition
has finite representable local roundoff error in the strict right half-cell
branch. -/
theorem finiteRoundToEvenOp_add_positive_subnormal_sameSign_normalized_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (hemin : fmt.emin ≤ e)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent e <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue false n +
          fmt.normalizedValue false m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue false n +
          fmt.normalizedValue false m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue false m e)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.subnormalValue false n +
          fmt.normalizedValue false m e)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue false m e)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue false m e)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue false m e +
            fmt.subnormalValue false n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.subnormalValue false n)
            (fmt.normalizedValue false m e)) :=
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hm hmSucc hn hemin hhalf hulp hpolicy
  convert hfin using 1
  ring
/-- Negative same-sign mixed normal/subnormal addition has finite local error
in the strict right half-cell branch by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (hemin : fmt.emin ≤ e)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent e <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e +
          fmt.subnormalValue true n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e +
          fmt.subnormalValue true n) - y) := by
  have hsource_neg :
      -(fmt.normalizedValue true m e + fmt.subnormalValue true n) =
        fmt.normalizedValue false m e + fmt.subnormalValue false n := by
    simp [normalizedValue, subnormalValue, signValue]
    ring
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e +
          fmt.subnormalValue false n) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    simpa [hsource_neg] using hneg
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false m e +
            fmt.subnormalValue false n) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hm hmSucc hn hemin hhalf hulp hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [normalizedValue, subnormalValue, signValue]
  ring
/-- Operation-level negative same-sign mixed normal/subnormal addition has
finite representable local roundoff error in the strict right half-cell
branch. -/
theorem finiteRoundToEvenOp_add_negative_normalized_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (hemin : fmt.emin ≤ e)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent e <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true m e +
          fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue true n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e +
          fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true m e)
          (fmt.subnormalValue true n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hbeta ht hm hmSucc hn hemin hhalf hulp hpolicy
/-- Commuted operation-level negative same-sign mixed subnormal/normal addition
has finite representable local roundoff error in the strict right half-cell
branch. -/
theorem finiteRoundToEvenOp_add_negative_subnormal_sameSign_normalized_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (hemin : fmt.emin ≤ e)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent e <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue true n +
          fmt.normalizedValue true m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue true n +
          fmt.normalizedValue true m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue true m e)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.subnormalValue true n +
          fmt.normalizedValue true m e)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue true m e)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e +
          fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue true m e)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue true m e +
            fmt.subnormalValue true n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.subnormalValue true n)
            (fmt.normalizedValue true m e)) :=
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hbeta ht hm hmSucc hn hemin hhalf hulp hpolicy
  convert hfin using 1
  ring
/-- Positive same-sign mixed max-normal/subnormal addition has finite local
error in the strict right half-cell branch around the exponent-boundary
endpoint. -/
theorem sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hemin : fmt.emin ≤ e)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent e <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n) - y) := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa e
  let b := fmt.normalizedValue false fmt.minNormalMantissa (e + 1)
  let low := fmt.subnormalValue false n
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.subnormalValue_false_pos hn
  have hb_sub_a : b - a = fmt.ulpAtExponent e := by
    dsimp [a, b]
    simpa [ulpAtExponent, signValue] using
      (fmt.normalizedValue_boundary_sub false e)
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, e, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have ha_lt_source : a < a + low := by
    linarith
  have hsource_lt_b : a + low < b := by
    linarith
  have hleft_abs : |(a + low) - a| = low := by
    have hsub : (a + low) - a = low := by ring
    rw [hsub, abs_of_pos hlow_pos]
  have hright_abs :
      |(a + low) - b| = fmt.ulpAtExponent e - low := by
    have hsub : (a + low) - b = low - fmt.ulpAtExponent e := by
      linarith
    have hneg : low - fmt.ulpAtExponent e < 0 := by
      linarith
    rw [hsub, abs_of_neg hneg]
    ring
  have hrightCloser : |(a + low) - b| < |(a + low) - a| := by
    rw [hleft_abs, hright_abs]
    linarith
  have hy : y = b := by
    exact
      fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
        hpolicy hadj ⟨ha_lt_source, hsource_lt_b⟩ hrightCloser
  have hgap :
      (((n : ℤ) -
          ((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ)).natAbs <
        fmt.beta ^ fmt.t) :=
    fmt.subnormal_right_half_coeff_gap_of_half_ulp_lt hn hemin hhalf
  have hulp_lattice :
      fmt.ulpAtExponent e =
        ((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
    have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
    have hd_cast :
        ((Int.toNat (e - fmt.emin) : ℕ) : ℤ) = e - fmt.emin := by
      have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr hemin
      simpa using Int.toNat_of_nonneg hnonneg
    have hpow :
        fmt.betaR ^ (((Int.toNat (e - fmt.emin) : ℕ) : ℤ)) =
          ((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℝ) := by
      rw [zpow_natCast]
      simp [betaR, Nat.cast_pow]
    calc
      fmt.ulpAtExponent e =
          fmt.betaR ^ (e - (fmt.t : ℤ)) := by
        rfl
      _ = fmt.betaR ^
            (((Int.toNat (e - fmt.emin) : ℕ) : ℤ) +
              (fmt.emin - (fmt.t : ℤ))) := by
        congr 1
        omega
      _ = fmt.betaR ^ (((Int.toNat (e - fmt.emin) : ℕ) : ℤ)) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
        rw [zpow_add₀ hbase]
      _ = ((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
        rw [hpow]
  have hfin_scaled :
      fmt.finiteSystem
        (fmt.signValue false * ((n : ℤ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) -
          fmt.signValue false *
            ((((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ) : ℝ)) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) :=
    fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := false) (k := (n : ℤ))
      (l := ((fmt.beta ^ Int.toNat (e - fmt.emin) : ℕ) : ℤ))
      (e := fmt.emin) ⟨le_rfl, fmt.emin_le_emax⟩ hgap
  rw [hy]
  change fmt.finiteSystem ((a + low) - b)
  convert hfin_scaled using 1
  have hres : (a + low) - b = low - fmt.ulpAtExponent e := by
    linarith
  rw [hres, hulp_lattice]
  dsimp [low]
  simp [subnormalValue, signValue]
/-- Operation-level positive same-sign mixed max-normal/subnormal addition has
finite representable local roundoff error in the strict right half-cell branch. -/
theorem finiteRoundToEvenOp_add_positive_max_normalized_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat}
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hemin : fmt.emin ≤ e)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent e <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.maxNormalMantissa e)
          (fmt.subnormalValue false n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false fmt.maxNormalMantissa e)
          (fmt.subnormalValue false n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hn hemin hhalf hulp hpolicy
/-- Commuted operation-level positive same-sign mixed subnormal/max-normal
addition has finite representable local roundoff error in the strict right
half-cell branch. -/
theorem finiteRoundToEvenOp_add_positive_subnormal_sameSign_max_normalized_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat}
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hemin : fmt.emin ≤ e)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent e <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue false n +
          fmt.normalizedValue false fmt.maxNormalMantissa e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue false n +
          fmt.normalizedValue false fmt.maxNormalMantissa e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue false fmt.maxNormalMantissa e)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.subnormalValue false n +
          fmt.normalizedValue false fmt.maxNormalMantissa e)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue false fmt.maxNormalMantissa e)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue false n)
          (fmt.normalizedValue false fmt.maxNormalMantissa e)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue false fmt.maxNormalMantissa e +
            fmt.subnormalValue false n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.subnormalValue false n)
            (fmt.normalizedValue false fmt.maxNormalMantissa e)) :=
    fmt.sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hn hemin hhalf hulp hpolicy
  convert hfin using 1
  ring
/-- Negative same-sign mixed max-normal/subnormal addition has finite local
error in the strict right half-cell branch by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hemin : fmt.emin ≤ e)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent e <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n) - y) := by
  have hsource_neg :
      -(fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n) =
        fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n := by
    simp [normalizedValue, subnormalValue, signValue]
    ring
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.maxNormalMantissa e +
          fmt.subnormalValue false n) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    simpa [hsource_neg] using hneg
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false fmt.maxNormalMantissa e +
            fmt.subnormalValue false n) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hn hemin hhalf hulp hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [normalizedValue, subnormalValue, signValue]
  ring
/-- Operation-level negative same-sign mixed max-normal/subnormal addition has
finite representable local roundoff error in the strict right half-cell branch. -/
theorem finiteRoundToEvenOp_add_negative_max_normalized_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hemin : fmt.emin ≤ e)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent e <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.maxNormalMantissa e)
          (fmt.subnormalValue true n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue true fmt.maxNormalMantissa e)
          (fmt.subnormalValue true n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_negative_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hbeta ht hn hemin hhalf hulp hpolicy
/-- Commuted operation-level negative same-sign mixed subnormal/max-normal
addition has finite representable local roundoff error in the strict right
half-cell branch. -/
theorem finiteRoundToEvenOp_add_negative_subnormal_sameSign_max_normalized_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hemin : fmt.emin ≤ e)
    (hhalf :
      (1 / 2 : ℝ) * fmt.ulpAtExponent e <
        fmt.subnormalValue false n)
    (hulp :
      fmt.subnormalValue false n < fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue true n +
          fmt.normalizedValue true fmt.maxNormalMantissa e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue true n +
          fmt.normalizedValue true fmt.maxNormalMantissa e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue true fmt.maxNormalMantissa e)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.subnormalValue true n +
          fmt.normalizedValue true fmt.maxNormalMantissa e)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue true fmt.maxNormalMantissa e)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.maxNormalMantissa e +
          fmt.subnormalValue true n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue true n)
          (fmt.normalizedValue true fmt.maxNormalMantissa e)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue true fmt.maxNormalMantissa e +
            fmt.subnormalValue true n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.subnormalValue true n)
            (fmt.normalizedValue true fmt.maxNormalMantissa e)) :=
    fmt.sourceRoundToEvenEvidence_negative_max_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
      hbeta ht hn hemin hhalf hulp hpolicy
  convert hfin using 1
  ring
/-- Same-sign mixed normal/subnormal exact-successor source sums are finite:
when the subnormal addend is exactly one ulp at the normal exponent, the exact
sum is the normal operand's same-exponent successor. -/
theorem normalizedValue_add_sameSign_subnormal_finiteSystem_of_low_eq_ulp
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (he : fmt.exponentInRange e)
    (hlow : fmt.subnormalValue false n = fmt.ulpAtExponent e) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e + fmt.subnormalValue negative n) := by
  cases negative
  · let a := fmt.normalizedValue false m e
    let b := fmt.normalizedValue false (m + 1) e
    let low := fmt.subnormalValue false n
    have hb_sub_a : b - a = fmt.ulpAtExponent e := by
      dsimp [a, b]
      simpa [ulpAtExponent, signValue] using
        (fmt.normalizedValue_succ_sub_sameExponent false m e)
    have hsource_eq : a + low = b := by
      dsimp [low]
      linarith
    change fmt.finiteSystem (a + low)
    rw [hsource_eq]
    exact Or.inr (Or.inl ⟨false, m + 1, e, hmSucc, he, rfl⟩)
  · let a := fmt.normalizedValue true m e
    let b := fmt.normalizedValue true (m + 1) e
    let lowNeg := fmt.subnormalValue true n
    have hb_sub_a : b - a = -fmt.ulpAtExponent e := by
      dsimp [a, b]
      simpa [ulpAtExponent, signValue] using
        (fmt.normalizedValue_succ_sub_sameExponent true m e)
    have hlowNeg : lowNeg = -fmt.ulpAtExponent e := by
      dsimp [lowNeg]
      simpa [hlow] using fmt.subnormalValue_not_eq_neg false n
    have hsource_eq : a + lowNeg = b := by
      linarith
    change fmt.finiteSystem (a + lowNeg)
    rw [hsource_eq]
    exact Or.inr (Or.inl ⟨true, m + 1, e, hmSucc, he, rfl⟩)
/-- Same-sign mixed max-normal/subnormal exact-successor source sums are
finite: at the max mantissa, adding exactly one ulp reaches the next-binade
minimum endpoint. -/
theorem max_normalizedValue_add_sameSign_subnormal_finiteSystem_of_low_eq_ulp
    {fmt : FloatingPointFormat} {negative : Bool} {n : ℕ} {e : ℤ}
    (hlow : fmt.subnormalValue false n = fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative fmt.maxNormalMantissa e +
          fmt.subnormalValue negative n)) :
    fmt.finiteSystem
      (fmt.normalizedValue negative fmt.maxNormalMantissa e +
        fmt.subnormalValue negative n) := by
  cases negative
  · let a := fmt.normalizedValue false fmt.maxNormalMantissa e
    let b := fmt.normalizedValue false fmt.minNormalMantissa (e + 1)
    let low := fmt.subnormalValue false n
    have hb_sub_a : b - a = fmt.ulpAtExponent e := by
      dsimp [a, b]
      simpa [ulpAtExponent, signValue] using
        (fmt.normalizedValue_boundary_sub false e)
    have hsource_eq : a + low = b := by
      dsimp [low]
      linarith
    have hb_unbounded : fmt.unboundedNormalizedSystem b :=
      ⟨false, fmt.minNormalMantissa, e + 1,
        fmt.minNormalMantissa_normalized, rfl⟩
    have hb_range : fmt.finiteNormalRange b := by
      change fmt.finiteNormalRange (a + low) at hxy
      rwa [hsource_eq] at hxy
    have hb_norm : fmt.normalizedSystem b :=
      fmt.unboundedNormalizedSystem_normalizedSystem_of_finiteNormalRange
        hb_unbounded hb_range
    change fmt.finiteSystem (a + low)
    rw [hsource_eq]
    exact Or.inr (Or.inl hb_norm)
  · let a := fmt.normalizedValue true fmt.maxNormalMantissa e
    let b := fmt.normalizedValue true fmt.minNormalMantissa (e + 1)
    let lowNeg := fmt.subnormalValue true n
    have hb_sub_a : b - a = -fmt.ulpAtExponent e := by
      dsimp [a, b]
      simpa [ulpAtExponent, signValue] using
        (fmt.normalizedValue_boundary_sub true e)
    have hlowNeg : lowNeg = -fmt.ulpAtExponent e := by
      dsimp [lowNeg]
      simpa [hlow] using fmt.subnormalValue_not_eq_neg false n
    have hsource_eq : a + lowNeg = b := by
      linarith
    have hb_unbounded : fmt.unboundedNormalizedSystem b :=
      ⟨true, fmt.minNormalMantissa, e + 1,
        fmt.minNormalMantissa_normalized, rfl⟩
    have hb_range : fmt.finiteNormalRange b := by
      change fmt.finiteNormalRange (a + lowNeg) at hxy
      rwa [hsource_eq] at hxy
    have hb_norm : fmt.normalizedSystem b :=
      fmt.unboundedNormalizedSystem_normalizedSystem_of_finiteNormalRange
        hb_unbounded hb_range
    change fmt.finiteSystem (a + lowNeg)
    rw [hsource_eq]
    exact Or.inr (Or.inl hb_norm)
/-- Same-sign mixed normal/subnormal addition is exact when the subnormal
addend is exactly one ulp at the normal exponent and the normal mantissa has a
same-exponent successor. -/
theorem finiteRoundToEvenOp_add_normalized_sameSign_subnormal_eq_exact_of_low_eq_ulp
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (_hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (_hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hlow : fmt.subnormalValue false n = fmt.ulpAtExponent e) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue negative m e)
        (fmt.subnormalValue negative n) =
      fmt.normalizedValue negative m e + fmt.subnormalValue negative n := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) :=
    fmt.normalizedValue_add_sameSign_subnormal_finiteSystem_of_low_eq_ulp
      hmSucc he hlow
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue negative m e)
      (y := fmt.subnormalValue negative n) hfin)
/-- The mixed normal/subnormal exact-successor branch has zero local roundoff
error, hence a finite representable error. -/
theorem finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_low_eq_ulp
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hlow : fmt.subnormalValue false n = fmt.ulpAtExponent e) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.subnormalValue negative n)) := by
  rw [
    finiteRoundToEvenOp_add_normalized_sameSign_subnormal_eq_exact_of_low_eq_ulp
      hm hmSucc hn he hlow]
  simpa using fmt.finiteSystem_zero
/-- Commuted same-sign mixed subnormal/normal addition is exact in the
exact-successor branch. -/
theorem finiteRoundToEvenOp_add_subnormal_sameSign_normalized_eq_exact_of_low_eq_ulp
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (_hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (_hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hlow : fmt.subnormalValue false n = fmt.ulpAtExponent e) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.subnormalValue negative n)
        (fmt.normalizedValue negative m e) =
      fmt.subnormalValue negative n + fmt.normalizedValue negative m e := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) :=
    fmt.normalizedValue_add_sameSign_subnormal_finiteSystem_of_low_eq_ulp
      hmSucc he hlow
  have hfin_comm :
      fmt.finiteSystem
        (fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e) := by
    convert hfin using 1
    ring
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.subnormalValue negative n)
      (y := fmt.normalizedValue negative m e) hfin_comm)
/-- The commuted mixed subnormal/normal exact-successor branch has zero local
roundoff error, hence a finite representable error. -/
theorem finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_low_eq_ulp
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hlow : fmt.subnormalValue false n = fmt.ulpAtExponent e) :
    fmt.finiteSystem
      ((fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative m e)) := by
  rw [
    finiteRoundToEvenOp_add_subnormal_sameSign_normalized_eq_exact_of_low_eq_ulp
      hm hmSucc hn he hlow]
  simpa using fmt.finiteSystem_zero
/-- Same-sign mixed max-normal/subnormal addition is exact when the subnormal
addend is exactly one ulp at the max-normal exponent.  The exact source sum is
the next-binade minimum endpoint. -/
theorem finiteRoundToEvenOp_add_max_normalized_sameSign_subnormal_eq_exact_of_low_eq_ulp
    {fmt : FloatingPointFormat} {negative : Bool} {n : ℕ} {e : ℤ}
    (_hn : fmt.subnormalMantissa n)
    (hlow : fmt.subnormalValue false n = fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative fmt.maxNormalMantissa e +
          fmt.subnormalValue negative n)) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue negative fmt.maxNormalMantissa e)
        (fmt.subnormalValue negative n) =
      fmt.normalizedValue negative fmt.maxNormalMantissa e +
        fmt.subnormalValue negative n := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue negative fmt.maxNormalMantissa e +
          fmt.subnormalValue negative n) :=
    fmt.max_normalizedValue_add_sameSign_subnormal_finiteSystem_of_low_eq_ulp
      hlow hxy
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue negative fmt.maxNormalMantissa e)
      (y := fmt.subnormalValue negative n) hfin)
/-- The mixed max-normal/subnormal exact-successor boundary branch has zero
local roundoff error, hence a finite representable error. -/
theorem finiteRoundToEvenOp_add_max_normalized_sameSign_subnormal_error_finiteSystem_of_low_eq_ulp
    {fmt : FloatingPointFormat} {negative : Bool} {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow : fmt.subnormalValue false n = fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative fmt.maxNormalMantissa e +
          fmt.subnormalValue negative n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative fmt.maxNormalMantissa e +
          fmt.subnormalValue negative n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative fmt.maxNormalMantissa e)
          (fmt.subnormalValue negative n)) := by
  rw [
    finiteRoundToEvenOp_add_max_normalized_sameSign_subnormal_eq_exact_of_low_eq_ulp
      hn hlow hxy]
  simpa using fmt.finiteSystem_zero
/-- Commuted same-sign mixed subnormal/max-normal addition is exact in the
exact-successor boundary branch. -/
theorem finiteRoundToEvenOp_add_subnormal_sameSign_max_normalized_eq_exact_of_low_eq_ulp
    {fmt : FloatingPointFormat} {negative : Bool} {n : ℕ} {e : ℤ}
    (_hn : fmt.subnormalMantissa n)
    (hlow : fmt.subnormalValue false n = fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue negative n +
          fmt.normalizedValue negative fmt.maxNormalMantissa e)) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.subnormalValue negative n)
        (fmt.normalizedValue negative fmt.maxNormalMantissa e) =
      fmt.subnormalValue negative n +
        fmt.normalizedValue negative fmt.maxNormalMantissa e := by
  have hxy_order :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative fmt.maxNormalMantissa e +
          fmt.subnormalValue negative n) := by
    convert hxy using 1
    ring
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue negative fmt.maxNormalMantissa e +
          fmt.subnormalValue negative n) :=
    fmt.max_normalizedValue_add_sameSign_subnormal_finiteSystem_of_low_eq_ulp
      hlow hxy_order
  have hfin_comm :
      fmt.finiteSystem
        (fmt.subnormalValue negative n +
          fmt.normalizedValue negative fmt.maxNormalMantissa e) := by
    convert hfin using 1
    ring
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.subnormalValue negative n)
      (y := fmt.normalizedValue negative fmt.maxNormalMantissa e) hfin_comm)
/-- The commuted mixed subnormal/max-normal exact-successor boundary branch has
zero local roundoff error, hence a finite representable error. -/
theorem finiteRoundToEvenOp_add_subnormal_sameSign_max_normalized_error_finiteSystem_of_low_eq_ulp
    {fmt : FloatingPointFormat} {negative : Bool} {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hlow : fmt.subnormalValue false n = fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue negative n +
          fmt.normalizedValue negative fmt.maxNormalMantissa e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue negative n +
          fmt.normalizedValue negative fmt.maxNormalMantissa e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative fmt.maxNormalMantissa e)) := by
  rw [
    finiteRoundToEvenOp_add_subnormal_sameSign_max_normalized_eq_exact_of_low_eq_ulp
      hn hlow hxy]
  simpa using fmt.finiteSystem_zero
/-- Dispatcher for the same-sign mixed normal/subnormal low-cell split.

This packages the strict-left, half-ulp tie, strict-right, and exact-successor
branches for an ordinary normal mantissa with a same-exponent successor. -/
theorem finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_low_cell_cases
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hemin : fmt.emin ≤ e)
    (hcell :
      fmt.subnormalValue false n <
          (1 / 2 : ℝ) * fmt.ulpAtExponent e ∨
        fmt.subnormalValue false n =
          (1 / 2 : ℝ) * fmt.ulpAtExponent e ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent e <
            fmt.subnormalValue false n ∧
          fmt.subnormalValue false n < fmt.ulpAtExponent e) ∨
        fmt.subnormalValue false n = fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.subnormalValue negative n)) := by
  rcases hcell with hlt | hrest
  · cases negative
    · exact
        fmt.finiteRoundToEvenOp_add_positive_normalized_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
          hm hmSucc hn hlt hxy
    · exact
        fmt.finiteRoundToEvenOp_add_negative_normalized_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
          hbeta ht hm hmSucc hn hlt hxy
  · rcases hrest with heq | hrest
    · cases negative
      · exact
          fmt.finiteRoundToEvenOp_add_positive_normalized_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
            hm hmSucc hn heq hxy
      · exact
          fmt.finiteRoundToEvenOp_add_negative_normalized_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
            hbeta ht hm hmSucc hn heq hxy
    · rcases hrest with hright | hulp
      · cases negative
        · exact
            fmt.finiteRoundToEvenOp_add_positive_normalized_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
              hm hmSucc hn hemin hright.1 hright.2 hxy
        · exact
            fmt.finiteRoundToEvenOp_add_negative_normalized_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
              hbeta ht hm hmSucc hn hemin hright.1 hright.2 hxy
      · exact
          fmt.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_low_eq_ulp
            hm hmSucc hn he hulp
/-- Commuted dispatcher for the same-sign mixed subnormal/normal low-cell
split. -/
theorem finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_low_cell_cases
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmSucc : fmt.normalizedMantissa (m + 1))
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hemin : fmt.emin ≤ e)
    (hcell :
      fmt.subnormalValue false n <
          (1 / 2 : ℝ) * fmt.ulpAtExponent e ∨
        fmt.subnormalValue false n =
          (1 / 2 : ℝ) * fmt.ulpAtExponent e ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent e <
            fmt.subnormalValue false n ∧
          fmt.subnormalValue false n < fmt.ulpAtExponent e) ∨
        fmt.subnormalValue false n = fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative m e)) := by
  rcases hcell with hlt | hrest
  · cases negative
    · exact
        fmt.finiteRoundToEvenOp_add_positive_subnormal_sameSign_normalized_error_finiteSystem_of_low_lt_half_ulp
          hm hmSucc hn hlt hxy
    · exact
        fmt.finiteRoundToEvenOp_add_negative_subnormal_sameSign_normalized_error_finiteSystem_of_low_lt_half_ulp
          hbeta ht hm hmSucc hn hlt hxy
  · rcases hrest with heq | hrest
    · cases negative
      · exact
          fmt.finiteRoundToEvenOp_add_positive_subnormal_sameSign_normalized_error_finiteSystem_of_low_eq_half_ulp
            hm hmSucc hn heq hxy
      · exact
          fmt.finiteRoundToEvenOp_add_negative_subnormal_sameSign_normalized_error_finiteSystem_of_low_eq_half_ulp
            hbeta ht hm hmSucc hn heq hxy
    · rcases hrest with hright | hulp
      · cases negative
        · exact
            fmt.finiteRoundToEvenOp_add_positive_subnormal_sameSign_normalized_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
              hm hmSucc hn hemin hright.1 hright.2 hxy
        · exact
            fmt.finiteRoundToEvenOp_add_negative_subnormal_sameSign_normalized_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
              hbeta ht hm hmSucc hn hemin hright.1 hright.2 hxy
      · exact
          fmt.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_low_eq_ulp
            hm hmSucc hn he hulp
/-- Dispatcher for the same-sign mixed max-normal/subnormal low-cell split.

The exact-successor branch crosses the exponent boundary and therefore keeps
the finite-normal-range hypothesis visible. -/
theorem finiteRoundToEvenOp_add_max_normalized_sameSign_subnormal_error_finiteSystem_of_low_cell_cases
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hemin : fmt.emin ≤ e)
    (hcell :
      fmt.subnormalValue false n <
          (1 / 2 : ℝ) * fmt.ulpAtExponent e ∨
        fmt.subnormalValue false n =
          (1 / 2 : ℝ) * fmt.ulpAtExponent e ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent e <
            fmt.subnormalValue false n ∧
          fmt.subnormalValue false n < fmt.ulpAtExponent e) ∨
        fmt.subnormalValue false n = fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative fmt.maxNormalMantissa e +
          fmt.subnormalValue negative n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative fmt.maxNormalMantissa e +
          fmt.subnormalValue negative n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative fmt.maxNormalMantissa e)
          (fmt.subnormalValue negative n)) := by
  rcases hcell with hlt | hrest
  · cases negative
    · exact
        fmt.finiteRoundToEvenOp_add_positive_max_normalized_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
          hn hlt hxy
    · exact
        fmt.finiteRoundToEvenOp_add_negative_max_normalized_sameSign_subnormal_error_finiteSystem_of_low_lt_half_ulp
          hbeta ht hn hlt hxy
  · rcases hrest with heq | hrest
    · cases negative
      · exact
          fmt.finiteRoundToEvenOp_add_positive_max_normalized_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
            hn heq hxy
      · exact
          fmt.finiteRoundToEvenOp_add_negative_max_normalized_sameSign_subnormal_error_finiteSystem_of_low_eq_half_ulp
            hbeta ht hn heq hxy
    · rcases hrest with hright | hulp
      · cases negative
        · exact
            fmt.finiteRoundToEvenOp_add_positive_max_normalized_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
              hn hemin hright.1 hright.2 hxy
        · exact
            fmt.finiteRoundToEvenOp_add_negative_max_normalized_sameSign_subnormal_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
              hbeta ht hn hemin hright.1 hright.2 hxy
      · exact
          fmt.finiteRoundToEvenOp_add_max_normalized_sameSign_subnormal_error_finiteSystem_of_low_eq_ulp
            hn hulp hxy
/-- Commuted dispatcher for the same-sign mixed subnormal/max-normal low-cell
split. -/
theorem finiteRoundToEvenOp_add_subnormal_sameSign_max_normalized_error_finiteSystem_of_low_cell_cases
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {n : ℕ} {e : ℤ}
    (hn : fmt.subnormalMantissa n)
    (hemin : fmt.emin ≤ e)
    (hcell :
      fmt.subnormalValue false n <
          (1 / 2 : ℝ) * fmt.ulpAtExponent e ∨
        fmt.subnormalValue false n =
          (1 / 2 : ℝ) * fmt.ulpAtExponent e ∨
        ((1 / 2 : ℝ) * fmt.ulpAtExponent e <
            fmt.subnormalValue false n ∧
          fmt.subnormalValue false n < fmt.ulpAtExponent e) ∨
        fmt.subnormalValue false n = fmt.ulpAtExponent e)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue negative n +
          fmt.normalizedValue negative fmt.maxNormalMantissa e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue negative n +
          fmt.normalizedValue negative fmt.maxNormalMantissa e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative fmt.maxNormalMantissa e)) := by
  rcases hcell with hlt | hrest
  · cases negative
    · exact
        fmt.finiteRoundToEvenOp_add_positive_subnormal_sameSign_max_normalized_error_finiteSystem_of_low_lt_half_ulp
          hn hlt hxy
    · exact
        fmt.finiteRoundToEvenOp_add_negative_subnormal_sameSign_max_normalized_error_finiteSystem_of_low_lt_half_ulp
          hbeta ht hn hlt hxy
  · rcases hrest with heq | hrest
    · cases negative
      · exact
          fmt.finiteRoundToEvenOp_add_positive_subnormal_sameSign_max_normalized_error_finiteSystem_of_low_eq_half_ulp
            hn heq hxy
      · exact
          fmt.finiteRoundToEvenOp_add_negative_subnormal_sameSign_max_normalized_error_finiteSystem_of_low_eq_half_ulp
            hbeta ht hn heq hxy
    · rcases hrest with hright | hulp
      · cases negative
        · exact
            fmt.finiteRoundToEvenOp_add_positive_subnormal_sameSign_max_normalized_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
              hn hemin hright.1 hright.2 hxy
        · exact
            fmt.finiteRoundToEvenOp_add_negative_subnormal_sameSign_max_normalized_error_finiteSystem_of_half_ulp_lt_low_lt_ulp
              hbeta ht hn hemin hright.1 hright.2 hxy
      · exact
          fmt.finiteRoundToEvenOp_add_subnormal_sameSign_max_normalized_error_finiteSystem_of_low_eq_ulp
            hn hulp hxy
/-- Same-sign, same-exponent subtraction is exact for the concrete finite
round-to-even operation wrapper.  The finite-system side condition is discharged
by the derived same-exponent finite-difference selector. -/
theorem finiteRoundToEvenOp_sub_sameSign_sameExponent_eq_exact
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e) :
    fmt.finiteRoundToEvenOp BasicOp.sub
        (fmt.normalizedValue negative m e)
        (fmt.normalizedValue negative n e) =
      fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue negative m e -
          fmt.normalizedValue negative n e) :=
    fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedMantissas
      (negative := negative) (m := m) (n := n) (e := e) hm hn he
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub)
      (x := fmt.normalizedValue negative m e)
      (y := fmt.normalizedValue negative n e) hfin)
/-- Same-sign subnormal subtraction is exact for the concrete finite
round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_sub_sameSign_subnormal_eq_exact
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ}
    (hm : fmt.subnormalMantissa m)
    (hn : fmt.subnormalMantissa n) :
    fmt.finiteRoundToEvenOp BasicOp.sub
        (fmt.subnormalValue negative m)
        (fmt.subnormalValue negative n) =
      fmt.subnormalValue negative m -
        fmt.subnormalValue negative n := by
  have hfin :
      fmt.finiteSystem
        (fmt.subnormalValue negative m -
          fmt.subnormalValue negative n) :=
    fmt.subnormalValue_sub_sameSign_finiteSystem_of_subnormalMantissas
      (negative := negative) (m := m) (n := n) hm hn
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub)
      (x := fmt.subnormalValue negative m)
      (y := fmt.subnormalValue negative n) hfin)
/-- Finite round-to-even addition satisfies the left-add-zero law whenever the
input is finite representable.  This is the concrete side condition needed for
the `FPModel.fl_add_zero` law on the ordinary finite wrapper. -/
theorem finiteRoundToEvenOp_add_zero_of_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    fmt.finiteRoundToEvenOp BasicOp.add 0 x = x := by
  simpa [finiteRoundToEvenOp, BasicOp.exact] using
    fmt.finiteRoundToEven_eq_self_of_finiteSystem hx
/-- Finite round-to-even addition satisfies the right-add-zero law whenever the
input is finite representable. -/
theorem finiteRoundToEvenOp_add_zero_right_of_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    fmt.finiteRoundToEvenOp BasicOp.add x 0 = x := by
  simpa [finiteRoundToEvenOp, BasicOp.exact] using
    fmt.finiteRoundToEven_eq_self_of_finiteSystem hx
/-- The local add roundoff error is finite when the left operand is zero and
the right operand is finite. -/
theorem finiteRoundToEvenOp_add_zero_error_finiteSystem_of_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    fmt.finiteSystem
      ((0 + x) - fmt.finiteRoundToEvenOp BasicOp.add 0 x) := by
  rw [fmt.finiteRoundToEvenOp_add_zero_of_finiteSystem hx]
  simpa using fmt.finiteSystem_zero
/-- The local add roundoff error is finite when the right operand is zero and
the left operand is finite. -/
theorem finiteRoundToEvenOp_add_zero_right_error_finiteSystem_of_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    fmt.finiteSystem
      ((x + 0) - fmt.finiteRoundToEvenOp BasicOp.add x 0) := by
  rw [fmt.finiteRoundToEvenOp_add_zero_right_of_finiteSystem hx]
  simpa using fmt.finiteSystem_zero
/-- Same-sign finite operands have finite representable local add roundoff
error in the base-2 finite-normal branch.

This lifts the explicit normalized/normalized, mixed normal/subnormal,
all-subnormal, and zero branches to ordinary source values with supplied
same-sign finite representations. -/
theorem finiteRoundToEvenOp_add_sameSign_finiteSystemWithSign_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {negative : Bool} {x y : ℝ}
    (hx : fmt.finiteSystemWithSign negative x)
    (hy : fmt.finiteSystemWithSign negative y)
    (hxy : fmt.finiteNormalRange (x + y)) :
    fmt.finiteSystem
      ((x + y) - fmt.finiteRoundToEvenOp BasicOp.add x y) := by
  have hxfin : fmt.finiteSystem x :=
    fmt.finiteSystem_of_finiteSystemWithSign hx
  have hyfin : fmt.finiteSystem y :=
    fmt.finiteSystem_of_finiteSystemWithSign hy
  rcases hx with rfl | hxnonzero
  · exact fmt.finiteRoundToEvenOp_add_zero_error_finiteSystem_of_finiteSystem hyfin
  rcases hy with rfl | hynonzero
  · exact
      fmt.finiteRoundToEvenOp_add_zero_right_error_finiteSystem_of_finiteSystem
        hxfin
  rcases hxnonzero with hxnorm | hxsub
  · rcases hxnorm with ⟨m, e, hm, he, rfl⟩
    rcases hynonzero with hynorm | hysub
    · rcases hynorm with ⟨n, f, hn, hf, rfl⟩
      exact
        fmt.finiteRoundToEvenOp_add_sameSign_normalized_error_finiteSystem_of_baseTwo
          hbeta ht hm hn he hf hxy
    · rcases hysub with ⟨n, hn, rfl⟩
      exact
        fmt.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_baseTwo
          hbeta ht hm hn he hxy
  · rcases hxsub with ⟨m, hm, rfl⟩
    rcases hynonzero with hynorm | hysub
    · rcases hynorm with ⟨n, e, hn, he, rfl⟩
      exact
        fmt.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_baseTwo
          hbeta ht hn hm he hxy
    · rcases hysub with ⟨n, hn, rfl⟩
      exact
        fmt.finiteRoundToEvenOp_add_sameSign_subnormal_error_finiteSystem hm hn
/-- Arbitrary finite base-2 operands have finite representable local add
roundoff error whenever the exact sum stays in the finite normal range.

This is the ordinary finite-system dispatcher for Chapter 4's correction-formula
work: zero, normalized/normalized, mixed normal/subnormal, and all-subnormal
branches are delegated to the explicit branch theorems above. -/
theorem finiteRoundToEvenOp_add_finiteSystem_error_finiteSystem_of_baseTwo
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {x y : ℝ}
    (hx : fmt.finiteSystem x)
    (hy : fmt.finiteSystem y)
    (hxy : fmt.finiteNormalRange (x + y)) :
    fmt.finiteSystem
      ((x + y) - fmt.finiteRoundToEvenOp BasicOp.add x y) := by
  have hxfin : fmt.finiteSystem x := hx
  have hyfin : fmt.finiteSystem y := hy
  rcases hx with rfl | hxnonzero
  · exact fmt.finiteRoundToEvenOp_add_zero_error_finiteSystem_of_finiteSystem hyfin
  rcases hy with rfl | hynonzero
  · exact
      fmt.finiteRoundToEvenOp_add_zero_right_error_finiteSystem_of_finiteSystem
        hxfin
  rcases hxnonzero with hxnorm | hxsub
  · rcases hxnorm with ⟨sx, m, e, hm, he, rfl⟩
    rcases hynonzero with hynorm | hysub
    · rcases hynorm with ⟨sy, n, f, hn, hf, rfl⟩
      cases sx <;> cases sy
      · exact
          fmt.finiteRoundToEvenOp_add_sameSign_normalized_error_finiteSystem_of_baseTwo
            hbeta ht hm hn he hf hxy
      · exact
          fmt.finiteRoundToEvenOp_add_positive_neg_normalized_error_finiteSystem_of_baseTwo
            hbeta ht hm hn he hf hxy
      · exact
          fmt.finiteRoundToEvenOp_add_negative_pos_normalized_error_finiteSystem_of_baseTwo
            hbeta ht hm hn he hf hxy
      · exact
          fmt.finiteRoundToEvenOp_add_sameSign_normalized_error_finiteSystem_of_baseTwo
            hbeta ht hm hn he hf hxy
    · rcases hysub with ⟨sy, n, hn, rfl⟩
      cases sx <;> cases sy
      · exact
          fmt.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_baseTwo
            hbeta ht hm hn he hxy
      · exact
          fmt.finiteRoundToEvenOp_add_positive_normalized_neg_subnormal_error_finiteSystem_of_baseTwo
            hbeta ht hm hn he hxy
      · exact
          fmt.finiteRoundToEvenOp_add_negative_normalized_pos_subnormal_error_finiteSystem_of_baseTwo
            hbeta ht hm hn he hxy
      · exact
          fmt.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_baseTwo
            hbeta ht hm hn he hxy
  · rcases hxsub with ⟨sx, m, hm, rfl⟩
    rcases hynonzero with hynorm | hysub
    · rcases hynorm with ⟨sy, n, e, hn, he, rfl⟩
      cases sx <;> cases sy
      · exact
          fmt.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_baseTwo
            hbeta ht hn hm he hxy
      · exact
          fmt.finiteRoundToEvenOp_add_positive_subnormal_neg_normalized_error_finiteSystem_of_baseTwo
            hbeta ht hn hm he hxy
      · exact
          fmt.finiteRoundToEvenOp_add_negative_subnormal_pos_normalized_error_finiteSystem_of_baseTwo
            hbeta ht hn hm he hxy
      · exact
          fmt.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_baseTwo
            hbeta ht hn hm he hxy
    · rcases hysub with ⟨sy, n, hn, rfl⟩
      exact fmt.finiteRoundToEvenOp_add_subnormal_error_finiteSystem hm hn
/-- Paper-facing finite-add error theorem for the source orientation
`|b| < |a|`.  The magnitude ordering is retained in the statement because it is
the source-side hypothesis for the correction formula, but the branch dispatcher
above proves a slightly stronger finite-system fact. -/
theorem finiteRoundToEvenOp_add_error_finite_of_base2_abs_order_of_finiteNormalRange
    {fmt : FloatingPointFormat}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a)
    (hb : fmt.finiteSystem b)
    (_hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b)) :
    fmt.finiteSystem
      ((a + b) - fmt.finiteRoundToEvenOp BasicOp.add a b) :=
  fmt.finiteRoundToEvenOp_add_finiteSystem_error_finiteSystem_of_baseTwo
    hbeta ht ha hb habRange
theorem finiteRoundToEvenOp_signedRelErrorWitness_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite (BasicOp.exact op x y)
          (fmt.finiteRoundToEvenOp op x y) ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness (fmt.finiteRoundToEvenOp op x y)
            (BasicOp.exact op x y) δ := by
  rcases
    fmt.finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange
      hxy with
    ⟨δ, hround, hδ, hwit⟩
  exact
    ⟨δ, by simpa [finiteRoundToEvenOp] using hround, hδ,
      by simpa [finiteRoundToEvenOp] using hwit⟩
theorem finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        fmt.finiteRoundToEvenOp op x y =
          BasicOp.exact op x y * (1 + δ) := by
  rcases
    fmt.finiteRoundToEvenOp_signedRelErrorWitness_lt_of_finiteNormalRange
      hxy with
    ⟨δ, _hround, hδ, hwit⟩
  exact ⟨δ, hδ, by simpa [signedRelErrorWitness] using hwit⟩
/-- Operation-level finite round-to-even wrapper for the real square root used
in Higham's standard model note after (2.4).  The standard-model theorem below
is stated on nonnegative inputs whose exact square root is finite-normal. -/
noncomputable def finiteRoundToEvenSqrt (fmt : FloatingPointFormat)
    (x : ℝ) : ℝ :=
  fmt.finiteRoundToEven (Real.sqrt x)
/-- Operation-level finite square-root selector parameterized by an IEEE
rounding mode.  It rounds the exact real square root with the total
source-facing finite selector for that mode. -/
noncomputable def finiteRoundToModeSqrt
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) : ℝ :=
  fmt.finiteRoundToMode mode (Real.sqrt x)
theorem finiteRoundToModeSqrt_nearestEven
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteRoundToModeSqrt IeeeRoundingMode.nearestEven x =
      fmt.finiteRoundToEvenSqrt x := rfl
theorem finiteRoundToModeSqrt_ieeeUnderflowModeRoundingEvidence_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hsqrt : fmt.finiteUnderflowRange (Real.sqrt x)) :
    fmt.ieeeUnderflowModeRoundingEvidence mode (Real.sqrt x)
      (fmt.finiteRoundToModeSqrt mode x) := by
  simpa [finiteRoundToModeSqrt] using
    fmt.finiteRoundToMode_ieeeUnderflowModeRoundingEvidence_of_finiteUnderflowRange
      (mode := mode) hsqrt
theorem finiteRoundToEvenSqrt_nearestRoundingToFinite
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.nearestRoundingToFinite (Real.sqrt x)
      (fmt.finiteRoundToEvenSqrt x) := by
  simpa [finiteRoundToEvenSqrt] using
    fmt.finiteRoundToEven_nearestRoundingToFinite (Real.sqrt x)
/-- The finite round-to-even square-root wrapper returns a finite
representable value. -/
theorem finiteRoundToEvenSqrt_finiteSystem
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteSystem (fmt.finiteRoundToEvenSqrt x) := by
  simpa [finiteRoundToEvenSqrt] using
    fmt.finiteRoundToEven_finiteSystem (Real.sqrt x)
/-- If the exact square-root result is finite representable, the finite
round-to-even square-root wrapper returns it exactly. -/
theorem finiteRoundToEvenSqrt_eq_exact_of_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsqrt : fmt.finiteSystem (Real.sqrt x)) :
    fmt.finiteRoundToEvenSqrt x = Real.sqrt x := by
  simpa [finiteRoundToEvenSqrt] using
    fmt.finiteRoundToEven_eq_self_of_finiteSystem hsqrt
theorem finiteRoundToEvenSqrt_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (_hx_nonneg : 0 ≤ x) (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        fmt.finiteRoundToEvenSqrt x = Real.sqrt x * (1 + δ) := by
  rcases
    fmt.finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange
      hsqrt with
    ⟨δ, _hround, hδ, hwit⟩
  exact ⟨δ, hδ, by simpa [finiteRoundToEvenSqrt, signedRelErrorWitness] using hwit⟩

end FloatingPointFormat

end

end NumStability
