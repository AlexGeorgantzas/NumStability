import NumStability.Analysis.FloatingPointArithmetic.ExactSubtraction
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.MidpointRounding.DecimalTieExamples
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.FloatingPointArithmetic.RoundToEvenLocalError
import NumStability.Analysis.Nonassociativity
import NumStability.FloatingPoint.Model

-- Analysis/Midpoint.lean
--
-- Concrete midpoint-rounding examples for Higham Chapter 2, Problem 2.8.



namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Midpoint Rounding

Higham Problem 2.8 asks for a base-10 violation of
`a < fl((a + b)/2) < b` with floating-point endpoints `a < b`.  The first
theorem below gives a minimal finite round-to-even witness in the existing
one-digit decimal format: `a = 1`, `b = 2`, and the exact midpoint `3/2` is a
tie whose left mantissa is odd, so round-to-even selects `2`.

The later counterexample audits the problem's second sentence.  It shows that
exact subtraction and exact division by `2` are still not enough for the naive
finite round-to-even operation-sequence interpretation of `fl(a + (b-a)/2)`;
the source guard-digit claim is therefore separated below into an exact-operation
model and corrected finite-selector side conditions.
-/








































































































































































































































































/-- The same guarded-sequence counterexample fails exactly the final-midpoint
representability hypothesis used by the corrected finite-selector theorem
below: `2-1` and `(2-1)/2` are finite, but `1+(2-1)/2 = 3/2` is not. -/
theorem problem2_8_guarded_sequence_counterexample_missing_midpoint_finiteSystem :
    decimalOneDigitThreeExponentFormat.finiteSystem ((2 : ℝ) - 1) ∧
      decimalOneDigitThreeExponentFormat.finiteSystem (((2 : ℝ) - 1) / 2) ∧
      ¬ decimalOneDigitThreeExponentFormat.finiteSystem
        ((1 : ℝ) + ((2 : ℝ) - 1) / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num
    exact decimalOneDigitThreeExponentFormat_finiteSystem_one
  · norm_num
    exact decimalOneDigitThreeExponentFormat_finiteSystem_one_half
  · have hmid : ((1 : ℝ) + ((2 : ℝ) - 1) / 2) = (3 / 2 : ℝ) := by
      norm_num
    rw [hmid]
    exact decimalOneDigitThreeExponentFormat_three_halves_not_finiteSystem

/-- The exact guarded midpoint expression is strictly between the endpoints.
This is the real-arithmetic core behind Problem 2.8's second sentence; the
finite-operation theorems below state which rounded paths actually compute this
exact midpoint. -/
theorem problem2_8_exact_guarded_midpoint_strict_between
    {a b : ℝ} (hab : a < b) :
    a < a + (b - a) / 2 ∧ a + (b - a) / 2 < b := by
  constructor <;> linarith

/-- Source-shaped exact-operation model for Problem 2.8's guard-digit midpoint
path.  If subtraction, halving, and the final addition return the corresponding
exact real intermediates, then the operation sequence computes the exact
guarded midpoint. -/
theorem problem2_8_guarded_exact_operation_sequence_eq_exact_midpoint
    {subOp divOp addOp : ℝ → ℝ → ℝ} {a b : ℝ}
    (hsub : subOp b a = b - a)
    (hdiv : divOp (b - a) 2 = (b - a) / 2)
    (hadd : addOp a ((b - a) / 2) = a + (b - a) / 2) :
    addOp a (divOp (subOp b a) 2) = a + (b - a) / 2 := by
  rw [hsub, hdiv, hadd]

/-- Exact-operation version of Problem 2.8's guard-digit midpoint sentence.
This theorem captures the arbitrary-base real-arithmetic conclusion once the
guarded operation/evaluation model supplies exactness of the three steps. -/
theorem problem2_8_guarded_exact_operation_sequence_strict_between
    {subOp divOp addOp : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hsub : subOp b a = b - a)
    (hdiv : divOp (b - a) 2 = (b - a) / 2)
    (hadd : addOp a ((b - a) / 2) = a + (b - a) / 2) :
    a < addOp a (divOp (subOp b a) 2) ∧
      addOp a (divOp (subOp b a) 2) < b := by
  rw [problem2_8_guarded_exact_operation_sequence_eq_exact_midpoint hsub hdiv hadd]
  exact problem2_8_exact_guarded_midpoint_strict_between hab

/-- Under the three exact-step representability hypotheses, the finite
round-to-even operation path for `a + (b-a)/2` equals the exact guarded
midpoint. -/
theorem problem2_8_guarded_sequence_eq_exact_midpoint_of_finite_midpoint_steps
    (fmt : FloatingPointFormat) {a b : ℝ}
    (hsubfin : fmt.finiteSystem (b - a))
    (hhalffin : fmt.finiteSystem ((b - a) / 2))
    (hmidfin : fmt.finiteSystem (a + (b - a) / 2)) :
    fmt.finiteRoundToEvenOp BasicOp.add a
        (fmt.finiteRoundToEvenOp BasicOp.div
          (fmt.finiteRoundToEvenOp BasicOp.sub b a) 2) =
      a + (b - a) / 2 := by
  have hsubfin' : fmt.finiteSystem (BasicOp.exact BasicOp.sub b a) := by
    simpa [BasicOp.exact] using hsubfin
  have hsub :=
    fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := b) (y := a) hsubfin'
  change fmt.finiteRoundToEvenOp BasicOp.sub b a = b - a at hsub
  have hhalffin' :
      fmt.finiteSystem (BasicOp.exact BasicOp.div ((b - a) : ℝ) 2) := by
    simpa [BasicOp.exact] using hhalffin
  have hhalf :=
    fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.div) (x := ((b - a) : ℝ)) (y := (2 : ℝ)) hhalffin'
  change fmt.finiteRoundToEvenOp BasicOp.div (b - a) 2 = (b - a) / 2 at hhalf
  have hmidfin' :
      fmt.finiteSystem (BasicOp.exact BasicOp.add a (((b - a) / 2) : ℝ)) := by
    simpa [BasicOp.exact] using hmidfin
  have hmid :=
    fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add) (x := a) (y := (((b - a) / 2) : ℝ)) hmidfin'
  change fmt.finiteRoundToEvenOp BasicOp.add a ((b - a) / 2) =
    a + (b - a) / 2 at hmid
  rw [hsub, hhalf, hmid]

/-- A corrected finite-selector version of Problem 2.8's guard-digit midpoint
sentence.  Exact subtraction and exact halving are not enough by themselves
(see `problem2_8_finiteRoundToEven_guarded_sequence_counterexample`), but if
the exact final midpoint is also representable, the rounded operation sequence
returns that midpoint and is strictly between the endpoints. -/
theorem problem2_8_guarded_sequence_strict_between_of_finite_midpoint_steps
    (fmt : FloatingPointFormat) {a b : ℝ} (hab : a < b)
    (hsubfin : fmt.finiteSystem (b - a))
    (hhalffin : fmt.finiteSystem ((b - a) / 2))
    (hmidfin : fmt.finiteSystem (a + (b - a) / 2)) :
    a <
        fmt.finiteRoundToEvenOp BasicOp.add a
          (fmt.finiteRoundToEvenOp BasicOp.div
            (fmt.finiteRoundToEvenOp BasicOp.sub b a) 2) ∧
      fmt.finiteRoundToEvenOp BasicOp.add a
          (fmt.finiteRoundToEvenOp BasicOp.div
            (fmt.finiteRoundToEvenOp BasicOp.sub b a) 2) <
        b := by
  rw [fmt.problem2_8_guarded_sequence_eq_exact_midpoint_of_finite_midpoint_steps
    hsubfin hhalffin hmidfin]
  exact problem2_8_exact_guarded_midpoint_strict_between hab

/-- Sterbenz-specialized corrected midpoint theorem for Problem 2.8.  The
exact subtraction step is discharged by the finite round-to-even Sterbenz
subtraction theorem, leaving only the halved difference and final midpoint
representability conditions as explicit operation-path hypotheses. -/
theorem problem2_8_guarded_sequence_strict_between_of_sterbenz_subtraction
    (fmt : FloatingPointFormat) {a b : ℝ} (hab : a < b)
    (ha : fmt.finiteSystem a)
    (hb : fmt.finiteSystem b)
    (hsterbenz : fmt.sterbenzRatioCondition b a)
    (hhalffin : fmt.finiteSystem ((b - a) / 2))
    (hmidfin : fmt.finiteSystem (a + (b - a) / 2)) :
    a <
        fmt.finiteRoundToEvenOp BasicOp.add a
          (fmt.finiteRoundToEvenOp BasicOp.div
            (fmt.finiteRoundToEvenOp BasicOp.sub b a) 2) ∧
      fmt.finiteRoundToEvenOp BasicOp.add a
          (fmt.finiteRoundToEvenOp BasicOp.div
            (fmt.finiteRoundToEvenOp BasicOp.sub b a) 2) <
        b := by
  have hsubfin : fmt.finiteSystem (b - a) :=
    fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
      hb ha hsterbenz
  exact fmt.problem2_8_guarded_sequence_strict_between_of_finite_midpoint_steps
    hab hsubfin hhalffin hmidfin

/-- Higham Problem 2.8's first requested phenomenon: in base-10 arithmetic,
`a < fl((a+b)/2) < b` can fail even when `a` and `b` are floating-point
numbers and `a < b`. -/
theorem problem2_8_decimal_midpoint_strict_between_violated :
    decimalOneDigitTwoExponentFormat.finiteSystem (1 : ℝ) ∧
      decimalOneDigitTwoExponentFormat.finiteSystem (2 : ℝ) ∧
      (1 : ℝ) < 2 ∧
      ¬ ((1 : ℝ) <
          decimalOneDigitTwoExponentFormat.finiteRoundToEven (((1 : ℝ) + 2) / 2) ∧
        decimalOneDigitTwoExponentFormat.finiteRoundToEven (((1 : ℝ) + 2) / 2) <
          (2 : ℝ)) := by
  refine ⟨decimalOneDigitTwoExponentFormat_finiteSystem_one,
    decimalOneDigitTwoExponentFormat_finiteSystem_two, by norm_num, ?_⟩
  rw [decimalOneDigitTwoExponent_midpoint_one_two_rounds_to_two]
  norm_num

end FloatingPointFormat

end

end NumStability
