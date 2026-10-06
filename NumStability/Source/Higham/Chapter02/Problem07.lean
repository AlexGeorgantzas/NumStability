import NumStability.Analysis.Midpoint
import NumStability.FloatingPoint.OperationLaws

namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Higham Chapter 2, Problem 2.7

Source-facing aliases for the generic finite round-to-even operation laws,
together with the finite counterexamples to associativity and the strict
midpoint claim. Full IEEE special-value and exception semantics remain outside
the finite real-valued selector used here.
-/

/-- Problem 2.7, statement 1: finite rounded addition commutes. -/
theorem problem2_7_statement1_add_comm
    (fmt : FloatingPointFormat) (a b : ℝ) :
    fmt.finiteRoundToEvenOp BasicOp.add a b =
      fmt.finiteRoundToEvenOp BasicOp.add b a :=
  finiteRoundToEvenOp_add_comm fmt a b

/-- Problem 2.7, statement 1: finite rounded multiplication commutes. -/
theorem problem2_7_statement1_mul_comm
    (fmt : FloatingPointFormat) (a b : ℝ) :
    fmt.finiteRoundToEvenOp BasicOp.mul a b =
      fmt.finiteRoundToEvenOp BasicOp.mul b a :=
  finiteRoundToEvenOp_mul_comm fmt a b

/-- Problem 2.7, statement 2, on the exact-representable subtraction branch. -/
theorem problem2_7_statement2_sub_sign_symmetry_of_exact_finiteSystem
    {fmt : FloatingPointFormat} {a b : ℝ}
    (hab : fmt.finiteSystem (a - b)) :
    fmt.finiteRoundToEvenOp BasicOp.sub b a =
      -fmt.finiteRoundToEvenOp BasicOp.sub a b :=
  finiteRoundToEvenOp_sub_sign_symmetry_of_exact_finiteSystem hab

/-- Problem 2.7, statement 2, outside the finite-normal range. -/
theorem problem2_7_statement2_sub_sign_symmetry_of_not_finiteNormalRange
    {fmt : FloatingPointFormat} {a b : ℝ}
    (hab : ¬ fmt.finiteNormalRange (a - b)) :
    fmt.finiteRoundToEvenOp BasicOp.sub b a =
      -fmt.finiteRoundToEvenOp BasicOp.sub a b :=
  finiteRoundToEvenOp_sub_sign_symmetry_of_not_finiteNormalRange hab

/-- Problem 2.7, statement 2, for binary-style round-to-even formats. -/
theorem problem2_7_statement2_sub_sign_symmetry
    {fmt : FloatingPointFormat}
    (hbeta : evenMantissa fmt.beta) (ht : 1 < fmt.t)
    (a b : ℝ) :
    fmt.finiteRoundToEvenOp BasicOp.sub b a =
      -fmt.finiteRoundToEvenOp BasicOp.sub a b :=
  finiteRoundToEvenOp_sub_sign_symmetry hbeta ht a b

/-- Problem 2.7, statement 3: `fl(a + a) = fl(2 * a)`. -/
theorem problem2_7_statement3_add_self_eq_mul_two
    (fmt : FloatingPointFormat) (a : ℝ) :
    fmt.finiteRoundToEvenOp BasicOp.add a a =
      fmt.finiteRoundToEvenOp BasicOp.mul 2 a :=
  finiteRoundToEvenOp_add_self_eq_mul_two fmt a

/-- Problem 2.7, statement 4: `fl((1 / 2) * a) = fl(a / 2)`. -/
theorem problem2_7_statement4_half_mul_eq_div_two
    (fmt : FloatingPointFormat) (a : ℝ) :
    fmt.finiteRoundToEvenOp BasicOp.mul (1 / 2 : ℝ) a =
      fmt.finiteRoundToEvenOp BasicOp.div a 2 :=
  finiteRoundToEvenOp_half_mul_eq_div_two fmt a

/-- Problem 2.7, statement 5 is false for finite round-to-even addition. -/
theorem problem2_7_statement5_add_associativity_false :
    ¬ (∀ a b c : ℝ,
      decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp BasicOp.add
          (decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
            BasicOp.add a b) c =
        decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp BasicOp.add
          a
          (decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
            BasicOp.add b c)) := by
  intro h
  exact
    decimalOneDigitTwoExponent_roundToEven_add_nonassociative
      (h (10 : ℝ) 4 (-4))

/-- Problem 2.7, statement 6 is false for finite midpoint rounding. -/
theorem problem2_7_statement6_midpoint_strict_between_false :
    ¬ (∀ a b : ℝ,
      decimalOneDigitTwoExponentFormat.finiteSystem a →
        decimalOneDigitTwoExponentFormat.finiteSystem b →
          a < b →
            a <
              decimalOneDigitTwoExponentFormat.finiteRoundToEven
                ((a + b) / 2) ∧
              decimalOneDigitTwoExponentFormat.finiteRoundToEven
                ((a + b) / 2) < b) := by
  intro h
  rcases problem2_8_decimal_midpoint_strict_between_violated with
    ⟨ha, hb, hab, hnot⟩
  exact hnot (h (1 : ℝ) 2 ha hb hab)

end FloatingPointFormat

end

end NumStability
