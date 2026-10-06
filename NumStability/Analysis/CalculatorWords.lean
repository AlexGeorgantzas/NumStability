-- Analysis/CalculatorWords.lean
--
-- Exact calculator upside-down digit words for Higham Chapter 1, Problem 1.6.

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.NormNum

namespace NumStability

/-!
# Calculator Upside-Down Words

Higham Problem 1.6 is recreational rather than a numerical-analysis theorem:
type several displayed numbers into a calculator, turn the display upside down,
and read the resulting words.  This file records the exact digit-to-glyph map
and the listed outputs.
-/

/-- Glyphs readable from calculator digits after turning the display upside
down. -/
inductive CalculatorGlyph where
  | O | I | E | H | S | G | L | B
  deriving DecidableEq, Repr

/-- Upside-down interpretation of a single calculator digit.  Both `6` and
`9` are read as `G`, matching the examples in Problem 1.6. -/
def invertedCalculatorDigit : Nat → Option CalculatorGlyph
  | 0 => some .O
  | 1 => some .I
  | 3 => some .E
  | 4 => some .H
  | 5 => some .S
  | 6 => some .G
  | 7 => some .L
  | 8 => some .B
  | 9 => some .G
  | _ => none

/-- Interpret a left-to-right calculator digit list after turning the display
upside down. -/
def calculatorInvertDigits : List Nat → Option (List CalculatorGlyph)
  | [] => some []
  | d :: ds => do
      let rest ← calculatorInvertDigits ds
      let g ← invertedCalculatorDigit d
      pure (rest ++ [g])

theorem problem_1_6_07734_hello :
    calculatorInvertDigits [0, 7, 7, 3, 4] =
      some [.H, .E, .L, .L, .O] := rfl

theorem problem_1_6_38079_globe :
    calculatorInvertDigits [3, 8, 0, 7, 9] =
      some [.G, .L, .O, .B, .E] := rfl

theorem problem_1_6_318808_bobbie :
    calculatorInvertDigits [3, 1, 8, 8, 0, 8] =
      some [.B, .O, .B, .B, .I, .E] := rfl

theorem problem_1_6_35007_loose :
    calculatorInvertDigits [3, 5, 0, 0, 7] =
      some [.L, .O, .O, .S, .E] := rfl

/-- The mantissa digits of `57738.57734 * 10^40` read as "HELLS BELLS" after
the display is inverted. -/
theorem problem_1_6_5773857734_hells_bells :
    calculatorInvertDigits [5, 7, 7, 3, 8, 5, 7, 7, 3, 4] =
      some [.H, .E, .L, .L, .S, .B, .E, .L, .L, .S] := rfl

theorem problem_1_6_3331_ieee :
    calculatorInvertDigits [3, 3, 3, 1] =
      some [.I, .E, .E, .E] := rfl

theorem problem_1_6_5607_logs :
    calculatorInvertDigits [5, 6, 0, 7] =
      some [.L, .O, .G, .S] := rfl

theorem problem_1_6_5607_sq :
    (5607 : ℕ) ^ 2 = 31438449 := by
  norm_num

theorem problem_1_6_real_sqrt_31438449_eq_5607 :
    Real.sqrt (31438449 : ℝ) = 5607 := by
  rw [show (31438449 : ℝ) = (5607 : ℝ) ^ 2 by norm_num]
  rw [Real.sqrt_sq_eq_abs]
  norm_num

end NumStability
