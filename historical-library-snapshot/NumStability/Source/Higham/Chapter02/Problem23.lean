/-
SPDX-License-Identifier: MIT
-/

import NumStability.Analysis.Heron

namespace NumStability

noncomputable section

/-!
# Higham Chapter 2, Problem 2.23

Problem 2.23 asks for the accuracy of Kahan's parenthesized Heron formula
(2.7) when subtraction has a guard digit. The main Heron module already proves
the operation trace; this file exposes the problem-numbered theorem surface.

The declaration names retain their historical `problem2_22` spelling for API
compatibility with the repository's former one-place numbering offset.
-/

/-- The guard-digit/Sterbenz step used by Kahan's Heron formula: under the
ordered-side and triangle assumptions, the parenthesized `a-b` subtraction is
exact for finite round-to-even subtraction. -/
theorem problem2_22_guard_digit_a_sub_b_exact
    {fmt : FloatingPointFormat} {a b c : ℝ}
    (ha : fmt.finiteSystem a)
    (hb : fmt.finiteSystem b)
    (hside : kahanOrderedTriangleSides a b c) :
    finiteKahanHeronAB fmt a b = a - b :=
  finiteKahanHeronAB_eq_exact_of_kahanOrderedTriangleSides ha hb hside

/-- Problem 2.23 theorem surface: with the guard-digit exact `a-b` step and
finite-normal side conditions for the remaining rounded operations, Kahan's
parenthesized Heron formula computes the area with relative error bounded by
`(1 + gamma_9) * (1 + u)^2 - 1` relative to the exact Kahan expression. -/
theorem problem2_22_kahanHeronArea_relError_le_gamma9_unitRoundoff
    {fmt : FloatingPointFormat} {a b c : ℝ}
    (ha : fmt.finiteSystem a)
    (hb : fmt.finiteSystem b)
    (hside : kahanOrderedTriangleSides a b c)
    (hbc : fmt.finiteNormalRange (b - c))
    (hbpc : fmt.finiteNormalRange (b + c))
    (hf1 : fmt.finiteNormalRange (a + finiteKahanHeronBplusC fmt b c))
    (hf2 : fmt.finiteNormalRange (c - (a - b)))
    (hf3 : fmt.finiteNormalRange (c + (a - b)))
    (hf4 : fmt.finiteNormalRange (a + finiteKahanHeronBC fmt b c))
    (hp12 : fmt.finiteNormalRange
      (finiteKahanHeronFactor1 fmt a b c * finiteKahanHeronFactor2 fmt a b c))
    (hp123 : fmt.finiteNormalRange
      (finiteKahanHeronProduct12 fmt a b c * finiteKahanHeronFactor3 fmt a b c))
    (hr : fmt.finiteNormalRange
      (finiteKahanHeronProduct123 fmt a b c * finiteKahanHeronFactor4 fmt a b c))
    (hr_nonneg : 0 ≤ finiteKahanHeronRadicand fmt a b c)
    (hsqrt : fmt.finiteNormalRange
      (Real.sqrt (finiteKahanHeronRadicand fmt a b c)))
    (harea : fmt.finiteNormalRange (finiteKahanHeronSqrt fmt a b c / 4))
    (hγ : gammaValid (finiteFormatUnitRoundoffModel fmt) 18) :
    relError (finiteKahanHeronArea fmt a b c) (kahanHeronArea a b c) ≤
      (1 + gamma (finiteFormatUnitRoundoffModel fmt) 9) *
        (1 + fmt.unitRoundoff) ^ 2 - 1 :=
  finiteKahanHeronArea_relError_le_gamma9_unitRoundoff_of_finiteNormalRange
    ha hb hside hbc hbpc hf1 hf2 hf3 hf4 hp12 hp123 hr
    hr_nonneg hsqrt harea hγ

end

end NumStability
