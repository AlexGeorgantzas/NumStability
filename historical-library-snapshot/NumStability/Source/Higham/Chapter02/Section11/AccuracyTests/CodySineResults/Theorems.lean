-- NumStability/Source/Higham/Chapter02/Section11/AccuracyTests/CodySineResults/Theorems.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Split component of a mixed/multi-destination owner.
-- Historical owner: `NumStability.Analysis.AccuracyTests`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.Rounding
import NumStability.Source.Higham.Chapter01.Problem05.CompensatedLogarithm.Basic
import NumStability.Source.Higham.Chapter01.Section11.Accumulation.Basic
import NumStability.Source.Higham.Chapter02.Section11.AccuracyTests.Basic
import NumStability.Analysis.Approximation.SineTaylor.OddDegreeFiveError.Theorems

/-!
# Theorems

Relocated from `NumStability.Analysis.AccuracyTests` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# AccuracyTests (compatibility module)

Historical path, retained so existing imports of `NumStability.Analysis.AccuracyTests`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

noncomputable section

namespace NumStability


theorem codySineReducedArgument_sineTaylorOdd5_abs_error_lt_one_e20 :
    |Real.sin codySineReducedArgument - sineTaylorOdd5 codySineReducedArgument| <
      (1 : ℝ) / 10 ^ 20 := by
  have hle := sineTaylorOdd5_abs_error_le_next codySineReducedArgument
    (le_of_lt codySineReducedArgument_pos)
    (le_trans (le_of_lt codySineReducedArgument_lt_one_hundredth)
      (by norm_num : (1 / 100 : ℝ) ≤ 1))
  have hr_nonneg : 0 ≤ codySineReducedArgument := le_of_lt codySineReducedArgument_pos
  have hr_le : codySineReducedArgument ≤ (1 / 100 : ℝ) :=
    le_of_lt codySineReducedArgument_lt_one_hundredth
  have hpow : codySineReducedArgument ^ 11 ≤ (1 / 100 : ℝ) ^ 11 :=
    pow_le_pow_left₀ hr_nonneg hr_le 11
  have hrem :
      codySineReducedArgument ^ 11 / (Nat.factorial 11 : ℝ) <
        (1 : ℝ) / 10 ^ 20 := by
    calc
      codySineReducedArgument ^ 11 / (Nat.factorial 11 : ℝ)
          ≤ (1 / 100 : ℝ) ^ 11 / (Nat.factorial 11 : ℝ) := by
              exact div_le_div_of_nonneg_right hpow (by positivity)
      _ < (1 : ℝ) / 10 ^ 20 := by norm_num
  exact lt_of_le_of_lt hle hrem


theorem codySineTestExact_sineTaylorOdd5_abs_error_lt_one_e20 :
    |codySineTestExact + sineTaylorOdd5 codySineReducedArgument| <
      (1 : ℝ) / 10 ^ 20 := by
  have h := codySineReducedArgument_sineTaylorOdd5_abs_error_lt_one_e20
  rw [codySineTestExact_eq_neg_sin_reducedArgument]
  have halg :
      -Real.sin codySineReducedArgument + sineTaylorOdd5 codySineReducedArgument =
        -(Real.sin codySineReducedArgument - sineTaylorOdd5 codySineReducedArgument) := by
    ring
  rw [halg, abs_neg]
  exact h


private def codySineReducedArgumentLowerD20 : ℝ :=
  22 - 7 * (314159265358979323847 : ℝ) / 10 ^ 20


private def codySineReducedArgumentUpperD20 : ℝ :=
  22 - 7 * (314159265358979323846 : ℝ) / 10 ^ 20


private theorem codySineReducedArgumentLowerD20_le :
    codySineReducedArgumentLowerD20 ≤ codySineReducedArgument := by
  unfold codySineReducedArgumentLowerD20 codySineReducedArgument
  nlinarith [Real.pi_lt_d20]


private theorem codySineReducedArgument_leUpperD20 :
    codySineReducedArgument ≤ codySineReducedArgumentUpperD20 := by
  unfold codySineReducedArgumentUpperD20 codySineReducedArgument
  nlinarith [Real.pi_gt_d20]


theorem codySineTaylorOdd5_displayedMagnitude_abs_error_lt_41e21 :
    |sineTaylorOdd5 codySineReducedArgument - codySineDisplayedTableMagnitude17| <
      (41 : ℝ) / 10 ^ 21 := by
  let lo : ℝ := codySineReducedArgumentLowerD20
  let hi : ℝ := codySineReducedArgumentUpperD20
  let r : ℝ := codySineReducedArgument
  let d : ℝ := codySineDisplayedTableMagnitude17
  have hlo : lo ≤ r := by
    simpa [lo, r] using codySineReducedArgumentLowerD20_le
  have hhi : r ≤ hi := by
    simpa [hi, r] using codySineReducedArgument_leUpperD20
  have hlo_nonneg : 0 ≤ lo := by
    norm_num [lo, codySineReducedArgumentLowerD20]
  have hr_nonneg : 0 ≤ r := by
    simpa [r] using le_of_lt codySineReducedArgument_pos
  have hhi_nonneg : 0 ≤ hi := by
    norm_num [hi, codySineReducedArgumentUpperD20]
  have h3lo : lo ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hlo_nonneg hlo 3
  have h5hi : r ^ 5 ≤ hi ^ 5 := pow_le_pow_left₀ hr_nonneg hhi 5
  have h7lo : lo ^ 7 ≤ r ^ 7 := pow_le_pow_left₀ hlo_nonneg hlo 7
  have h9hi : r ^ 9 ≤ hi ^ 9 := pow_le_pow_left₀ hr_nonneg hhi 9
  have h3hi : r ^ 3 ≤ hi ^ 3 := pow_le_pow_left₀ hr_nonneg hhi 3
  have h5lo : lo ^ 5 ≤ r ^ 5 := pow_le_pow_left₀ hlo_nonneg hlo 5
  have h7hi : r ^ 7 ≤ hi ^ 7 := pow_le_pow_left₀ hr_nonneg hhi 7
  have h9lo : lo ^ 9 ≤ r ^ 9 := pow_le_pow_left₀ hlo_nonneg hlo 9
  have hupper :
      sineTaylorOdd5 r - d ≤
        hi - lo ^ 3 / 6 + hi ^ 5 / 120 - lo ^ 7 / 5040 + hi ^ 9 / 362880 - d := by
    rw [sineTaylorOdd5_eq]
    nlinarith
  have hlower :
      lo - hi ^ 3 / 6 + lo ^ 5 / 120 - hi ^ 7 / 5040 + lo ^ 9 / 362880 - d ≤
        sineTaylorOdd5 r - d := by
    rw [sineTaylorOdd5_eq]
    nlinarith
  have hupper_num :
      hi - lo ^ 3 / 6 + hi ^ 5 / 120 - lo ^ 7 / 5040 + hi ^ 9 / 362880 - d <
        (41 : ℝ) / 10 ^ 21 := by
    norm_num [lo, hi, d, codySineReducedArgumentLowerD20,
      codySineReducedArgumentUpperD20, codySineDisplayedTableMagnitude17]
  have hlower_num :
      -((41 : ℝ) / 10 ^ 21) <
        lo - hi ^ 3 / 6 + lo ^ 5 / 120 - hi ^ 7 / 5040 + lo ^ 9 / 362880 - d := by
    norm_num [lo, hi, d, codySineReducedArgumentLowerD20,
      codySineReducedArgumentUpperD20, codySineDisplayedTableMagnitude17]
  rw [abs_lt]
  constructor
  · exact lt_of_lt_of_le hlower_num hlower
  · exact lt_of_le_of_lt hupper hupper_num


theorem codySineTestExact_displayedTableDecimal17_abs_error_lt_half_last_place :
    |codySineTestExact - codySineDisplayedTableDecimal17| <
      (1 / 2 : ℝ) / 10 ^ 19 := by
  have hrem_le := sineTaylorOdd5_abs_error_le_next codySineReducedArgument
    (le_of_lt codySineReducedArgument_pos)
    (le_trans (le_of_lt codySineReducedArgument_lt_one_hundredth)
      (by norm_num : (1 / 100 : ℝ) ≤ 1))
  have hr_nonneg : 0 ≤ codySineReducedArgument := le_of_lt codySineReducedArgument_pos
  have hr_le : codySineReducedArgument ≤ (1 / 100 : ℝ) :=
    le_of_lt codySineReducedArgument_lt_one_hundredth
  have hpow : codySineReducedArgument ^ 11 ≤ (1 / 100 : ℝ) ^ 11 :=
    pow_le_pow_left₀ hr_nonneg hr_le 11
  have hrem :
      |Real.sin codySineReducedArgument - sineTaylorOdd5 codySineReducedArgument| <
        (1 : ℝ) / 10 ^ 21 := by
    refine lt_of_le_of_lt hrem_le ?_
    calc
      codySineReducedArgument ^ 11 / (Nat.factorial 11 : ℝ)
          ≤ (1 / 100 : ℝ) ^ 11 / (Nat.factorial 11 : ℝ) := by
              exact div_le_div_of_nonneg_right hpow (by positivity)
      _ < (1 : ℝ) / 10 ^ 21 := by norm_num
  have hpoly := codySineTaylorOdd5_displayedMagnitude_abs_error_lt_41e21
  have htarget :
      |Real.sin codySineReducedArgument - codySineDisplayedTableMagnitude17| <
        (1 / 2 : ℝ) / 10 ^ 19 := by
    calc
      |Real.sin codySineReducedArgument - codySineDisplayedTableMagnitude17|
          =
            |(Real.sin codySineReducedArgument -
                sineTaylorOdd5 codySineReducedArgument) +
              (sineTaylorOdd5 codySineReducedArgument -
                codySineDisplayedTableMagnitude17)| := by
              ring_nf
      _ ≤ |Real.sin codySineReducedArgument - sineTaylorOdd5 codySineReducedArgument| +
            |sineTaylorOdd5 codySineReducedArgument -
              codySineDisplayedTableMagnitude17| := abs_add_le _ _
      _ < (1 : ℝ) / 10 ^ 21 + (41 : ℝ) / 10 ^ 21 :=
            add_lt_add hrem hpoly
      _ < (1 / 2 : ℝ) / 10 ^ 19 := by norm_num
  rw [codySineTestExact_eq_neg_sin_reducedArgument, codySineDisplayedTableDecimal17]
  have halg :
      -Real.sin codySineReducedArgument - -codySineDisplayedTableMagnitude17 =
        -(Real.sin codySineReducedArgument - codySineDisplayedTableMagnitude17) := by
    ring
  rw [halg, abs_neg]
  exact htarget

end NumStability
