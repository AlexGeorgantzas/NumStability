import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.FloatingPointArithmetic.Rounding
import NumStability.Analysis.FloatingPointArithmetic.DoubleRounding.ToyBinary

-- Analysis/DoubleRounding.lean
--
-- Concrete finite double-rounding example for Higham Chapter 2, §2.3 and
-- Problem 2.9.



namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Double Rounding

Higham Chapter 2, §2.3 notes that computing first in an extended format and
then rounding again to the destination format can differ from rounding directly
to the destination format.  This file records a small binary round-to-even
counterexample over finite normal values:

* the extended `t = 3` format rounds `21/16` to `5/4`;
* the destination `t = 2` format rounds that midpoint `5/4` to the even
  mantissa endpoint `1`;
* direct destination rounding of `21/16` gives `3/2`.

The example is intentionally finite-format only: it does not claim the full
IEEE double/64-bit-extended arithmetic trace requested in Problem 2.9.
-/




























































































































































































/-- The tiny `t = 2` destination format does not contain `-3/16`. -/
theorem binaryT2DoubleRounding_neg_three_sixteenths_not_finiteSystem :
    ¬ binaryT2DoubleRoundingDestinationFormat.finiteSystem (-3 / 16 : ℝ) := by
  intro hfin
  have hnonzero : (-3 / 16 : ℝ) ≠ 0 := by norm_num
  have hfloor :=
    binaryT2DoubleRoundingDestinationFormat.finiteSystem_ne_zero_abs_ge_minSubnormalMagnitude
      hfin hnonzero
  norm_num [binaryT2DoubleRoundingDestinationFormat, minSubnormalMagnitude,
    betaR] at hfloor

/-- The direct `t = 2` rounding error for `21/16` is not representable in the
destination finite system. -/
theorem binaryT2DoubleRounding_roundoff_error_not_finiteSystem :
    ¬ binaryT2DoubleRoundingDestinationFormat.finiteSystem
        ((21 / 16 : ℝ) -
          binaryT2DoubleRoundingDestinationFormat.finiteRoundToEven (21 / 16 : ℝ)) := by
  rw [binaryT2DoubleRounding_rounds_21_16_to_3_2]
  rw [show (21 / 16 : ℝ) - (3 / 2 : ℝ) = -3 / 16 by norm_num]
  exact binaryT2DoubleRounding_neg_three_sixteenths_not_finiteSystem

/-- The source value `21/16` lies inside the finite-normal source range of the
tiny `t = 2` destination format. -/
theorem binaryT2DoubleRounding_21_16_finiteNormalRange :
    binaryT2DoubleRoundingDestinationFormat.finiteNormalRange (21 / 16 : ℝ) := by
  rw [finiteNormalRange]
  have hxnonneg : 0 ≤ (21 / 16 : ℝ) := by norm_num
  rw [abs_of_nonneg hxnonneg]
  constructor
  · norm_num [binaryT2DoubleRoundingDestinationFormat, minNormalMagnitude,
      betaR]
  · have hmax :
        binaryT2DoubleRoundingDestinationFormat.maxFiniteMagnitude =
          (3 / 2 : ℝ) := by
      norm_num [binaryT2DoubleRoundingDestinationFormat, maxFiniteMagnitude,
        betaR]
    simpa [hmax] using (by norm_num : (21 / 16 : ℝ) ≤ 3 / 2)

/-- Finite-normal range and binary round-to-even alone do not imply that the
real roundoff error is finite representable.  The missing Chapter 4 FastTwoSum
dependency must use that the rounded source is the exact sum of finite binary
operands, not just an arbitrary in-range real. -/
theorem finiteNormalRange_not_enough_for_roundoff_error_finiteSystem :
    ∃ fmt : FloatingPointFormat, ∃ x : ℝ,
      fmt.beta = 2 ∧ fmt.finiteNormalRange x ∧
        ¬ fmt.finiteSystem (x - fmt.finiteRoundToEven x) := by
  refine ⟨binaryT2DoubleRoundingDestinationFormat, (21 / 16 : ℝ), ?_, ?_, ?_⟩
  · rfl
  · exact binaryT2DoubleRounding_21_16_finiteNormalRange
  · simpa using binaryT2DoubleRounding_roundoff_error_not_finiteSystem

/-! ## Higham Problem 2.9: `sqrt (1 - 2^-53)` -/



















































































































































































































































































































end FloatingPointFormat

end

end NumStability
