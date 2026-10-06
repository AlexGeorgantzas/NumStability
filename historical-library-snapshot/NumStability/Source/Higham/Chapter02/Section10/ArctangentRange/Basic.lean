import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results

/-!
# Chapter02 Section10 ArctangentRange Basic

Canonical destination for material split out of
`NumStability.Analysis.HighamChapter2ElementaryFunctions` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Set MeasureTheory
open scoped Interval

noncomputable section

namespace NumStability

/-- The IEEE-single value immediately below the exact `arctan (2^30)`. -/
def higham2ArctanSingleLower : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 13176794 (1 : ℤ)

/-- The IEEE-single value immediately above the exact `arctan (2^30)`. -/
def higham2ArctanSingleUpper : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 13176795 (1 : ℤ)

theorem higham2ArctanSingleLower_value :
    higham2ArctanSingleLower =
      (13176794 : ℝ) * (2 : ℝ) ^ (-23 : ℤ) := by
  norm_num [higham2ArctanSingleLower,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR, zpow_neg]

theorem higham2ArctanSingleUpper_value :
    higham2ArctanSingleUpper =
      (13176795 : ℝ) * (2 : ℝ) ^ (-23 : ℤ) := by
  norm_num [higham2ArctanSingleUpper,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR, zpow_neg]

theorem higham2ArctanSingleUpper_gt_pi_div_two :
    Real.pi / 2 < higham2ArctanSingleUpper := by
  rw [higham2ArctanSingleUpper_value]
  nlinarith [Real.pi_lt_d20]

end NumStability

end
