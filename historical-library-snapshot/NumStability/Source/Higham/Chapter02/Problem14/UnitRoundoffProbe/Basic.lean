import Mathlib.Data.Nat.Factorization.Basic
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError

/-!
# Chapter02 Problem14 UnitRoundoffProbe Basic

Canonical destination for material split out of
`NumStability.Analysis.Problem2_14` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

namespace FloatingPointFormat

/-- Absolute-value form of Kahan's finite IEEE-double Problem 2.14 probe. -/
def problem2_14_ieeeDoubleKahanEstimate : ℝ :=
  |ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub
      (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (3 : ℝ)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub
          (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (4 : ℝ) 3) 1)) 1|

/-- Absolute-value form of Kahan's finite IEEE-single Problem 2.14 probe. -/
def problem2_14_ieeeSingleKahanEstimate : ℝ :=
  |ieeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
      (ieeeSingleFormat.finiteRoundToEvenOp BasicOp.mul (3 : ℝ)
        (ieeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
          (ieeeSingleFormat.finiteRoundToEvenOp BasicOp.div (4 : ℝ) 3) 1)) 1|

end FloatingPointFormat
end NumStability

end
