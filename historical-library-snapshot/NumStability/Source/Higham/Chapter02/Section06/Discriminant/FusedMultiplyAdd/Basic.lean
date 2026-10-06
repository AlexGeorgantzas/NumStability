
import NumStability.FloatingPoint.FusedMultiplyAdd.Core

/-!
# Chapter02 Section06 Discriminant FusedMultiplyAdd Basic

Canonical destination for material split out of
`NumStability.Analysis.HighamChapter2FmaDiscriminant` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

/-- The binary32 input `1 + 2^-23`. -/
def higham2FmaDiscriminantInput : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8388609 (1 : ℤ)

/-- The binary32 value `1 + 2^-22`, immediately below the exact input square. -/
def higham2FmaDiscriminantRoundedSquare : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8388610 (1 : ℤ)

/-- The next binary32 value above `higham2FmaDiscriminantRoundedSquare`. -/
def higham2FmaDiscriminantSquareNext : ℝ :=
  FloatingPointFormat.ieeeSingleFormat.normalizedValue false 8388611 (1 : ℤ)

theorem higham2FmaDiscriminantInput_value :
    higham2FmaDiscriminantInput =
      (8388609 : ℝ) * (2 : ℝ) ^ (-23 : ℤ) := by
  norm_num [higham2FmaDiscriminantInput,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR, zpow_neg]

theorem higham2FmaDiscriminantRoundedSquare_value :
    higham2FmaDiscriminantRoundedSquare =
      (8388610 : ℝ) * (2 : ℝ) ^ (-23 : ℤ) := by
  norm_num [higham2FmaDiscriminantRoundedSquare,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR, zpow_neg]

theorem higham2FmaDiscriminantSquareNext_value :
    higham2FmaDiscriminantSquareNext =
      (8388611 : ℝ) * (2 : ℝ) ^ (-23 : ℤ) := by
  norm_num [higham2FmaDiscriminantSquareNext,
    FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.normalizedValue,
    FloatingPointFormat.signValue,
    FloatingPointFormat.betaR, zpow_neg]

end NumStability

end
