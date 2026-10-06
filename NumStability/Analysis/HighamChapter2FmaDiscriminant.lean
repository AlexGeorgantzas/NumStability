import NumStability.Analysis.FusedMultiplyAdd

namespace NumStability

noncomputable section

/-!
# Higham Chapter 2: an FMA discriminant sign counterexample

Section 2.6 contrasts separate correctly rounded products with an FMA
evaluation of `fl(b^2) - a*c`.  The former preserves nonnegativity when
`b^2 >= a*c`, whereas the latter can be negative because the FMA sees the
unrounded second product.  This file supplies a concrete IEEE-single trace.
-/

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

private theorem higham2FmaDiscriminantInput_normalizedSystem :
    FloatingPointFormat.ieeeSingleFormat.normalizedSystem
      higham2FmaDiscriminantInput := by
  refine ⟨false, 8388609, (1 : ℤ), ?_, ?_, rfl⟩
  · norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]

private theorem higham2FmaDiscriminantRoundedSquare_normalizedSystem :
    FloatingPointFormat.ieeeSingleFormat.normalizedSystem
      higham2FmaDiscriminantRoundedSquare := by
  refine ⟨false, 8388610, (1 : ℤ), ?_, ?_, rfl⟩
  · norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]

private theorem higham2FmaDiscriminantSquareNext_normalizedSystem :
    FloatingPointFormat.ieeeSingleFormat.normalizedSystem
      higham2FmaDiscriminantSquareNext := by
  refine ⟨false, 8388611, (1 : ℤ), ?_, ?_, rfl⟩
  · norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]

private theorem higham2FmaDiscriminantSquare_strict_between :
    higham2FmaDiscriminantRoundedSquare <
        higham2FmaDiscriminantInput * higham2FmaDiscriminantInput ∧
      higham2FmaDiscriminantInput * higham2FmaDiscriminantInput <
        higham2FmaDiscriminantSquareNext := by
  rw [higham2FmaDiscriminantInput_value,
    higham2FmaDiscriminantRoundedSquare_value,
    higham2FmaDiscriminantSquareNext_value]
  norm_num [zpow_neg]

private theorem higham2FmaDiscriminantSquare_left_closer :
    |higham2FmaDiscriminantInput * higham2FmaDiscriminantInput -
        higham2FmaDiscriminantRoundedSquare| <
      |higham2FmaDiscriminantInput * higham2FmaDiscriminantInput -
        higham2FmaDiscriminantSquareNext| := by
  rw [higham2FmaDiscriminantInput_value,
    higham2FmaDiscriminantRoundedSquare_value,
    higham2FmaDiscriminantSquareNext_value]
  norm_num [zpow_neg, abs_of_nonneg, abs_of_neg]

private theorem higham2FmaDiscriminantSquare_finiteNormalRange :
    FloatingPointFormat.ieeeSingleFormat.finiteNormalRange
      (higham2FmaDiscriminantInput * higham2FmaDiscriminantInput) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  have hlo :=
    fmt.normalizedSystem_finiteNormalRange
      higham2FmaDiscriminantRoundedSquare_normalizedSystem
  have hhi :=
    fmt.normalizedSystem_finiteNormalRange
      higham2FmaDiscriminantSquareNext_normalizedSystem
  have hrounded_pos : 0 < higham2FmaDiscriminantRoundedSquare := by
    rw [higham2FmaDiscriminantRoundedSquare_value]
    positivity
  have hnext_pos : 0 < higham2FmaDiscriminantSquareNext := by
    rw [higham2FmaDiscriminantSquareNext_value]
    positivity
  have hproduct_pos :
      0 < higham2FmaDiscriminantInput * higham2FmaDiscriminantInput := by
    rw [higham2FmaDiscriminantInput_value]
    positivity
  rw [FloatingPointFormat.finiteNormalRange, abs_of_pos hproduct_pos]
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos hrounded_pos] at hlo
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos hnext_pos] at hhi
  exact ⟨hlo.1.trans higham2FmaDiscriminantSquare_strict_between.1.le,
    higham2FmaDiscriminantSquare_strict_between.2.le.trans hhi.2⟩

/-- The first binary32 product rounds downward to `1 + 2^-22`. -/
theorem higham2FmaDiscriminantInput_square_rounds_down :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenOp BasicOp.mul
        higham2FmaDiscriminantInput higham2FmaDiscriminantInput =
      higham2FmaDiscriminantRoundedSquare := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let a := higham2FmaDiscriminantRoundedSquare
  let b := higham2FmaDiscriminantSquareNext
  let x := higham2FmaDiscriminantInput * higham2FmaDiscriminantInput
  have hm : fmt.normalizedMantissa 8388610 := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (8388610 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 8388610, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      higham2FmaDiscriminantSquare_finiteNormalRange
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj higham2FmaDiscriminantSquare_strict_between
        higham2FmaDiscriminantSquare_left_closer
  simpa [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact,
    fmt, x, a] using hround

private theorem higham2FmaDiscriminantCorrection_finiteSystem :
    FloatingPointFormat.ieeeSingleFormat.finiteSystem
      (fusedMultiplyAddExact (-higham2FmaDiscriminantInput)
        higham2FmaDiscriminantInput higham2FmaDiscriminantRoundedSquare) := by
  have hexact :
      fusedMultiplyAddExact (-higham2FmaDiscriminantInput)
          higham2FmaDiscriminantInput higham2FmaDiscriminantRoundedSquare =
        -(2 : ℝ) ^ (-46 : ℤ) := by
    rw [higham2FmaDiscriminantInput_value,
      higham2FmaDiscriminantRoundedSquare_value]
    norm_num [fusedMultiplyAddExact, zpow_neg]
  rw [hexact]
  refine Or.inr (Or.inl ⟨true, 8388608, (-45 : ℤ), ?_, ?_, ?_⟩)
  · norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]

private theorem higham2FmaDiscriminantFma_value :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEvenFMA
        (-higham2FmaDiscriminantInput) higham2FmaDiscriminantInput
        higham2FmaDiscriminantRoundedSquare =
      -(2 : ℝ) ^ (-46 : ℤ) := by
  rw [FloatingPointFormat.finiteRoundToEvenFMA_eq_exact_of_finiteSystem
    higham2FmaDiscriminantCorrection_finiteSystem]
  rw [higham2FmaDiscriminantInput_value,
    higham2FmaDiscriminantRoundedSquare_value]
  norm_num [fusedMultiplyAddExact, zpow_neg]

/-- Concrete closure of Higham Section 2.6's discriminant warning.

With `a = b = c = 1 + 2^-23`, the exact discriminant `b^2-a*c` is zero.
The separately rounded product is `1 + 2^-22`, but using one FMA for
`fl(b^2)-a*c` returns exactly `-2^-46`, hence a negative radicand.
-/
theorem higham2_fma_discriminant_source_counterexample_ieeeSingle :
    let fmt := FloatingPointFormat.ieeeSingleFormat
    let b := higham2FmaDiscriminantInput
    fmt.finiteSystem b ∧
      b * b - b * b = 0 ∧
      fmt.finiteRoundToEvenOp BasicOp.mul b b =
        higham2FmaDiscriminantRoundedSquare ∧
      fmt.finiteRoundToEvenFMA (-b) b
          (fmt.finiteRoundToEvenOp BasicOp.mul b b) =
        -(2 : ℝ) ^ (-46 : ℤ) ∧
      fmt.finiteRoundToEvenFMA (-b) b
          (fmt.finiteRoundToEvenOp BasicOp.mul b b) < 0 := by
  dsimp
  have hfinite :
      FloatingPointFormat.ieeeSingleFormat.finiteSystem
        higham2FmaDiscriminantInput :=
    Or.inr (Or.inl higham2FmaDiscriminantInput_normalizedSystem)
  rw [higham2FmaDiscriminantInput_square_rounds_down]
  exact ⟨hfinite, by ring, rfl, higham2FmaDiscriminantFma_value, by
    simpa only [higham2FmaDiscriminantFma_value] using
      (neg_lt_zero.mpr (by positivity : 0 < (2 : ℝ) ^ (-46 : ℤ)))⟩

end

end NumStability
