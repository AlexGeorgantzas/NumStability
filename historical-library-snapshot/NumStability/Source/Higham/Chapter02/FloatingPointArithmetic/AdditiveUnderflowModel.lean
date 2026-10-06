import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic.ErrorModels.AdditiveProperties
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.IeeeOperations
import NumStability.Analysis.FloatingPointArithmetic.IeeeValue
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.FloatingPointArithmetic.RoundToEvenLocalError
import NumStability.Analysis.FloatingPointArithmetic.Rounding

namespace NumStability

/-!
# AdditiveUnderflowModel

Extracted without change from FloatingPointArithmetic.
-/

noncomputable section

namespace FloatingPointFormat

/-- Higham Chapter 2 equation (2.8), gradual-underflow additive-error bound
`u * alpha`, where `alpha = beta^(emin-1)` is the smallest positive normalized
floating-point magnitude. -/
def gradualUnderflowEtaBound (fmt : FloatingPointFormat) : ℝ :=
  fmt.unitRoundoff * fmt.minNormalMagnitude
/-- Higham Chapter 2 equation (2.8), flush-to-zero additive-error bound
`alpha`, the smallest positive normalized floating-point magnitude. -/
def flushToZeroEtaBound (fmt : FloatingPointFormat) : ℝ :=
  fmt.minNormalMagnitude
/-- Higham's gradual-underflow `eta` bound is half the subnormal spacing. -/
theorem gradualUnderflowEtaBound_eq_half_minSubnormalMagnitude
    (fmt : FloatingPointFormat) :
    fmt.gradualUnderflowEtaBound =
      (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
  simpa [gradualUnderflowEtaBound] using
    fmt.unitRoundoff_mul_minNormalMagnitude_eq_half_minSubnormalMagnitude
/-- The gradual-underflow additive-error bound is positive. -/
theorem gradualUnderflowEtaBound_pos (fmt : FloatingPointFormat) :
    0 < fmt.gradualUnderflowEtaBound := by
  rw [fmt.gradualUnderflowEtaBound_eq_half_minSubnormalMagnitude]
  exact mul_pos (by norm_num) fmt.minSubnormalMagnitude_pos
/-- The gradual-underflow additive-error bound is nonnegative. -/
theorem gradualUnderflowEtaBound_nonneg (fmt : FloatingPointFormat) :
    0 ≤ fmt.gradualUnderflowEtaBound :=
  le_of_lt fmt.gradualUnderflowEtaBound_pos
/-- The flush-to-zero additive-error bound is positive. -/
theorem flushToZeroEtaBound_pos (fmt : FloatingPointFormat) :
    0 < fmt.flushToZeroEtaBound := by
  simpa [flushToZeroEtaBound] using fmt.minNormalMagnitude_pos
/-- The flush-to-zero additive-error bound is nonnegative. -/
theorem flushToZeroEtaBound_nonneg (fmt : FloatingPointFormat) :
    0 ≤ fmt.flushToZeroEtaBound :=
  le_of_lt fmt.flushToZeroEtaBound_pos
/-- The gradual-underflow nearest/even additive-error bound is no larger than
the flush-to-zero additive-error bound. -/
theorem gradualUnderflowEtaBound_le_flushToZeroEtaBound
    (fmt : FloatingPointFormat) :
    fmt.gradualUnderflowEtaBound ≤ fmt.flushToZeroEtaBound := by
  rw [fmt.gradualUnderflowEtaBound_eq_half_minSubnormalMagnitude,
    flushToZeroEtaBound]
  have hhalf_le :
      (1 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤
        fmt.minSubnormalMagnitude := by
    have hpos := fmt.minSubnormalMagnitude_pos
    nlinarith
  exact le_trans hhalf_le fmt.minSubnormalMagnitude_le_minNormalMagnitude
/-- No finite candidate is exactly half a subnormal spacing from the source.
This is the visible side condition needed to upgrade Higham's gradual-underflow
additive bound from non-strict `≤` to strict `<`; exact half-cell ties are
intentionally not hidden. -/
def finiteUnderflowNoHalfTie (fmt : FloatingPointFormat) (x : ℝ) : Prop :=
  ∀ y : ℝ, fmt.finiteSystem y →
    absError y x ≠ fmt.gradualUnderflowEtaBound
/-- Any finite nearest-rounded output for a finite-underflow input is within
Higham's gradual-underflow additive-error bound `u * alpha`, equivalently half
a subnormal spacing. -/
theorem nearestRoundingToFinite_absError_le_gradualUnderflowEtaBound_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hround : fmt.nearestRoundingToFinite x y)
    (hunder : fmt.finiteUnderflowRange x) :
    absError y x ≤ fmt.gradualUnderflowEtaBound := by
  rcases
    fmt.exists_finiteSystem_absError_le_half_minSubnormalMagnitude_finiteUnderflowRange
      hunder with
    ⟨z, hz, hdist_z⟩
  have hmin : |x - y| ≤ |x - z| :=
    nearestRoundingIn_minimal hround hz
  have hdist_y : absError y x ≤ absError z x := by
    simpa [absError, abs_sub_comm] using hmin
  exact le_trans hdist_y
    (by
      simpa [fmt.gradualUnderflowEtaBound_eq_half_minSubnormalMagnitude]
        using hdist_z)
/-- Strict variant of the gradual-underflow additive-error bound away from
exact half-cell ties. -/
theorem nearestRoundingToFinite_absError_lt_gradualUnderflowEtaBound_of_finiteUnderflowRange_of_noHalfTie
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hround : fmt.nearestRoundingToFinite x y)
    (hunder : fmt.finiteUnderflowRange x)
    (hnotie : fmt.finiteUnderflowNoHalfTie x) :
    absError y x < fmt.gradualUnderflowEtaBound := by
  have hle :=
    fmt.nearestRoundingToFinite_absError_le_gradualUnderflowEtaBound_of_finiteUnderflowRange
      hround hunder
  exact lt_of_le_of_ne hle (hnotie y (nearestRoundingIn_mem hround))
/-- The source-facing underflow round-to-even branch satisfies Higham's
gradual-underflow additive absolute-error bound. -/
theorem finiteUnderflowRoundToEven_absError_le_gradualUnderflowEtaBound
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    absError (fmt.finiteUnderflowRoundToEven x) x ≤
      fmt.gradualUnderflowEtaBound :=
  fmt.nearestRoundingToFinite_absError_le_gradualUnderflowEtaBound_of_finiteUnderflowRange
    (fmt.finiteUnderflowRoundToEven_nearestRoundingToFinite hunder) hunder
/-- Strict gradual-underflow additive absolute-error bound for the source-facing
underflow round-to-even branch, away from exact half-cell ties. -/
theorem finiteUnderflowRoundToEven_absError_lt_gradualUnderflowEtaBound_of_noHalfTie
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x)
    (hnotie : fmt.finiteUnderflowNoHalfTie x) :
    absError (fmt.finiteUnderflowRoundToEven x) x <
      fmt.gradualUnderflowEtaBound :=
  fmt.nearestRoundingToFinite_absError_lt_gradualUnderflowEtaBound_of_finiteUnderflowRange_of_noHalfTie
    (fmt.finiteUnderflowRoundToEven_nearestRoundingToFinite hunder)
    hunder hnotie
/-- Nonnegative directed round-down underflow has additive error bounded by
the flush-to-zero `eta` constant. -/
theorem finiteUnderflowRoundTowardZeroNonneg_absError_le_flushToZeroEtaBound
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x) (hunder : fmt.finiteUnderflowRange x) :
    absError (fmt.finiteUnderflowRoundTowardZeroNonneg x) x ≤
      fmt.flushToZeroEtaBound := by
  have hout_nonneg :=
    fmt.finiteUnderflowRoundTowardZeroNonneg_nonneg x
  have hout_le := fmt.finiteUnderflowRoundTowardZeroNonneg_le hxnonneg
  have hx_lt_min : x < fmt.minNormalMagnitude := by
    simpa [finiteUnderflowRange, abs_of_nonneg hxnonneg] using hunder
  rw [absError, abs_of_nonpos (by linarith :
    fmt.finiteUnderflowRoundTowardZeroNonneg x - x ≤ 0)]
  simpa [flushToZeroEtaBound] using
    (by linarith [le_of_lt hx_lt_min, hout_nonneg] :
      x - fmt.finiteUnderflowRoundTowardZeroNonneg x ≤
        fmt.minNormalMagnitude)
/-- Nonnegative directed round-up underflow has additive error bounded by the
flush-to-zero `eta` constant. -/
theorem finiteUnderflowRoundTowardPositiveNonneg_absError_le_flushToZeroEtaBound
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x) (hunder : fmt.finiteUnderflowRange x) :
    absError (fmt.finiteUnderflowRoundTowardPositiveNonneg x) x ≤
      fmt.flushToZeroEtaBound := by
  have hx_le :=
    fmt.le_finiteUnderflowRoundTowardPositiveNonneg hxnonneg hunder
  have hout_le_min :=
    fmt.finiteUnderflowRoundTowardPositiveNonneg_le_minNormalMagnitude
      hxnonneg hunder
  rw [absError, abs_of_nonneg (by linarith :
    0 ≤ fmt.finiteUnderflowRoundTowardPositiveNonneg x - x)]
  simpa [flushToZeroEtaBound] using
    (by linarith [hxnonneg, hout_le_min] :
      fmt.finiteUnderflowRoundTowardPositiveNonneg x - x ≤
        fmt.minNormalMagnitude)
/-- Directed round-toward-zero underflow has additive error bounded by the
flush-to-zero `eta` constant. -/
theorem finiteUnderflowRoundTowardZero_absError_le_flushToZeroEtaBound
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    absError (fmt.finiteUnderflowRoundTowardZero x) x ≤
      fmt.flushToZeroEtaBound := by
  unfold finiteUnderflowRoundTowardZero
  by_cases hxnonneg : 0 ≤ x
  · simp [hxnonneg]
    exact
      fmt.finiteUnderflowRoundTowardZeroNonneg_absError_le_flushToZeroEtaBound
        hxnonneg hunder
  · simp [hxnonneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hunder_neg : fmt.finiteUnderflowRange (-x) := by
      simpa [finiteUnderflowRange, abs_neg] using hunder
    rw [absError_neg_left_eq_neg_exact]
    exact
      fmt.finiteUnderflowRoundTowardZeroNonneg_absError_le_flushToZeroEtaBound
        hxneg_nonneg hunder_neg
/-- Directed round-toward-positive underflow has additive error bounded by the
flush-to-zero `eta` constant. -/
theorem finiteUnderflowRoundTowardPositive_absError_le_flushToZeroEtaBound
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    absError (fmt.finiteUnderflowRoundTowardPositive x) x ≤
      fmt.flushToZeroEtaBound := by
  unfold finiteUnderflowRoundTowardPositive
  by_cases hxnonneg : 0 ≤ x
  · simp [hxnonneg]
    exact
      fmt.finiteUnderflowRoundTowardPositiveNonneg_absError_le_flushToZeroEtaBound
        hxnonneg hunder
  · simp [hxnonneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hunder_neg : fmt.finiteUnderflowRange (-x) := by
      simpa [finiteUnderflowRange, abs_neg] using hunder
    rw [absError_neg_left_eq_neg_exact]
    exact
      fmt.finiteUnderflowRoundTowardZeroNonneg_absError_le_flushToZeroEtaBound
        hxneg_nonneg hunder_neg
/-- Directed round-toward-negative underflow has additive error bounded by the
flush-to-zero `eta` constant. -/
theorem finiteUnderflowRoundTowardNegative_absError_le_flushToZeroEtaBound
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    absError (fmt.finiteUnderflowRoundTowardNegative x) x ≤
      fmt.flushToZeroEtaBound := by
  unfold finiteUnderflowRoundTowardNegative
  by_cases hxnonneg : 0 ≤ x
  · simp [hxnonneg]
    exact
      fmt.finiteUnderflowRoundTowardZeroNonneg_absError_le_flushToZeroEtaBound
        hxnonneg hunder
  · simp [hxnonneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hunder_neg : fmt.finiteUnderflowRange (-x) := by
      simpa [finiteUnderflowRange, abs_neg] using hunder
    rw [absError_neg_left_eq_neg_exact]
    exact
      fmt.finiteUnderflowRoundTowardPositiveNonneg_absError_le_flushToZeroEtaBound
        hxneg_nonneg hunder_neg
/-- On source-facing underflow inputs, the total finite round-to-even selector
satisfies Higham's gradual-underflow additive absolute-error bound. -/
theorem finiteRoundToEven_absError_le_gradualUnderflowEtaBound_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    absError (fmt.finiteRoundToEven x) x ≤ fmt.gradualUnderflowEtaBound := by
  classical
  unfold finiteRoundToEven
  simp [hunder]
  exact fmt.finiteUnderflowRoundToEven_absError_le_gradualUnderflowEtaBound hunder
/-- Strict source-facing underflow absolute-error bound for the total finite
round-to-even selector, away from exact half-cell ties. -/
theorem finiteRoundToEven_absError_lt_gradualUnderflowEtaBound_of_finiteUnderflowRange_of_noHalfTie
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x)
    (hnotie : fmt.finiteUnderflowNoHalfTie x) :
    absError (fmt.finiteRoundToEven x) x < fmt.gradualUnderflowEtaBound := by
  classical
  unfold finiteRoundToEven
  simp [hunder]
  exact
    fmt.finiteUnderflowRoundToEven_absError_lt_gradualUnderflowEtaBound_of_noHalfTie
      hunder hnotie
/-- Underflow branch of Higham's additive model (2.8) for the total finite
round-to-even selector: `δ = 0` and the additive term is the absolute rounding
error, bounded by the gradual-underflow `eta` constant. -/
theorem finiteRoundToEven_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    ∃ η : ℝ,
      additiveUnderflowModelWitness (fmt.finiteRoundToEven x) x
        fmt.unitRoundoff fmt.gradualUnderflowEtaBound 0 η := by
  exact
    ⟨fmt.finiteRoundToEven x - x,
      additiveUnderflowModelWitness_underflow_branch_of_absError_le
        fmt.unitRoundoff_pos
        (fmt.finiteRoundToEven_absError_le_gradualUnderflowEtaBound_of_finiteUnderflowRange
          hunder)⟩
/-- Strict underflow branch of Higham's additive model (2.8) for the total
finite round-to-even selector, away from exact half-cell ties. -/
theorem finiteRoundToEven_strictAdditiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_of_noHalfTie
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x)
    (hnotie : fmt.finiteUnderflowNoHalfTie x) :
    ∃ η : ℝ,
      strictAdditiveUnderflowModelWitness (fmt.finiteRoundToEven x) x
        fmt.unitRoundoff fmt.gradualUnderflowEtaBound 0 η := by
  exact
    ⟨fmt.finiteRoundToEven x - x,
      strictAdditiveUnderflowModelWitness_underflow_branch_of_absError_lt
        fmt.unitRoundoff_pos
        (fmt.finiteRoundToEven_absError_lt_gradualUnderflowEtaBound_of_finiteUnderflowRange_of_noHalfTie
          hunder hnotie)⟩
/-- Normal-range branch of Higham's additive underflow model (2.8) for the
total finite round-to-even selector: away from underflow, the additive term is
zero and the usual strict relative-error witness supplies `δ`. -/
theorem finiteRoundToEven_strictAdditiveUnderflowModel_normal_branch_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ η : ℝ,
      strictAdditiveUnderflowModelWitness (fmt.finiteRoundToEven x) x
        fmt.unitRoundoff fmt.gradualUnderflowEtaBound δ η := by
  rcases
    fmt.finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange hx with
    ⟨δ, _hround, hδ, hwit⟩
  exact
    ⟨δ, 0,
      strictAdditiveUnderflowModelWitness_normal_branch
        hδ fmt.gradualUnderflowEtaBound_pos hwit⟩
/-- Any finite underflow selector for an IEEE rounding mode has absolute error
bounded by the flush-to-zero additive-error constant.  Nearest/even is stronger
elsewhere (`gradualUnderflowEtaBound`); directed modes use this full-spacing
bound. -/
theorem finiteRoundToMode_absError_le_flushToZeroEtaBound_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    absError (fmt.finiteRoundToMode mode x) x ≤
      fmt.flushToZeroEtaBound := by
  cases mode
  · exact le_trans
      (fmt.finiteRoundToEven_absError_le_gradualUnderflowEtaBound_of_finiteUnderflowRange
        hunder)
      fmt.gradualUnderflowEtaBound_le_flushToZeroEtaBound
  · rw [finiteRoundToMode_towardZero,
      fmt.finiteRoundTowardZero_eq_underflow hunder]
    exact fmt.finiteUnderflowRoundTowardZero_absError_le_flushToZeroEtaBound
      hunder
  · rw [finiteRoundToMode_towardPositive,
      fmt.finiteRoundTowardPositive_eq_underflow hunder]
    exact
      fmt.finiteUnderflowRoundTowardPositive_absError_le_flushToZeroEtaBound
        hunder
  · rw [finiteRoundToMode_towardNegative,
      fmt.finiteRoundTowardNegative_eq_underflow hunder]
    exact
      fmt.finiteUnderflowRoundTowardNegative_absError_le_flushToZeroEtaBound
        hunder
/-- Underflow branch of the additive model for any finite IEEE rounding-mode
selector, using the flush-to-zero additive-error bound. -/
theorem finiteRoundToMode_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_flush
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    ∃ η : ℝ,
      additiveUnderflowModelWitness (fmt.finiteRoundToMode mode x) x
        fmt.unitRoundoff fmt.flushToZeroEtaBound 0 η := by
  exact
    ⟨fmt.finiteRoundToMode mode x - x,
      additiveUnderflowModelWitness_underflow_branch_of_absError_le
        fmt.unitRoundoff_pos
        (fmt.finiteRoundToMode_absError_le_flushToZeroEtaBound_of_finiteUnderflowRange
          (mode := mode) hunder)⟩
/-- Operation wrapper for the all-mode finite underflow additive model with
the flush-to-zero additive-error bound. -/
theorem finiteRoundToModeOp_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_flush
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteUnderflowRange (BasicOp.exact op x y)) :
    ∃ η : ℝ,
      additiveUnderflowModelWitness (fmt.finiteRoundToModeOp mode op x y)
        (BasicOp.exact op x y) fmt.unitRoundoff
        fmt.flushToZeroEtaBound 0 η := by
  simpa [finiteRoundToModeOp] using
    fmt.finiteRoundToMode_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_flush
      (mode := mode) hxy
theorem ieeeRoundToNearestEvenOpResult_ieeeUnderflowResult_and_additiveUnderflowModel
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteUnderflowRange (BasicOp.exact op x y)) :
    fmt.ieeeUnderflowResult (BasicOp.exact op x y)
        (fmt.finiteRoundToEvenOp op x y)
        (fmt.ieeeRoundToNearestEvenOpResult op x y) ∧
      ∃ η : ℝ,
        additiveUnderflowModelWitness (fmt.finiteRoundToEvenOp op x y)
          (BasicOp.exact op x y) fmt.unitRoundoff
          fmt.gradualUnderflowEtaBound 0 η := by
  have hmodel :
      ∃ η : ℝ,
        additiveUnderflowModelWitness
          (fmt.finiteRoundToEven (BasicOp.exact op x y))
          (BasicOp.exact op x y) fmt.unitRoundoff
          fmt.gradualUnderflowEtaBound 0 η :=
    fmt.finiteRoundToEven_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange
      hxy
  exact
    ⟨fmt.ieeeRoundToNearestEvenOpResult_ieeeUnderflowResult_of_finiteUnderflowRange
        hxy,
      by simpa [finiteRoundToEvenOp] using hmodel⟩
/-- IEEE-facing all-mode operation underflow theorem paired with the
flush-bound additive model. -/
theorem ieeeRoundToModeOpResult_ieeeUnderflowModeResult_and_flushAdditiveUnderflowModel
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteUnderflowRange (BasicOp.exact op x y)) :
    fmt.ieeeUnderflowModeResult mode (BasicOp.exact op x y)
        (fmt.finiteRoundToModeOp mode op x y)
        (fmt.ieeeRoundToModeOpResult mode op x y) ∧
      ∃ η : ℝ,
        additiveUnderflowModelWitness (fmt.finiteRoundToModeOp mode op x y)
          (BasicOp.exact op x y) fmt.unitRoundoff
          fmt.flushToZeroEtaBound 0 η := by
  exact
    ⟨fmt.ieeeRoundToModeOpResult_ieeeUnderflowModeResult_of_finiteUnderflowRange
        (mode := mode) hxy,
      fmt.finiteRoundToModeOp_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_flush
        (mode := mode) hxy⟩
/-- Normal-range branch of Higham's additive underflow model (2.8) for the
ordinary finite primitive-operation wrapper: away from underflow, `η = 0`. -/
theorem finiteRoundToEvenOp_strictAdditiveUnderflowModel_normal_branch_of_finiteNormalRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    ∃ δ η : ℝ,
      strictAdditiveUnderflowModelWitness (fmt.finiteRoundToEvenOp op x y)
        (BasicOp.exact op x y) fmt.unitRoundoff fmt.gradualUnderflowEtaBound
        δ η := by
  rcases
    fmt.finiteRoundToEvenOp_signedRelErrorWitness_lt_of_finiteNormalRange
      hxy with
    ⟨δ, _hround, hδ, hwit⟩
  exact
    ⟨δ, 0,
      strictAdditiveUnderflowModelWitness_normal_branch
        hδ fmt.gradualUnderflowEtaBound_pos hwit⟩
/-- Underflow branch of Higham's additive model (2.8) for the ordinary finite
primitive-operation wrapper. -/
theorem finiteRoundToEvenOp_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteUnderflowRange (BasicOp.exact op x y)) :
    ∃ η : ℝ,
      additiveUnderflowModelWitness (fmt.finiteRoundToEvenOp op x y)
        (BasicOp.exact op x y) fmt.unitRoundoff fmt.gradualUnderflowEtaBound
        0 η := by
  simpa [finiteRoundToEvenOp] using
    fmt.finiteRoundToEven_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange
      (x := BasicOp.exact op x y) hxy
/-- Strict underflow branch of Higham's additive model (2.8) for the ordinary
finite primitive-operation wrapper, away from exact half-cell ties. -/
theorem finiteRoundToEvenOp_strictAdditiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_of_noHalfTie
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteUnderflowRange (BasicOp.exact op x y))
    (hnotie : fmt.finiteUnderflowNoHalfTie (BasicOp.exact op x y)) :
    ∃ η : ℝ,
      strictAdditiveUnderflowModelWitness (fmt.finiteRoundToEvenOp op x y)
        (BasicOp.exact op x y) fmt.unitRoundoff fmt.gradualUnderflowEtaBound
        0 η := by
  simpa [finiteRoundToEvenOp] using
    fmt.finiteRoundToEven_strictAdditiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_of_noHalfTie
      (x := BasicOp.exact op x y) hxy hnotie
/-- Square-root wrapper for the all-mode finite underflow additive model with
the flush-to-zero additive-error bound. -/
theorem finiteRoundToModeSqrt_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_flush
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hsqrt : fmt.finiteUnderflowRange (Real.sqrt x)) :
    ∃ η : ℝ,
      additiveUnderflowModelWitness (fmt.finiteRoundToModeSqrt mode x)
        (Real.sqrt x) fmt.unitRoundoff fmt.flushToZeroEtaBound 0 η := by
  simpa [finiteRoundToModeSqrt] using
    fmt.finiteRoundToMode_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_flush
      (mode := mode) hsqrt
/-- Normal-range branch of Higham's additive underflow model (2.8) for the
finite square-root wrapper: away from underflow, `η = 0`. -/
theorem finiteRoundToEvenSqrt_strictAdditiveUnderflowModel_normal_branch_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (_hx_nonneg : 0 ≤ x) (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    ∃ δ η : ℝ,
      strictAdditiveUnderflowModelWitness (fmt.finiteRoundToEvenSqrt x)
        (Real.sqrt x) fmt.unitRoundoff fmt.gradualUnderflowEtaBound δ η := by
  rcases
    fmt.finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange
      hsqrt with
    ⟨δ, _hround, hδ, hwit⟩
  exact
    ⟨δ, 0,
      strictAdditiveUnderflowModelWitness_normal_branch
        hδ fmt.gradualUnderflowEtaBound_pos
        (by simpa [finiteRoundToEvenSqrt] using hwit)⟩
/-- Underflow branch of Higham's additive model (2.8) for the finite
square-root wrapper. -/
theorem finiteRoundToEvenSqrt_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsqrt : fmt.finiteUnderflowRange (Real.sqrt x)) :
    ∃ η : ℝ,
      additiveUnderflowModelWitness (fmt.finiteRoundToEvenSqrt x)
        (Real.sqrt x) fmt.unitRoundoff fmt.gradualUnderflowEtaBound 0 η := by
  simpa [finiteRoundToEvenSqrt] using
    fmt.finiteRoundToEven_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange
      (x := Real.sqrt x) hsqrt
/-- Strict underflow branch of Higham's additive model (2.8) for the finite
square-root wrapper, away from exact half-cell ties. -/
theorem finiteRoundToEvenSqrt_strictAdditiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_of_noHalfTie
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsqrt : fmt.finiteUnderflowRange (Real.sqrt x))
    (hnotie : fmt.finiteUnderflowNoHalfTie (Real.sqrt x)) :
    ∃ η : ℝ,
      strictAdditiveUnderflowModelWitness (fmt.finiteRoundToEvenSqrt x)
        (Real.sqrt x) fmt.unitRoundoff fmt.gradualUnderflowEtaBound 0 η := by
  simpa [finiteRoundToEvenSqrt] using
    fmt.finiteRoundToEven_strictAdditiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_of_noHalfTie
      (x := Real.sqrt x) hsqrt hnotie
theorem ieeeRoundToNearestEvenSqrtResult_ieeeUnderflowResult_and_additiveUnderflowModel
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteUnderflowRange (Real.sqrt x)) :
    fmt.ieeeUnderflowResult (Real.sqrt x)
        (fmt.finiteRoundToEvenSqrt x)
        (fmt.ieeeRoundToNearestEvenSqrtResult x) ∧
      ∃ η : ℝ,
        additiveUnderflowModelWitness (fmt.finiteRoundToEvenSqrt x)
          (Real.sqrt x) fmt.unitRoundoff
          fmt.gradualUnderflowEtaBound 0 η := by
  exact
    ⟨fmt.ieeeRoundToNearestEvenSqrtResult_ieeeUnderflowResult_of_finiteUnderflowRange
        hx_nonneg hsqrt,
      fmt.finiteRoundToEvenSqrt_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange
        hsqrt⟩
/-- IEEE-facing all-mode square-root underflow theorem paired with the
flush-bound additive model. -/
theorem ieeeRoundToModeSqrtResult_ieeeUnderflowModeResult_and_flushAdditiveUnderflowModel
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteUnderflowRange (Real.sqrt x)) :
    fmt.ieeeUnderflowModeResult mode (Real.sqrt x)
        (fmt.finiteRoundToModeSqrt mode x)
        (fmt.ieeeRoundToModeSqrtResult mode x) ∧
      ∃ η : ℝ,
        additiveUnderflowModelWitness (fmt.finiteRoundToModeSqrt mode x)
          (Real.sqrt x) fmt.unitRoundoff fmt.flushToZeroEtaBound 0 η := by
  exact
    ⟨fmt.ieeeRoundToModeSqrtResult_ieeeUnderflowModeResult_of_finiteUnderflowRange
        (mode := mode) hx_nonneg hsqrt,
      fmt.finiteRoundToModeSqrt_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_flush
        (mode := mode) hsqrt⟩

end FloatingPointFormat

end

end NumStability
