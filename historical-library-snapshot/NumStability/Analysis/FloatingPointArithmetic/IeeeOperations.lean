import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.IeeeExceptions
import NumStability.Analysis.FloatingPointArithmetic.IeeeValue
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.FloatingPointArithmetic.RoundToEvenLocalError
import NumStability.Analysis.FloatingPointArithmetic.Rounding

namespace NumStability

/-!
# IeeeOperations

Extracted without change from FloatingPointArithmetic.
-/

noncomputable section

namespace FloatingPointFormat

/-- IEEE-facing wrapper for the source-facing finite saturation map.  The
result is explicitly finite and flag-free, so this bridge records the current
finite real-valued policy rather than IEEE overflow exception/infinity
semantics. -/
def finiteOverflowSaturationIeeeFiniteResult
    (fmt : FloatingPointFormat) (x : ℝ) : IeeeOperationResult :=
  IeeeOperationResult.finiteNoFlags (fmt.finiteOverflowSaturation x)
theorem finiteOverflowSaturationIeeeFiniteResult_isFinite
    (fmt : FloatingPointFormat) (x : ℝ) :
    (fmt.finiteOverflowSaturationIeeeFiniteResult x).isFinite :=
  IeeeOperationResult.finiteNoFlags_isFinite _
theorem finiteOverflowSaturationIeeeFiniteResult_noFlags
    (fmt : FloatingPointFormat) (x : ℝ) :
    (fmt.finiteOverflowSaturationIeeeFiniteResult x).noFlags :=
  IeeeOperationResult.finiteNoFlags_noFlags _
theorem finiteOverflowSaturationIeeeFiniteResult_not_ieeeOverflowResult
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    ¬ fmt.ieeeOverflowResult mode x
      (fmt.finiteOverflowSaturationIeeeFiniteResult x) := by
  simpa [finiteOverflowSaturationIeeeFiniteResult] using
    (ieeeOverflowResult_not_finiteNoFlags
      (fmt := fmt) (mode := mode) (x := x)
      (y := fmt.finiteOverflowSaturation x))
theorem finiteOverflowSaturationIeeeFiniteResult_toReal?
    (fmt : FloatingPointFormat) (x : ℝ) :
    (fmt.finiteOverflowSaturationIeeeFiniteResult x).value.toReal? =
      some (fmt.finiteOverflowSaturation x) :=
  IeeeOperationResult.finiteNoFlags_toReal? _
/-- IEEE-facing wrapper for the source-facing finite round-to-even selector.
It is finite and flag-free by construction; full IEEE exception and special
value behavior is represented by separate future semantics. -/
noncomputable def finiteRoundToEvenIeeeFiniteResult
    (fmt : FloatingPointFormat) (x : ℝ) : IeeeOperationResult :=
  IeeeOperationResult.finiteNoFlags (fmt.finiteRoundToEven x)
theorem finiteRoundToEvenIeeeFiniteResult_isFinite
    (fmt : FloatingPointFormat) (x : ℝ) :
    (fmt.finiteRoundToEvenIeeeFiniteResult x).isFinite :=
  IeeeOperationResult.finiteNoFlags_isFinite _
theorem finiteRoundToEvenIeeeFiniteResult_noFlags
    (fmt : FloatingPointFormat) (x : ℝ) :
    (fmt.finiteRoundToEvenIeeeFiniteResult x).noFlags :=
  IeeeOperationResult.finiteNoFlags_noFlags _
theorem finiteRoundToEvenIeeeFiniteResult_toReal?
    (fmt : FloatingPointFormat) (x : ℝ) :
    (fmt.finiteRoundToEvenIeeeFiniteResult x).value.toReal? =
      some (fmt.finiteRoundToEven x) :=
  IeeeOperationResult.finiteNoFlags_toReal? _
/-- IEEE-facing finite/no-flags wrapper for the source-facing finite primitive
operation selector. -/
noncomputable def finiteRoundToEvenOpIeeeFiniteResult
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    IeeeOperationResult :=
  IeeeOperationResult.finiteNoFlags (fmt.finiteRoundToEvenOp op x y)
theorem finiteRoundToEvenOpIeeeFiniteResult_isFinite
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    (fmt.finiteRoundToEvenOpIeeeFiniteResult op x y).isFinite :=
  IeeeOperationResult.finiteNoFlags_isFinite _
theorem finiteRoundToEvenOpIeeeFiniteResult_noFlags
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    (fmt.finiteRoundToEvenOpIeeeFiniteResult op x y).noFlags :=
  IeeeOperationResult.finiteNoFlags_noFlags _
theorem finiteRoundToEvenOpIeeeFiniteResult_toReal?
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    (fmt.finiteRoundToEvenOpIeeeFiniteResult op x y).value.toReal? =
      some (fmt.finiteRoundToEvenOp op x y) :=
  IeeeOperationResult.finiteNoFlags_toReal? _
/-- IEEE-facing nearest/even primitive-operation wrapper with the first
overflow branch.  If the exact real result is in the source-facing overflow
range, it returns the flagged IEEE overflow default result.  If the exact real
result is in the underflow range, it returns the finite rounded value with the
underflow flag.  Otherwise it uses the finite/no-flags source-facing
round-to-even operation wrapper.  Special-value inputs remain separate future
semantics. -/
noncomputable def ieeeRoundToNearestEvenOpResult
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    IeeeOperationResult := by
  classical
  let exact := BasicOp.exact op x y
  let rounded := fmt.finiteRoundToEvenOp op x y
  exact
    if fmt.finiteOverflowRange exact then
      fmt.ieeeOverflowDefaultResult IeeeRoundingMode.nearestEven exact
    else if fmt.finiteUnderflowRange exact then
      fmt.ieeeUnderflowDefaultResult exact rounded
    else
      IeeeOperationResult.finiteNoFlags rounded
theorem ieeeRoundToNearestEvenOpResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteOverflowRange (BasicOp.exact op x y)) :
    fmt.ieeeOverflowResult IeeeRoundingMode.nearestEven (BasicOp.exact op x y)
      (fmt.ieeeRoundToNearestEvenOpResult op x y) := by
  classical
  simpa [ieeeRoundToNearestEvenOpResult, hxy] using
    (fmt.ieeeOverflowDefaultResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := IeeeRoundingMode.nearestEven) hxy)
theorem ieeeRoundToNearestEvenOpResult_noFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hover : ¬ fmt.finiteOverflowRange (BasicOp.exact op x y))
    (hunder : ¬ fmt.finiteUnderflowRange (BasicOp.exact op x y)) :
    (fmt.ieeeRoundToNearestEvenOpResult op x y).noFlags := by
  classical
  simpa [ieeeRoundToNearestEvenOpResult, hover, hunder] using
    (IeeeOperationResult.finiteNoFlags_noFlags
      (fmt.finiteRoundToEvenOp op x y))
theorem ieeeRoundToNearestEvenOpResult_toReal?_of_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : ¬ fmt.finiteOverflowRange (BasicOp.exact op x y)) :
    (fmt.ieeeRoundToNearestEvenOpResult op x y).value.toReal? =
      some (fmt.finiteRoundToEvenOp op x y) := by
  classical
  by_cases hunder : fmt.finiteUnderflowRange (BasicOp.exact op x y)
  · simpa [ieeeRoundToNearestEvenOpResult, hxy, hunder] using
      (fmt.ieeeUnderflowDefaultResult_toReal? (BasicOp.exact op x y)
        (fmt.finiteRoundToEvenOp op x y))
  · simpa [ieeeRoundToNearestEvenOpResult, hxy, hunder] using
      (IeeeOperationResult.finiteNoFlags_toReal?
        (fmt.finiteRoundToEvenOp op x y))
/-- Finite-normal exact primitive results take the nearest/even finite/no-flags
IEEE wrapper branch. -/
theorem ieeeRoundToNearestEvenOpResult_eq_finiteNoFlags_of_finiteNormalRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    fmt.ieeeRoundToNearestEvenOpResult op x y =
      IeeeOperationResult.finiteNoFlags (fmt.finiteRoundToEvenOp op x y) := by
  classical
  simp [ieeeRoundToNearestEvenOpResult,
    fmt.finiteNormalRange_not_finiteOverflowRange hxy,
    fmt.finiteNormalRange_not_finiteUnderflowRange hxy]
/-- Finite-normal exact primitive results do not raise IEEE flags in the
nearest/even source-facing wrapper. -/
theorem ieeeRoundToNearestEvenOpResult_noFlags_of_finiteNormalRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    (fmt.ieeeRoundToNearestEvenOpResult op x y).noFlags := by
  rw [fmt.ieeeRoundToNearestEvenOpResult_eq_finiteNoFlags_of_finiteNormalRange hxy]
  exact IeeeOperationResult.finiteNoFlags_noFlags _
/-- Finite-normal exact primitive results expose the finite round-to-even
operation value in the nearest/even IEEE wrapper. -/
theorem ieeeRoundToNearestEvenOpResult_toReal?_of_finiteNormalRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    (fmt.ieeeRoundToNearestEvenOpResult op x y).value.toReal? =
      some (fmt.finiteRoundToEvenOp op x y) := by
  rw [fmt.ieeeRoundToNearestEvenOpResult_eq_finiteNoFlags_of_finiteNormalRange hxy]
  exact IeeeOperationResult.finiteNoFlags_toReal? _
theorem ieeeRoundToNearestEvenOpResult_ieeeUnderflowResult_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteUnderflowRange (BasicOp.exact op x y)) :
    fmt.ieeeUnderflowResult (BasicOp.exact op x y)
      (fmt.finiteRoundToEvenOp op x y)
      (fmt.ieeeRoundToNearestEvenOpResult op x y) := by
  classical
  have hover : ¬ fmt.finiteOverflowRange (BasicOp.exact op x y) := by
    intro hover
    have hle := fmt.minNormalMagnitude_le_maxFiniteMagnitude
    rw [finiteUnderflowRange] at hxy
    rw [finiteOverflowRange] at hover
    linarith
  simpa [ieeeRoundToNearestEvenOpResult, hover, hxy] using
    (fmt.ieeeUnderflowDefaultResult_ieeeUnderflowResult
      hxy
      (by
        simpa [finiteRoundToEvenOp] using
          fmt.finiteRoundToEven_nearestRoundingToFinite
            (BasicOp.exact op x y)))
/-- IEEE-facing primitive-operation wrapper parameterized by an IEEE rounding
mode.  Overflow dispatch uses the mode-dependent `ieeeOverflowValue` table, and
the finite underflow/no-flag branches use the source-facing finite selector for
the same mode.  Special-value inputs, traps, and NaN payload/signaling behavior
remain separate future semantics. -/
noncomputable def ieeeRoundToModeOpResult
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) (x y : ℝ) : IeeeOperationResult := by
  classical
  let exact := BasicOp.exact op x y
  let rounded := fmt.finiteRoundToModeOp mode op x y
  exact
    if fmt.finiteOverflowRange exact then
      fmt.ieeeOverflowDefaultResult mode exact
    else if fmt.finiteUnderflowRange exact then
      fmt.ieeeUnderflowDefaultResult exact rounded
    else
      IeeeOperationResult.finiteNoFlags rounded
/-- Directed-mode alias for round toward zero. -/
noncomputable def ieeeRoundTowardZeroOpResult
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    IeeeOperationResult :=
  fmt.ieeeRoundToModeOpResult IeeeRoundingMode.towardZero op x y
/-- Directed-mode alias for round toward positive infinity. -/
noncomputable def ieeeRoundTowardPositiveOpResult
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    IeeeOperationResult :=
  fmt.ieeeRoundToModeOpResult IeeeRoundingMode.towardPositive op x y
/-- Directed-mode alias for round toward negative infinity. -/
noncomputable def ieeeRoundTowardNegativeOpResult
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    IeeeOperationResult :=
  fmt.ieeeRoundToModeOpResult IeeeRoundingMode.towardNegative op x y
theorem ieeeRoundToModeOpResult_nearestEven
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    fmt.ieeeRoundToModeOpResult IeeeRoundingMode.nearestEven op x y =
      fmt.ieeeRoundToNearestEvenOpResult op x y := by
  classical
  rfl
theorem ieeeRoundToModeOpResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteOverflowRange (BasicOp.exact op x y)) :
    fmt.ieeeOverflowResult mode (BasicOp.exact op x y)
      (fmt.ieeeRoundToModeOpResult mode op x y) := by
  classical
  simpa [ieeeRoundToModeOpResult, hxy] using
    (fmt.ieeeOverflowDefaultResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := mode) hxy)
theorem ieeeRoundToModeOpResult_eq_finiteNoFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hover : ¬ fmt.finiteOverflowRange (BasicOp.exact op x y))
    (hunder : ¬ fmt.finiteUnderflowRange (BasicOp.exact op x y)) :
    fmt.ieeeRoundToModeOpResult mode op x y =
      IeeeOperationResult.finiteNoFlags
        (fmt.finiteRoundToModeOp mode op x y) := by
  classical
  simp [ieeeRoundToModeOpResult, hover, hunder]
theorem ieeeRoundToModeOpResult_noFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hover : ¬ fmt.finiteOverflowRange (BasicOp.exact op x y))
    (hunder : ¬ fmt.finiteUnderflowRange (BasicOp.exact op x y)) :
    (fmt.ieeeRoundToModeOpResult mode op x y).noFlags := by
  rw [
    fmt.ieeeRoundToModeOpResult_eq_finiteNoFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
      hover hunder]
  exact IeeeOperationResult.finiteNoFlags_noFlags _
theorem ieeeRoundToModeOpResult_toReal?_of_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : ¬ fmt.finiteOverflowRange (BasicOp.exact op x y)) :
    (fmt.ieeeRoundToModeOpResult mode op x y).value.toReal? =
      some (fmt.finiteRoundToModeOp mode op x y) := by
  classical
  by_cases hunder : fmt.finiteUnderflowRange (BasicOp.exact op x y)
  · simpa [ieeeRoundToModeOpResult, hxy, hunder] using
      (fmt.ieeeUnderflowDefaultResult_toReal? (BasicOp.exact op x y)
        (fmt.finiteRoundToModeOp mode op x y))
  · simpa [ieeeRoundToModeOpResult, hxy, hunder] using
      (IeeeOperationResult.finiteNoFlags_toReal?
        (fmt.finiteRoundToModeOp mode op x y))
/-- Finite-normal exact primitive results take the finite/no-flags branch for
any source-facing IEEE rounding mode wrapper. -/
theorem ieeeRoundToModeOpResult_eq_finiteNoFlags_of_finiteNormalRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    fmt.ieeeRoundToModeOpResult mode op x y =
      IeeeOperationResult.finiteNoFlags
        (fmt.finiteRoundToModeOp mode op x y) := by
  exact
    fmt.ieeeRoundToModeOpResult_eq_finiteNoFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
      (fmt.finiteNormalRange_not_finiteOverflowRange hxy)
      (fmt.finiteNormalRange_not_finiteUnderflowRange hxy)
/-- Finite-normal exact primitive results do not raise IEEE flags for any
source-facing rounding mode wrapper. -/
theorem ieeeRoundToModeOpResult_noFlags_of_finiteNormalRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    (fmt.ieeeRoundToModeOpResult mode op x y).noFlags := by
  rw [fmt.ieeeRoundToModeOpResult_eq_finiteNoFlags_of_finiteNormalRange hxy]
  exact IeeeOperationResult.finiteNoFlags_noFlags _
/-- Finite-normal exact primitive results expose the selected finite rounded
value for any source-facing IEEE rounding mode wrapper. -/
theorem ieeeRoundToModeOpResult_toReal?_of_finiteNormalRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    (fmt.ieeeRoundToModeOpResult mode op x y).value.toReal? =
      some (fmt.finiteRoundToModeOp mode op x y) := by
  rw [fmt.ieeeRoundToModeOpResult_eq_finiteNoFlags_of_finiteNormalRange hxy]
  exact IeeeOperationResult.finiteNoFlags_toReal? _
/-- IEEE-facing primitive-operation wrapper that records Table 2.2's ordinary
finite inexact exception: outside the overflow and underflow branches, an exact
rounded result is flag-free, while a rounded value different from the exact real
operation result raises exactly the inexact flag.  This is still only the
ordinary finite real-valued branch, not traps or full special-value semantics. -/
noncomputable def ieeeRoundToModeOpInexactAwareResult
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) (x y : ℝ) : IeeeOperationResult := by
  classical
  let exact := BasicOp.exact op x y
  let rounded := fmt.finiteRoundToModeOp mode op x y
  exact
    if fmt.finiteOverflowRange exact then
      fmt.ieeeOverflowDefaultResult mode exact
    else if fmt.finiteUnderflowRange exact then
      fmt.ieeeUnderflowDefaultResult exact rounded
    else if rounded = exact then
      IeeeOperationResult.finiteNoFlags rounded
    else
      ieeeInexactDefaultResult rounded
theorem ieeeRoundToModeOpInexactAwareResult_ieeeInexactResult_of_ne_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hover : ¬ fmt.finiteOverflowRange (BasicOp.exact op x y))
    (hunder : ¬ fmt.finiteUnderflowRange (BasicOp.exact op x y))
    (hne :
      fmt.finiteRoundToModeOp mode op x y ≠ BasicOp.exact op x y) :
    ieeeInexactResult (BasicOp.exact op x y)
      (fmt.finiteRoundToModeOp mode op x y)
      (fmt.ieeeRoundToModeOpInexactAwareResult mode op x y) := by
  classical
  simpa [ieeeRoundToModeOpInexactAwareResult, hover, hunder, hne] using
    (ieeeInexactDefaultResult_ieeeInexactResult
      (exact := BasicOp.exact op x y)
      (rounded := fmt.finiteRoundToModeOp mode op x y) hne)
theorem ieeeRoundToModeOpInexactAwareResult_eq_finiteNoFlags_of_eq_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hover : ¬ fmt.finiteOverflowRange (BasicOp.exact op x y))
    (hunder : ¬ fmt.finiteUnderflowRange (BasicOp.exact op x y))
    (heq :
      fmt.finiteRoundToModeOp mode op x y = BasicOp.exact op x y) :
    fmt.ieeeRoundToModeOpInexactAwareResult mode op x y =
      IeeeOperationResult.finiteNoFlags
        (fmt.finiteRoundToModeOp mode op x y) := by
  classical
  simp [ieeeRoundToModeOpInexactAwareResult, hover, hunder, heq]
theorem ieeeRoundToModeOpInexactAwareResult_ieeeInexactResult_of_finiteNormalRange_of_ne
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y))
    (hne :
      fmt.finiteRoundToModeOp mode op x y ≠ BasicOp.exact op x y) :
    ieeeInexactResult (BasicOp.exact op x y)
      (fmt.finiteRoundToModeOp mode op x y)
      (fmt.ieeeRoundToModeOpInexactAwareResult mode op x y) :=
  fmt.ieeeRoundToModeOpInexactAwareResult_ieeeInexactResult_of_ne_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
    (fmt.finiteNormalRange_not_finiteOverflowRange hxy)
    (fmt.finiteNormalRange_not_finiteUnderflowRange hxy)
    hne
theorem ieeeRoundToModeOpInexactAwareResult_eq_finiteNoFlags_of_finiteNormalRange_of_eq
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y))
    (heq :
      fmt.finiteRoundToModeOp mode op x y = BasicOp.exact op x y) :
    fmt.ieeeRoundToModeOpInexactAwareResult mode op x y =
      IeeeOperationResult.finiteNoFlags
        (fmt.finiteRoundToModeOp mode op x y) :=
  fmt.ieeeRoundToModeOpInexactAwareResult_eq_finiteNoFlags_of_eq_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
    (fmt.finiteNormalRange_not_finiteOverflowRange hxy)
    (fmt.finiteNormalRange_not_finiteUnderflowRange hxy)
    heq
/-- Predicate-level IEEE primitive-operation value dispatch.  Special-value,
division-by-zero, and mode-aware exact-zero-sum branches take precedence; if no
such value branch applies and both operands are ordinary finite payloads, the
result is the existing mode-aware finite wrapper.  This is a guarded dispatch
predicate, not an executable hardware instruction semantics with traps or NaN
payloads. -/
def ieeeRoundToModeOpValueResult
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) (x y : IeeeValue)
    (r : IeeeOperationResult) : Prop :=
  ieeePrimitiveValueBranchResult op x y r ∨
    ieeePrimitiveAddSubZeroSumResult mode op x y r ∨
      (¬ ∃ r', ieeePrimitiveValueBranchResult op x y r') ∧
        ∃ xr yr : ℝ,
          x = IeeeValue.finite xr ∧ y = IeeeValue.finite yr ∧
            r = fmt.ieeeRoundToModeOpResult mode op xr yr
/-- Nearest/even alias for the primitive-operation value dispatch predicate. -/
def ieeeRoundToNearestEvenOpValueResult
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : IeeeValue)
    (r : IeeeOperationResult) : Prop :=
  fmt.ieeeRoundToModeOpValueResult IeeeRoundingMode.nearestEven op x y r
theorem ieeeRoundToModeOpValueResult_branch
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveValueBranchResult op x y r) :
    fmt.ieeeRoundToModeOpValueResult mode op x y r :=
  Or.inl h
theorem ieeeRoundToModeOpValueResult_addSubZeroSum
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubZeroSumResult mode op x y r) :
    fmt.ieeeRoundToModeOpValueResult mode op x y r :=
  Or.inr (Or.inl h)
theorem ieeeRoundToModeOpValueResult_addSubZeroSumDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubZeroSumResult? mode op x y = some r) :
    fmt.ieeeRoundToModeOpValueResult mode op x y r :=
  fmt.ieeeRoundToModeOpValueResult_addSubZeroSum
    (ieeePrimitiveAddSubZeroSumResult?_sound h)
theorem ieeeRoundToModeOpValueResult_add_posZero_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.add
      IeeeValue.posZero IeeeValue.negZero
      (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) :=
  fmt.ieeeRoundToModeOpValueResult_addSubZeroSum
    (ieeePrimitiveAddSubZeroSumResult_add_posZero_negZero mode)
theorem ieeeRoundToModeOpValueResult_add_negZero_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.add
      IeeeValue.negZero IeeeValue.posZero
      (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) :=
  fmt.ieeeRoundToModeOpValueResult_addSubZeroSum
    (ieeePrimitiveAddSubZeroSumResult_add_negZero_posZero mode)
theorem ieeeRoundToModeOpValueResult_sub_posZero_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.sub
      IeeeValue.posZero IeeeValue.posZero
      (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) :=
  fmt.ieeeRoundToModeOpValueResult_addSubZeroSum
    (ieeePrimitiveAddSubZeroSumResult_sub_posZero_posZero mode)
theorem ieeeRoundToModeOpValueResult_sub_negZero_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.sub
      IeeeValue.negZero IeeeValue.negZero
      (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) :=
  fmt.ieeeRoundToModeOpValueResult_addSubZeroSum
    (ieeePrimitiveAddSubZeroSumResult_sub_negZero_negZero mode)
theorem ieeeRoundToModeOpValueResult_special
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveSpecialValueResult op x y r) :
    fmt.ieeeRoundToModeOpValueResult mode op x y r :=
  fmt.ieeeRoundToModeOpValueResult_branch
    (ieeePrimitiveValueBranchResult_special h)
theorem ieeeRoundToModeOpValueResult_quietNaNDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeQuietNaNPropagationResult? x y = some r) :
    fmt.ieeeRoundToModeOpValueResult mode op x y r :=
  fmt.ieeeRoundToModeOpValueResult_branch
    (ieeePrimitiveValueBranchResult_quietNaNDefault? h)
theorem ieeeRoundToModeOpValueResult_left_nan
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) (y : IeeeValue) :
    fmt.ieeeRoundToModeOpValueResult mode op IeeeValue.nan y
      (IeeeOperationResult.valueNoFlags IeeeValue.nan) :=
  fmt.ieeeRoundToModeOpValueResult_quietNaNDefault? (mode := mode)
    (ieeeQuietNaNPropagationResult?_left_nan y)
theorem ieeeRoundToModeOpValueResult_right_nan
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) (x : IeeeValue) :
    fmt.ieeeRoundToModeOpValueResult mode op x IeeeValue.nan
      (IeeeOperationResult.valueNoFlags IeeeValue.nan) :=
  fmt.ieeeRoundToModeOpValueResult_quietNaNDefault? (mode := mode)
    (ieeeQuietNaNPropagationResult?_right_nan x)
theorem ieeeRoundToModeOpValueResult_invalidOperationDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInvalidOperationResult? op x y = some r) :
    fmt.ieeeRoundToModeOpValueResult mode op x y r :=
  fmt.ieeeRoundToModeOpValueResult_branch
    (ieeePrimitiveValueBranchResult_invalidOperationDefault? h)
theorem ieeeRoundToModeOpValueResult_of_invalidOperationInput
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue}
    (hinput : ieeePrimitiveInvalidOperationInput op x y) :
    fmt.ieeeRoundToModeOpValueResult mode op x y
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult_branch
    (ieeePrimitiveValueBranchResult_invalidOperationDefault?
      (ieeePrimitiveInvalidOperationResult?_of_input hinput))
theorem ieeeRoundToModeOpValueResult_divisionByZero
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeDivisionByZeroResult x y r) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.div x y r :=
  fmt.ieeeRoundToModeOpValueResult_branch
    (ieeePrimitiveValueBranchResult_divisionByZero h)
theorem ieeeRoundToModeOpValueResult_divisionByZeroDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeDivisionByZeroDefaultResult? x y = some r) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.div x y r :=
  fmt.ieeeRoundToModeOpValueResult_branch
    (ieeePrimitiveValueBranchResult_divisionByZeroDefault? h)
theorem ieeeRoundToModeOpValueResult_mulSignedZeroDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveMulSignedZeroResult? x y = some r) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.mul x y r :=
  fmt.ieeeRoundToModeOpValueResult_branch
    (ieeePrimitiveValueBranchResult_mulSignedZeroDefault? h)
theorem ieeeRoundToModeOpValueResult_signedZeroOverFiniteDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveSignedZeroOverFiniteResult? x y = some r) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.div x y r :=
  fmt.ieeeRoundToModeOpValueResult_branch
    (ieeePrimitiveValueBranchResult_signedZeroOverFiniteDefault? h)
theorem ieeeRoundToModeOpValueResult_addSubSignedZeroDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubSignedZeroResult? op x y = some r) :
    fmt.ieeeRoundToModeOpValueResult mode op x y r :=
  fmt.ieeeRoundToModeOpValueResult_branch
    (ieeePrimitiveValueBranchResult_addSubSignedZeroDefault? h)
theorem ieeeRoundToModeOpValueResult_finiteOverInfinityDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveFiniteOverInfinityResult? op x y = some r) :
    fmt.ieeeRoundToModeOpValueResult mode op x y r :=
  fmt.ieeeRoundToModeOpValueResult_branch
    (ieeePrimitiveValueBranchResult_finiteOverInfinityDefault? h)
theorem ieeeRoundToModeOpValueResult_addSubFiniteSignedZeroDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubFiniteSignedZeroResult? op x y = some r) :
    fmt.ieeeRoundToModeOpValueResult mode op x y r :=
  fmt.ieeeRoundToModeOpValueResult_branch
    (ieeePrimitiveValueBranchResult_addSubFiniteSignedZeroDefault? h)
theorem ieeeRoundToModeOpValueResult_add_negInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.add
      IeeeValue.negInf IeeeValue.posInf
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult_of_invalidOperationInput
    ieeePrimitiveInvalidOperationInput_add_negInf_posInf
theorem ieeeRoundToModeOpValueResult_sub_posInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.sub
      IeeeValue.posInf IeeeValue.posInf
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult_of_invalidOperationInput
    ieeePrimitiveInvalidOperationInput_sub_posInf_posInf
theorem ieeeRoundToModeOpValueResult_sub_negInf_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.sub
      IeeeValue.negInf IeeeValue.negInf
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult_of_invalidOperationInput
    ieeePrimitiveInvalidOperationInput_sub_negInf_negInf
theorem ieeeRoundToModeOpValueResult_mul_zero_inf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : IeeeValue} (hx : x.isZero) (hy : y.isInfinite) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.mul x y
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult_of_invalidOperationInput
    (ieeePrimitiveInvalidOperationInput_mul_zero_inf hx hy)
theorem ieeeRoundToModeOpValueResult_mul_inf_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : IeeeValue} (hx : x.isInfinite) (hy : y.isZero) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.mul x y
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult_of_invalidOperationInput
    (ieeePrimitiveInvalidOperationInput_mul_inf_zero hx hy)
theorem ieeeRoundToModeOpValueResult_div_zero_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : IeeeValue} (hx : x.isZero) (hy : y.isZero) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.div x y
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult_of_invalidOperationInput
    (ieeePrimitiveInvalidOperationInput_div_zero_zero hx hy)
theorem ieeeRoundToModeOpValueResult_div_inf_inf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : IeeeValue} (hx : x.isInfinite) (hy : y.isInfinite) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.div x y
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult_of_invalidOperationInput
    (ieeePrimitiveInvalidOperationInput_div_inf_inf hx hy)
theorem ieeeRoundToModeOpValueResult_finite_of_no_value_branch
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hno : ¬ ∃ r, ieeePrimitiveValueBranchResult op
      (IeeeValue.finite x) (IeeeValue.finite y) r) :
    fmt.ieeeRoundToModeOpValueResult mode op
      (IeeeValue.finite x) (IeeeValue.finite y)
      (fmt.ieeeRoundToModeOpResult mode op x y) := by
  exact Or.inr (Or.inr ⟨hno, ⟨x, y, rfl, rfl, rfl⟩⟩)
theorem ieeeRoundToModeOpValueResult_eq_finite_of_finite_no_value_branch
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ} {r : IeeeOperationResult}
    (h : fmt.ieeeRoundToModeOpValueResult mode op
      (IeeeValue.finite x) (IeeeValue.finite y) r)
    (hno : ¬ ∃ r', ieeePrimitiveValueBranchResult op
      (IeeeValue.finite x) (IeeeValue.finite y) r') :
    r = fmt.ieeeRoundToModeOpResult mode op x y := by
  rcases h with hbranch | hmode
  · exact False.elim (hno ⟨r, hbranch⟩)
  · rcases hmode with hzero | hfinite
    · have hzero_absurd :
          ¬ ∃ r', ieeePrimitiveAddSubZeroSumResult mode op
            (IeeeValue.finite x) (IeeeValue.finite y) r' :=
        ieeePrimitiveAddSubZeroSumResult_finite_absurd mode op x y
      exact False.elim (hzero_absurd ⟨r, hzero⟩)
    · rcases hfinite with ⟨_, xr, yr, hx, hy, hr⟩
      cases hx
      cases hy
      exact hr
theorem ieeePrimitiveValueBranchResult_finite_add_absurd
    (x y : ℝ) :
    ¬ ∃ r, ieeePrimitiveValueBranchResult BasicOp.add
      (IeeeValue.finite x) (IeeeValue.finite y) r := by
  intro h
  rcases h with ⟨r, h⟩
  simp [ieeePrimitiveValueBranchResult, ieeePrimitiveSpecialValueResult,
    ieeeQuietNaNPropagationResult, ieeePrimitiveInvalidOperationResult,
    ieeePrimitiveInvalidOperationInput, ieeePrimitiveInfinityPropagationResult,
    ieeePrimitiveFiniteOverInfinityResult,
    ieeePrimitiveAddSubSignedZeroResult,
    ieeePrimitiveAddSubFiniteSignedZeroResult,
    ieeeDivisionByZeroResult, ieeeDivisionByZeroInput,
    IeeeValue.isNaN, IeeeValue.isFinite, IeeeValue.isInfinite,
    IeeeValue.isZero, IeeeValue.isSignedZero,
    IeeeValue.oppositeSignedInfinities] at h
theorem ieeePrimitiveValueBranchResult_finite_sub_absurd
    (x y : ℝ) :
    ¬ ∃ r, ieeePrimitiveValueBranchResult BasicOp.sub
      (IeeeValue.finite x) (IeeeValue.finite y) r := by
  intro h
  rcases h with ⟨r, h⟩
  simp [ieeePrimitiveValueBranchResult, ieeePrimitiveSpecialValueResult,
    ieeeQuietNaNPropagationResult, ieeePrimitiveInvalidOperationResult,
    ieeePrimitiveInvalidOperationInput, ieeePrimitiveInfinityPropagationResult,
    ieeePrimitiveFiniteOverInfinityResult,
    ieeePrimitiveAddSubSignedZeroResult,
    ieeePrimitiveAddSubFiniteSignedZeroResult,
    ieeeDivisionByZeroResult, ieeeDivisionByZeroInput,
    IeeeValue.isNaN, IeeeValue.isFinite, IeeeValue.isInfinite,
    IeeeValue.isZero, IeeeValue.isSignedZero,
    IeeeValue.sameSignedInfinities] at h
theorem ieeePrimitiveValueBranchResult_finite_mul_absurd
    (x y : ℝ) :
    ¬ ∃ r, ieeePrimitiveValueBranchResult BasicOp.mul
      (IeeeValue.finite x) (IeeeValue.finite y) r := by
  intro h
  rcases h with ⟨r, h⟩
  simp [ieeePrimitiveValueBranchResult, ieeePrimitiveSpecialValueResult,
    ieeeQuietNaNPropagationResult, ieeePrimitiveInvalidOperationResult,
    ieeePrimitiveInvalidOperationInput, ieeePrimitiveInfinityPropagationResult,
    ieeePrimitiveMulInfinityPropagationResult, ieeePrimitiveMulInfinityValue,
    ieeePrimitiveMulSignedZeroResult, ieeePrimitiveMulSignedZeroValue,
    ieeePrimitiveFiniteOverInfinityResult,
    ieeePrimitiveAddSubSignedZeroResult,
    ieeePrimitiveAddSubFiniteSignedZeroResult,
    ieeeDivisionByZeroResult, ieeeDivisionByZeroInput,
    IeeeValue.isNaN, IeeeValue.isFinite, IeeeValue.isInfinite,
    IeeeValue.isZero, IeeeValue.isSignedZero, IeeeValue.isPositiveNonzero,
    IeeeValue.isNegativeNonzero] at h
theorem ieeePrimitiveValueBranchResult_finite_div_absurd_of_denominator_ne_zero
    {x y : ℝ} (hy : y ≠ 0) :
    ¬ ∃ r, ieeePrimitiveValueBranchResult BasicOp.div
      (IeeeValue.finite x) (IeeeValue.finite y) r := by
  intro h
  rcases h with ⟨r, h⟩
  simp [ieeePrimitiveValueBranchResult, ieeePrimitiveSpecialValueResult,
    ieeeQuietNaNPropagationResult, ieeePrimitiveInvalidOperationResult,
    ieeePrimitiveInvalidOperationInput, ieeePrimitiveInfinityPropagationResult,
    ieeePrimitiveDivInfinityPropagationResult, ieeePrimitiveDivInfinityValue,
    ieeePrimitiveFiniteOverInfinityResult, ieeePrimitiveFiniteOverInfinityZeroValue,
    ieeePrimitiveAddSubSignedZeroResult,
    ieeePrimitiveAddSubFiniteSignedZeroResult,
    ieeeDivisionByZeroResult, ieeeDivisionByZeroInput,
    IeeeValue.isNaN, IeeeValue.isFinite, IeeeValue.isInfinite,
    IeeeValue.isZero, IeeeValue.isPositiveNonzero,
    IeeeValue.isNegativeNonzero, IeeeValue.isNonnegativeSigned,
    IeeeValue.isNegativeSigned, hy] at h
  rcases h with ⟨value, hvalue, _hr⟩
  exact (by simpa [ieeePrimitiveSignedZeroOverFiniteValue,
    IeeeValue.isSignedZero] using hvalue.1)
theorem ieeePrimitiveValueBranchResult_finite_absurd_of_division_guard
    (op : BasicOp) {x y : ℝ}
    (hdiv : op = BasicOp.div → y ≠ 0) :
    ¬ ∃ r, ieeePrimitiveValueBranchResult op
      (IeeeValue.finite x) (IeeeValue.finite y) r := by
  cases op
  · exact ieeePrimitiveValueBranchResult_finite_add_absurd x y
  · exact ieeePrimitiveValueBranchResult_finite_sub_absurd x y
  · exact ieeePrimitiveValueBranchResult_finite_mul_absurd x y
  · exact
      ieeePrimitiveValueBranchResult_finite_div_absurd_of_denominator_ne_zero
        (hdiv rfl)
theorem ieeePrimitiveValueBranchResult_finite_absurd_of_valueBranchDefault?_none
    {op : BasicOp} {x y : ℝ}
    (hbranch : ieeePrimitiveValueBranchResult? op
      (IeeeValue.finite x) (IeeeValue.finite y) = none) :
    ¬ ∃ r, ieeePrimitiveValueBranchResult op
      (IeeeValue.finite x) (IeeeValue.finite y) r := by
  cases op
  · exact ieeePrimitiveValueBranchResult_finite_add_absurd x y
  · exact ieeePrimitiveValueBranchResult_finite_sub_absurd x y
  · exact ieeePrimitiveValueBranchResult_finite_mul_absurd x y
  · have hy : y ≠ 0 := by
      intro hy
      subst y
      by_cases hxzero : x = 0
      · subst x
        simp [ieeePrimitiveValueBranchResult?_div_finite_zero_finite_zero] at hbranch
      · rcases lt_or_gt_of_ne hxzero with hxneg | hxpos
        · simp [ieeePrimitiveValueBranchResult?_div_finite_neg_finite_zero hxneg] at hbranch
        · simp [ieeePrimitiveValueBranchResult?_div_finite_pos_finite_zero hxpos] at hbranch
    exact ieeePrimitiveValueBranchResult_finite_div_absurd_of_denominator_ne_zero hy
theorem ieeeRoundToModeOpValueResult_finite_add
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (x y : ℝ) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.add
      (IeeeValue.finite x) (IeeeValue.finite y)
      (fmt.ieeeRoundToModeOpResult mode BasicOp.add x y) :=
  fmt.ieeeRoundToModeOpValueResult_finite_of_no_value_branch
    (ieeePrimitiveValueBranchResult_finite_add_absurd x y)
theorem ieeeRoundToModeOpValueResult_finite_sub
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (x y : ℝ) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.sub
      (IeeeValue.finite x) (IeeeValue.finite y)
      (fmt.ieeeRoundToModeOpResult mode BasicOp.sub x y) :=
  fmt.ieeeRoundToModeOpValueResult_finite_of_no_value_branch
    (ieeePrimitiveValueBranchResult_finite_sub_absurd x y)
theorem ieeeRoundToModeOpValueResult_finite_mul
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (x y : ℝ) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.mul
      (IeeeValue.finite x) (IeeeValue.finite y)
      (fmt.ieeeRoundToModeOpResult mode BasicOp.mul x y) :=
  fmt.ieeeRoundToModeOpValueResult_finite_of_no_value_branch
    (ieeePrimitiveValueBranchResult_finite_mul_absurd x y)
theorem ieeeRoundToModeOpValueResult_finite_div_of_denominator_ne_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : ℝ} (hy : y ≠ 0) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.div
      (IeeeValue.finite x) (IeeeValue.finite y)
      (fmt.ieeeRoundToModeOpResult mode BasicOp.div x y) :=
  fmt.ieeeRoundToModeOpValueResult_finite_of_no_value_branch
    (ieeePrimitiveValueBranchResult_finite_div_absurd_of_denominator_ne_zero hy)
/-- Ordinary finite operands enter the finite wrapper branch of the guarded
primitive value dispatch.  Division keeps the visible nonzero-denominator guard
needed to avoid the IEEE division-by-zero branch. -/
theorem ieeeRoundToModeOpValueResult_finite_of_division_guard
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) {x y : ℝ}
    (hdiv : op = BasicOp.div → y ≠ 0) :
    fmt.ieeeRoundToModeOpValueResult mode op
      (IeeeValue.finite x) (IeeeValue.finite y)
      (fmt.ieeeRoundToModeOpResult mode op x y) := by
  cases op
  · exact fmt.ieeeRoundToModeOpValueResult_finite_add mode x y
  · exact fmt.ieeeRoundToModeOpValueResult_finite_sub mode x y
  · exact fmt.ieeeRoundToModeOpValueResult_finite_mul mode x y
  · exact fmt.ieeeRoundToModeOpValueResult_finite_div_of_denominator_ne_zero
      mode (hdiv rfl)
/-- Nearest/even alias for the finite-operand guarded value dispatch. -/
theorem ieeeRoundToNearestEvenOpValueResult_finite_of_division_guard
    (fmt : FloatingPointFormat) (op : BasicOp) {x y : ℝ}
    (hdiv : op = BasicOp.div → y ≠ 0) :
    fmt.ieeeRoundToNearestEvenOpValueResult op
      (IeeeValue.finite x) (IeeeValue.finite y)
      (fmt.ieeeRoundToNearestEvenOpResult op x y) := by
  rw [ieeeRoundToNearestEvenOpValueResult,
    ← fmt.ieeeRoundToModeOpResult_nearestEven op x y]
  exact
    fmt.ieeeRoundToModeOpValueResult_finite_of_division_guard
      IeeeRoundingMode.nearestEven op hdiv
/-- Finite-normal exact primitive results take the guarded value-dispatch finite
branch, raise no flags, and expose the selected finite rounded real value. -/
theorem ieeeRoundToModeOpValueResult_noFlags_toReal?_of_finiteNormalRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y))
    (hdiv : op = BasicOp.div → y ≠ 0) :
    fmt.ieeeRoundToModeOpValueResult mode op
        (IeeeValue.finite x) (IeeeValue.finite y)
        (fmt.ieeeRoundToModeOpResult mode op x y) ∧
      (fmt.ieeeRoundToModeOpResult mode op x y).noFlags ∧
      (fmt.ieeeRoundToModeOpResult mode op x y).value.toReal? =
          some (fmt.finiteRoundToModeOp mode op x y) :=
  ⟨fmt.ieeeRoundToModeOpValueResult_finite_of_division_guard
      mode op hdiv,
    fmt.ieeeRoundToModeOpResult_noFlags_of_finiteNormalRange hxy,
    fmt.ieeeRoundToModeOpResult_toReal?_of_finiteNormalRange hxy⟩
/-- Partial concrete selector for the currently modeled quiet/default
IEEE primitive value-result layer.  If a special-value, division-by-zero, or
mode-aware exact-zero-sum branch is available, it is selected before ordinary
finite rounding.  If no such branch is available and both operands are ordinary
finite payloads, the selector returns the mode-aware finite result wrapper.
Other non-finite cases remain `none`: traps, signaling NaNs, payloads, remaining
special-value operation rules, and a total hardware instruction semantics are
intentionally outside this partial selector. -/
noncomputable def ieeeRoundToModeOpValueResult?
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) (x y : IeeeValue) : Option IeeeOperationResult := by
  classical
  exact
    match ieeePrimitiveValueBranchResult? op x y with
    | some r => some r
    | none =>
        match ieeePrimitiveAddSubZeroSumResult? mode op x y with
        | some r => some r
        | none =>
            match x, y with
            | IeeeValue.finite xr, IeeeValue.finite yr =>
                some (fmt.ieeeRoundToModeOpResult mode op xr yr)
            | _, _ => none
/-- Nearest/even alias for the partial concrete primitive value-result
selector. -/
noncomputable def ieeeRoundToNearestEvenOpValueResult?
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : IeeeValue) :
    Option IeeeOperationResult :=
  fmt.ieeeRoundToModeOpValueResult? IeeeRoundingMode.nearestEven op x y
theorem ieeeRoundToModeOpValueResult?_addSubZeroSumDefault?_of_no_branch
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (hbranch : ieeePrimitiveValueBranchResult? op x y = none)
    (hzero : ieeePrimitiveAddSubZeroSumResult? mode op x y = some r) :
    fmt.ieeeRoundToModeOpValueResult? mode op x y = some r ∧
      ieeePrimitiveAddSubZeroSumResult mode op x y r := by
  exact
    ⟨by simp [ieeeRoundToModeOpValueResult?, hbranch, hzero],
      ieeePrimitiveAddSubZeroSumResult?_sound hzero⟩
theorem ieeeRoundToModeOpValueResult?_add_posZero_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.add
      IeeeValue.posZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) :=
  (fmt.ieeeRoundToModeOpValueResult?_addSubZeroSumDefault?_of_no_branch
    ieeePrimitiveValueBranchResult?_none_add_posZero_negZero
    (ieeePrimitiveAddSubZeroSumResult?_add_posZero_negZero mode)).1
theorem ieeeRoundToModeOpValueResult?_add_negZero_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.add
      IeeeValue.negZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) :=
  (fmt.ieeeRoundToModeOpValueResult?_addSubZeroSumDefault?_of_no_branch
    ieeePrimitiveValueBranchResult?_none_add_negZero_posZero
    (ieeePrimitiveAddSubZeroSumResult?_add_negZero_posZero mode)).1
theorem ieeeRoundToModeOpValueResult?_sub_posZero_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.sub
      IeeeValue.posZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) :=
  (fmt.ieeeRoundToModeOpValueResult?_addSubZeroSumDefault?_of_no_branch
    ieeePrimitiveValueBranchResult?_none_sub_posZero_posZero
    (ieeePrimitiveAddSubZeroSumResult?_sub_posZero_posZero mode)).1
theorem ieeeRoundToModeOpValueResult?_sub_negZero_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.sub
      IeeeValue.negZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) :=
  (fmt.ieeeRoundToModeOpValueResult?_addSubZeroSumDefault?_of_no_branch
    ieeePrimitiveValueBranchResult?_none_sub_negZero_negZero
    (ieeePrimitiveAddSubZeroSumResult?_sub_negZero_negZero mode)).1
/-- Predicate-level IEEE primitive-operation value dispatch whose ordinary
finite branch uses the inexact-aware finite wrapper.  Special-value,
division-by-zero, and mode-aware exact-zero-sum branches take precedence; if no
such value branch applies and both operands are ordinary finite payloads, the
result is the mode-aware finite wrapper that raises the inexact flag exactly
when the selected finite result differs from the exact real result. -/
def ieeeRoundToModeOpInexactAwareValueResult
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) (x y : IeeeValue)
    (r : IeeeOperationResult) : Prop :=
  ieeePrimitiveValueBranchResult op x y r ∨
    ieeePrimitiveAddSubZeroSumResult mode op x y r ∨
      (¬ ∃ r', ieeePrimitiveValueBranchResult op x y r') ∧
        ∃ xr yr : ℝ,
          x = IeeeValue.finite xr ∧ y = IeeeValue.finite yr ∧
            r = fmt.ieeeRoundToModeOpInexactAwareResult mode op xr yr
/-- Nearest/even alias for the inexact-aware primitive-operation value
dispatch predicate. -/
def ieeeRoundToNearestEvenOpInexactAwareValueResult
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : IeeeValue)
    (r : IeeeOperationResult) : Prop :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult
    IeeeRoundingMode.nearestEven op x y r
theorem ieeeRoundToModeOpInexactAwareValueResult_branch
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveValueBranchResult op x y r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode op x y r :=
  Or.inl h
theorem ieeeRoundToModeOpInexactAwareValueResult_addSubZeroSum
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubZeroSumResult mode op x y r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode op x y r :=
  Or.inr (Or.inl h)
theorem ieeeRoundToModeOpInexactAwareValueResult_addSubZeroSumDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubZeroSumResult? mode op x y = some r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode op x y r :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_addSubZeroSum
    (ieeePrimitiveAddSubZeroSumResult?_sound h)
theorem ieeeRoundToModeOpInexactAwareValueResult_quietNaNDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeQuietNaNPropagationResult? x y = some r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode op x y r :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_branch
    (ieeePrimitiveValueBranchResult_quietNaNDefault? h)
theorem ieeeRoundToModeOpInexactAwareValueResult_left_nan
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) (y : IeeeValue) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode op IeeeValue.nan y
      (IeeeOperationResult.valueNoFlags IeeeValue.nan) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_quietNaNDefault? (mode := mode)
    (ieeeQuietNaNPropagationResult?_left_nan y)
theorem ieeeRoundToModeOpInexactAwareValueResult_right_nan
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) (x : IeeeValue) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode op x IeeeValue.nan
      (IeeeOperationResult.valueNoFlags IeeeValue.nan) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_quietNaNDefault? (mode := mode)
    (ieeeQuietNaNPropagationResult?_right_nan x)
theorem ieeeRoundToModeOpInexactAwareValueResult_invalidOperationDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInvalidOperationResult? op x y = some r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode op x y r :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_branch
    (ieeePrimitiveValueBranchResult_invalidOperationDefault? h)
theorem ieeeRoundToModeOpInexactAwareValueResult_of_invalidOperationInput
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue}
    (hinput : ieeePrimitiveInvalidOperationInput op x y) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode op x y
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_branch
    (ieeePrimitiveValueBranchResult_invalidOperationDefault?
      (ieeePrimitiveInvalidOperationResult?_of_input hinput))
theorem ieeeRoundToModeOpInexactAwareValueResult_divisionByZeroDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeDivisionByZeroDefaultResult? x y = some r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.div x y r :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_branch
    (ieeePrimitiveValueBranchResult_divisionByZeroDefault? h)
theorem ieeeRoundToModeOpInexactAwareValueResult_mulSignedZeroDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveMulSignedZeroResult? x y = some r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.mul x y r :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_branch
    (ieeePrimitiveValueBranchResult_mulSignedZeroDefault? h)
theorem ieeeRoundToModeOpInexactAwareValueResult_signedZeroOverFiniteDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveSignedZeroOverFiniteResult? x y = some r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.div x y r :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_branch
    (ieeePrimitiveValueBranchResult_signedZeroOverFiniteDefault? h)
theorem ieeeRoundToModeOpInexactAwareValueResult_addSubSignedZeroDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubSignedZeroResult? op x y = some r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode op x y r :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_branch
    (ieeePrimitiveValueBranchResult_addSubSignedZeroDefault? h)
theorem ieeeRoundToModeOpInexactAwareValueResult_finiteOverInfinityDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveFiniteOverInfinityResult? op x y = some r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode op x y r :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_branch
    (ieeePrimitiveValueBranchResult_finiteOverInfinityDefault? h)
theorem ieeeRoundToModeOpInexactAwareValueResult_addSubFiniteSignedZeroDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubFiniteSignedZeroResult? op x y = some r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode op x y r :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_branch
    (ieeePrimitiveValueBranchResult_addSubFiniteSignedZeroDefault? h)
theorem ieeeRoundToModeOpInexactAwareValueResult_add_negInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.add
      IeeeValue.negInf IeeeValue.posInf
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_of_invalidOperationInput
    ieeePrimitiveInvalidOperationInput_add_negInf_posInf
theorem ieeeRoundToModeOpInexactAwareValueResult_sub_posInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.sub
      IeeeValue.posInf IeeeValue.posInf
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_of_invalidOperationInput
    ieeePrimitiveInvalidOperationInput_sub_posInf_posInf
theorem ieeeRoundToModeOpInexactAwareValueResult_sub_negInf_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.sub
      IeeeValue.negInf IeeeValue.negInf
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_of_invalidOperationInput
    ieeePrimitiveInvalidOperationInput_sub_negInf_negInf
theorem ieeeRoundToModeOpInexactAwareValueResult_mul_zero_inf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : IeeeValue} (hx : x.isZero) (hy : y.isInfinite) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.mul x y
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_of_invalidOperationInput
    (ieeePrimitiveInvalidOperationInput_mul_zero_inf hx hy)
theorem ieeeRoundToModeOpInexactAwareValueResult_mul_inf_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : IeeeValue} (hx : x.isInfinite) (hy : y.isZero) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.mul x y
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_of_invalidOperationInput
    (ieeePrimitiveInvalidOperationInput_mul_inf_zero hx hy)
theorem ieeeRoundToModeOpInexactAwareValueResult_div_zero_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : IeeeValue} (hx : x.isZero) (hy : y.isZero) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.div x y
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_of_invalidOperationInput
    (ieeePrimitiveInvalidOperationInput_div_zero_zero hx hy)
theorem ieeeRoundToModeOpInexactAwareValueResult_div_inf_inf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : IeeeValue} (hx : x.isInfinite) (hy : y.isInfinite) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.div x y
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_of_invalidOperationInput
    (ieeePrimitiveInvalidOperationInput_div_inf_inf hx hy)
theorem ieeeRoundToModeOpInexactAwareValueResult_finite_of_no_value_branch
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hno : ¬ ∃ r, ieeePrimitiveValueBranchResult op
      (IeeeValue.finite x) (IeeeValue.finite y) r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode op
      (IeeeValue.finite x) (IeeeValue.finite y)
      (fmt.ieeeRoundToModeOpInexactAwareResult mode op x y) :=
  Or.inr (Or.inr ⟨hno, x, y, rfl, rfl, rfl⟩)
theorem ieeeRoundToModeOpInexactAwareValueResult_finite_add
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (x y : ℝ) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.add
      (IeeeValue.finite x) (IeeeValue.finite y)
      (fmt.ieeeRoundToModeOpInexactAwareResult mode BasicOp.add x y) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_finite_of_no_value_branch
    (ieeePrimitiveValueBranchResult_finite_add_absurd x y)
theorem ieeeRoundToModeOpInexactAwareValueResult_finite_sub
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (x y : ℝ) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.sub
      (IeeeValue.finite x) (IeeeValue.finite y)
      (fmt.ieeeRoundToModeOpInexactAwareResult mode BasicOp.sub x y) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_finite_of_no_value_branch
    (ieeePrimitiveValueBranchResult_finite_sub_absurd x y)
theorem ieeeRoundToModeOpInexactAwareValueResult_finite_mul
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (x y : ℝ) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.mul
      (IeeeValue.finite x) (IeeeValue.finite y)
      (fmt.ieeeRoundToModeOpInexactAwareResult mode BasicOp.mul x y) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_finite_of_no_value_branch
    (ieeePrimitiveValueBranchResult_finite_mul_absurd x y)
theorem ieeeRoundToModeOpInexactAwareValueResult_finite_div_of_denominator_ne_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : ℝ} (hy : y ≠ 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.div
      (IeeeValue.finite x) (IeeeValue.finite y)
      (fmt.ieeeRoundToModeOpInexactAwareResult mode BasicOp.div x y) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_finite_of_no_value_branch
    (ieeePrimitiveValueBranchResult_finite_div_absurd_of_denominator_ne_zero hy)
theorem ieeeRoundToModeOpInexactAwareValueResult_finite_of_division_guard
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) {x y : ℝ}
    (hdiv : op = BasicOp.div → y ≠ 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode op
      (IeeeValue.finite x) (IeeeValue.finite y)
      (fmt.ieeeRoundToModeOpInexactAwareResult mode op x y) := by
  cases op
  · exact fmt.ieeeRoundToModeOpInexactAwareValueResult_finite_add mode x y
  · exact fmt.ieeeRoundToModeOpInexactAwareValueResult_finite_sub mode x y
  · exact fmt.ieeeRoundToModeOpInexactAwareValueResult_finite_mul mode x y
  · exact
      fmt.ieeeRoundToModeOpInexactAwareValueResult_finite_div_of_denominator_ne_zero
        mode (hdiv rfl)
/-- Partial concrete selector for the currently modeled quiet/default IEEE
primitive value-result layer, using the inexact-aware finite wrapper for
ordinary finite operands. -/
noncomputable def ieeeRoundToModeOpInexactAwareValueResult?
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) (x y : IeeeValue) : Option IeeeOperationResult := by
  classical
  exact
    match ieeePrimitiveValueBranchResult? op x y with
    | some r => some r
    | none =>
        match ieeePrimitiveAddSubZeroSumResult? mode op x y with
        | some r => some r
        | none =>
            match x, y with
            | IeeeValue.finite xr, IeeeValue.finite yr =>
                some (fmt.ieeeRoundToModeOpInexactAwareResult mode op xr yr)
            | _, _ => none
/-- Nearest/even alias for the partial inexact-aware primitive value-result
selector. -/
noncomputable def ieeeRoundToNearestEvenOpInexactAwareValueResult?
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : IeeeValue) :
    Option IeeeOperationResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?
    IeeeRoundingMode.nearestEven op x y
theorem ieeeRoundToModeOpInexactAwareValueResult?_addSubZeroSumDefault?_of_no_branch
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (hbranch : ieeePrimitiveValueBranchResult? op x y = none)
    (hzero : ieeePrimitiveAddSubZeroSumResult? mode op x y = some r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode op x y =
        some r ∧
      ieeePrimitiveAddSubZeroSumResult mode op x y r := by
  exact
    ⟨by simp [ieeeRoundToModeOpInexactAwareValueResult?, hbranch, hzero],
      ieeePrimitiveAddSubZeroSumResult?_sound hzero⟩
theorem ieeeRoundToModeOpInexactAwareValueResult?_add_posZero_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.add
      IeeeValue.posZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_addSubZeroSumDefault?_of_no_branch
    ieeePrimitiveValueBranchResult?_none_add_posZero_negZero
    (ieeePrimitiveAddSubZeroSumResult?_add_posZero_negZero mode)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_add_negZero_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.add
      IeeeValue.negZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_addSubZeroSumDefault?_of_no_branch
    ieeePrimitiveValueBranchResult?_none_add_negZero_posZero
    (ieeePrimitiveAddSubZeroSumResult?_add_negZero_posZero mode)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_sub_posZero_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.sub
      IeeeValue.posZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_addSubZeroSumDefault?_of_no_branch
    ieeePrimitiveValueBranchResult?_none_sub_posZero_posZero
    (ieeePrimitiveAddSubZeroSumResult?_sub_posZero_posZero mode)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_sub_negZero_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.sub
      IeeeValue.negZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_addSubZeroSumDefault?_of_no_branch
    ieeePrimitiveValueBranchResult?_none_sub_negZero_negZero
    (ieeePrimitiveAddSubZeroSumResult?_sub_negZero_negZero mode)).1
theorem ieeeRoundToModeOpResult_ieeeUnderflowModeResult_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteUnderflowRange (BasicOp.exact op x y)) :
    fmt.ieeeUnderflowModeResult mode (BasicOp.exact op x y)
      (fmt.finiteRoundToModeOp mode op x y)
      (fmt.ieeeRoundToModeOpResult mode op x y) := by
  classical
  have hover : ¬ fmt.finiteOverflowRange (BasicOp.exact op x y) := by
    intro hover
    have hle := fmt.minNormalMagnitude_le_maxFiniteMagnitude
    rw [finiteUnderflowRange] at hxy
    rw [finiteOverflowRange] at hover
    linarith
  simpa [ieeeRoundToModeOpResult, hover, hxy] using
    (fmt.ieeeUnderflowDefaultResult_ieeeUnderflowModeResult
      hxy
      (fmt.finiteRoundToModeOp_ieeeUnderflowModeRoundingEvidence_of_finiteUnderflowRange
        (mode := mode) hxy))
theorem ieeeRoundTowardZeroOpResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteOverflowRange (BasicOp.exact op x y)) :
    fmt.ieeeOverflowResult IeeeRoundingMode.towardZero
      (BasicOp.exact op x y)
      (fmt.ieeeRoundTowardZeroOpResult op x y) := by
  simpa [ieeeRoundTowardZeroOpResult] using
    (fmt.ieeeRoundToModeOpResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := IeeeRoundingMode.towardZero) hxy)
theorem ieeeRoundTowardPositiveOpResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteOverflowRange (BasicOp.exact op x y)) :
    fmt.ieeeOverflowResult IeeeRoundingMode.towardPositive
      (BasicOp.exact op x y)
      (fmt.ieeeRoundTowardPositiveOpResult op x y) := by
  simpa [ieeeRoundTowardPositiveOpResult] using
    (fmt.ieeeRoundToModeOpResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := IeeeRoundingMode.towardPositive) hxy)
theorem ieeeRoundTowardNegativeOpResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteOverflowRange (BasicOp.exact op x y)) :
    fmt.ieeeOverflowResult IeeeRoundingMode.towardNegative
      (BasicOp.exact op x y)
      (fmt.ieeeRoundTowardNegativeOpResult op x y) := by
  simpa [ieeeRoundTowardNegativeOpResult] using
    (fmt.ieeeRoundToModeOpResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := IeeeRoundingMode.towardNegative) hxy)
/-- IEEE-facing nearest/even finite-normal primitive-operation branch with the
strict standard-model value equation exposed through `toReal?`. -/
theorem ieeeRoundToNearestEvenOpResult_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        (fmt.ieeeRoundToNearestEvenOpResult op x y).noFlags ∧
          (fmt.ieeeRoundToNearestEvenOpResult op x y).value.toReal? =
            some (BasicOp.exact op x y * (1 + δ)) := by
  rcases
    fmt.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      hxy with
    ⟨δ, hδ, hmodel⟩
  exact
    ⟨δ, hδ,
      fmt.ieeeRoundToNearestEvenOpResult_noFlags_of_finiteNormalRange hxy,
      by
        rw [fmt.ieeeRoundToNearestEvenOpResult_toReal?_of_finiteNormalRange hxy,
          hmodel]⟩
/-- Guarded `IeeeValue` primitive-operation dispatch for ordinary finite
operands in the nearest/even finite-normal standard-model branch.  This exposes
the value-dispatch predicate together with the no-flag and strict
standard-model value facts; division keeps the visible nonzero-denominator
guard that excludes the division-by-zero branch. -/
theorem ieeeRoundToNearestEvenOpValueResult_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y))
    (hdiv : op = BasicOp.div → y ≠ 0) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        fmt.ieeeRoundToNearestEvenOpValueResult op
          (IeeeValue.finite x) (IeeeValue.finite y)
          (fmt.ieeeRoundToNearestEvenOpResult op x y) ∧
          (fmt.ieeeRoundToNearestEvenOpResult op x y).noFlags ∧
            (fmt.ieeeRoundToNearestEvenOpResult op x y).value.toReal? =
              some (BasicOp.exact op x y * (1 + δ)) := by
  rcases
    fmt.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      hxy with
    ⟨δ, hδ, hmodel⟩
  exact
    ⟨δ, hδ,
      fmt.ieeeRoundToNearestEvenOpValueResult_finite_of_division_guard
        op hdiv,
      fmt.ieeeRoundToNearestEvenOpResult_noFlags_of_finiteNormalRange hxy,
      by
        rw [fmt.ieeeRoundToNearestEvenOpResult_toReal?_of_finiteNormalRange hxy,
          hmodel]⟩
/-- IEEE-facing finite/no-flags wrapper for the source-facing finite square-root
selector. -/
noncomputable def finiteRoundToEvenSqrtIeeeFiniteResult
    (fmt : FloatingPointFormat) (x : ℝ) : IeeeOperationResult :=
  IeeeOperationResult.finiteNoFlags (fmt.finiteRoundToEvenSqrt x)
theorem finiteRoundToEvenSqrtIeeeFiniteResult_isFinite
    (fmt : FloatingPointFormat) (x : ℝ) :
    (fmt.finiteRoundToEvenSqrtIeeeFiniteResult x).isFinite :=
  IeeeOperationResult.finiteNoFlags_isFinite _
theorem finiteRoundToEvenSqrtIeeeFiniteResult_noFlags
    (fmt : FloatingPointFormat) (x : ℝ) :
    (fmt.finiteRoundToEvenSqrtIeeeFiniteResult x).noFlags :=
  IeeeOperationResult.finiteNoFlags_noFlags _
theorem finiteRoundToEvenSqrtIeeeFiniteResult_toReal?
    (fmt : FloatingPointFormat) (x : ℝ) :
    (fmt.finiteRoundToEvenSqrtIeeeFiniteResult x).value.toReal? =
      some (fmt.finiteRoundToEvenSqrt x) :=
  IeeeOperationResult.finiteNoFlags_toReal? _
/-- IEEE-facing nearest/even square-root wrapper for the real-valued square
root reference on nonnegative inputs, with the IEEE invalid-operation/NaN
branch for negative inputs.  For nonnegative inputs, `Real.sqrt x` is the exact
real quantity being rounded.  Overflow and underflow of that exact result
dispatch to the corresponding flagged IEEE-facing result; ordinary finite
results use the finite/no-flags source-facing square-root wrapper. -/
noncomputable def ieeeRoundToNearestEvenSqrtResult
    (fmt : FloatingPointFormat) (x : ℝ) : IeeeOperationResult := by
  classical
  exact
    if x < 0 then
      ieeeSqrtInvalidDefaultResult x
    else
      let exact := Real.sqrt x
      let rounded := fmt.finiteRoundToEvenSqrt x
      if fmt.finiteOverflowRange exact then
        fmt.ieeeOverflowDefaultResult IeeeRoundingMode.nearestEven exact
      else if fmt.finiteUnderflowRange exact then
        fmt.ieeeUnderflowDefaultResult exact rounded
      else
        IeeeOperationResult.finiteNoFlags rounded
theorem ieeeRoundToNearestEvenSqrtResult_ieeeSqrtInvalidResult_of_neg
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : x < 0) :
    ieeeSqrtInvalidResult x (fmt.ieeeRoundToNearestEvenSqrtResult x) := by
  classical
  simpa [ieeeRoundToNearestEvenSqrtResult, hx] using
    (ieeeSqrtInvalidDefaultResult_ieeeSqrtInvalidResult hx)
theorem ieeeRoundToNearestEvenSqrtResult_ieeeInvalidOperationResult_of_neg
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : x < 0) :
    ieeeInvalidOperationResult
      (fmt.ieeeRoundToNearestEvenSqrtResult x) :=
  (fmt.ieeeRoundToNearestEvenSqrtResult_ieeeSqrtInvalidResult_of_neg hx).2
theorem ieeeRoundToNearestEvenSqrtResult_value_of_neg
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : x < 0) :
    (fmt.ieeeRoundToNearestEvenSqrtResult x).value = IeeeValue.nan :=
  ieeeInvalidOperationResult_value
    (fmt.ieeeRoundToNearestEvenSqrtResult_ieeeInvalidOperationResult_of_neg hx)
theorem ieeeRoundToNearestEvenSqrtResult_hasInvalidOperationFlag_of_neg
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : x < 0) :
    (fmt.ieeeRoundToNearestEvenSqrtResult x).hasFlag
      IeeeExceptionFlag.invalidOperation :=
  ieeeInvalidOperationResult_hasInvalidOperationFlag
    (fmt.ieeeRoundToNearestEvenSqrtResult_ieeeInvalidOperationResult_of_neg hx)
theorem ieeeRoundToNearestEvenSqrtResult_toReal?_of_neg
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : x < 0) :
    (fmt.ieeeRoundToNearestEvenSqrtResult x).value.toReal? = none := by
  rw [fmt.ieeeRoundToNearestEvenSqrtResult_value_of_neg hx]
  rfl
theorem ieeeRoundToNearestEvenSqrtResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteOverflowRange (Real.sqrt x)) :
    fmt.ieeeOverflowResult IeeeRoundingMode.nearestEven (Real.sqrt x)
      (fmt.ieeeRoundToNearestEvenSqrtResult x) := by
  classical
  have hnot : ¬ x < 0 := not_lt.mpr hx_nonneg
  simpa [ieeeRoundToNearestEvenSqrtResult, hnot, hsqrt] using
    (fmt.ieeeOverflowDefaultResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := IeeeRoundingMode.nearestEven) hsqrt)
theorem ieeeRoundToNearestEvenSqrtResult_noFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hover : ¬ fmt.finiteOverflowRange (Real.sqrt x))
    (hunder : ¬ fmt.finiteUnderflowRange (Real.sqrt x)) :
    (fmt.ieeeRoundToNearestEvenSqrtResult x).noFlags := by
  classical
  have hnot : ¬ x < 0 := not_lt.mpr hx_nonneg
  simpa [ieeeRoundToNearestEvenSqrtResult, hnot, hover, hunder] using
    (IeeeOperationResult.finiteNoFlags_noFlags
      (fmt.finiteRoundToEvenSqrt x))
theorem ieeeRoundToNearestEvenSqrtResult_toReal?_of_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : ¬ fmt.finiteOverflowRange (Real.sqrt x)) :
    (fmt.ieeeRoundToNearestEvenSqrtResult x).value.toReal? =
      some (fmt.finiteRoundToEvenSqrt x) := by
  classical
  have hnot : ¬ x < 0 := not_lt.mpr hx_nonneg
  by_cases hunder : fmt.finiteUnderflowRange (Real.sqrt x)
  · simpa [ieeeRoundToNearestEvenSqrtResult, hnot, hsqrt, hunder] using
      (fmt.ieeeUnderflowDefaultResult_toReal? (Real.sqrt x)
        (fmt.finiteRoundToEvenSqrt x))
  · simpa [ieeeRoundToNearestEvenSqrtResult, hnot, hsqrt, hunder] using
      (IeeeOperationResult.finiteNoFlags_toReal?
        (fmt.finiteRoundToEvenSqrt x))
/-- Finite-normal exact square-root results take the nearest/even finite/no-flags
IEEE wrapper branch. -/
theorem ieeeRoundToNearestEvenSqrtResult_eq_finiteNoFlags_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    fmt.ieeeRoundToNearestEvenSqrtResult x =
      IeeeOperationResult.finiteNoFlags (fmt.finiteRoundToEvenSqrt x) := by
  classical
  have hnot : ¬ x < 0 := not_lt.mpr hx_nonneg
  simp [ieeeRoundToNearestEvenSqrtResult, hnot,
    fmt.finiteNormalRange_not_finiteOverflowRange hsqrt,
    fmt.finiteNormalRange_not_finiteUnderflowRange hsqrt]
/-- Finite-normal exact square-root results do not raise IEEE flags in the
nearest/even source-facing sqrt wrapper. -/
theorem ieeeRoundToNearestEvenSqrtResult_noFlags_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    (fmt.ieeeRoundToNearestEvenSqrtResult x).noFlags := by
  rw [fmt.ieeeRoundToNearestEvenSqrtResult_eq_finiteNoFlags_of_finiteNormalRange
    hx_nonneg hsqrt]
  exact IeeeOperationResult.finiteNoFlags_noFlags _
/-- Finite-normal exact square-root results expose the finite round-to-even
sqrt value in the nearest/even IEEE wrapper. -/
theorem ieeeRoundToNearestEvenSqrtResult_toReal?_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    (fmt.ieeeRoundToNearestEvenSqrtResult x).value.toReal? =
      some (fmt.finiteRoundToEvenSqrt x) := by
  rw [fmt.ieeeRoundToNearestEvenSqrtResult_eq_finiteNoFlags_of_finiteNormalRange
    hx_nonneg hsqrt]
  exact IeeeOperationResult.finiteNoFlags_toReal? _
/-- IEEE-facing nearest/even finite-normal square-root branch with the strict
standard-model value equation exposed through `toReal?`. -/
theorem ieeeRoundToNearestEvenSqrtResult_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        (fmt.ieeeRoundToNearestEvenSqrtResult x).noFlags ∧
          (fmt.ieeeRoundToNearestEvenSqrtResult x).value.toReal? =
            some (Real.sqrt x * (1 + δ)) := by
  rcases
    fmt.finiteRoundToEvenSqrt_standardModel_lt_of_finiteNormalRange
      hx_nonneg hsqrt with
    ⟨δ, hδ, hmodel⟩
  exact
    ⟨δ, hδ,
      fmt.ieeeRoundToNearestEvenSqrtResult_noFlags_of_finiteNormalRange
        hx_nonneg hsqrt,
      by
        rw [fmt.ieeeRoundToNearestEvenSqrtResult_toReal?_of_finiteNormalRange
          hx_nonneg hsqrt, hmodel]⟩
theorem ieeeRoundToNearestEvenSqrtResult_ieeeUnderflowResult_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteUnderflowRange (Real.sqrt x)) :
    fmt.ieeeUnderflowResult (Real.sqrt x)
      (fmt.finiteRoundToEvenSqrt x)
      (fmt.ieeeRoundToNearestEvenSqrtResult x) := by
  classical
  have hnot : ¬ x < 0 := not_lt.mpr hx_nonneg
  have hover : ¬ fmt.finiteOverflowRange (Real.sqrt x) := by
    intro hover
    have hle := fmt.minNormalMagnitude_le_maxFiniteMagnitude
    rw [finiteUnderflowRange] at hsqrt
    rw [finiteOverflowRange] at hover
    linarith
  simpa [ieeeRoundToNearestEvenSqrtResult, hnot, hover, hsqrt] using
    (fmt.ieeeUnderflowDefaultResult_ieeeUnderflowResult
      hsqrt (fmt.finiteRoundToEvenSqrt_nearestRoundingToFinite x))
/-- IEEE-facing square-root wrapper parameterized by an IEEE rounding mode.
The negative real-input branch is invalid-operation/NaN for every mode.  For
nonnegative real inputs, overflow uses the IEEE mode-dependent overflow table
and finite underflow/no-flag branches use the finite selector for the same
mode. -/
noncomputable def ieeeRoundToModeSqrtResult
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    IeeeOperationResult := by
  classical
  exact
    if x < 0 then
      ieeeSqrtInvalidDefaultResult x
    else
      let exact := Real.sqrt x
      let rounded := fmt.finiteRoundToModeSqrt mode x
      if fmt.finiteOverflowRange exact then
        fmt.ieeeOverflowDefaultResult mode exact
      else if fmt.finiteUnderflowRange exact then
        fmt.ieeeUnderflowDefaultResult exact rounded
      else
        IeeeOperationResult.finiteNoFlags rounded
/-- Directed-mode alias for square root rounded toward zero. -/
noncomputable def ieeeRoundTowardZeroSqrtResult
    (fmt : FloatingPointFormat) (x : ℝ) : IeeeOperationResult :=
  fmt.ieeeRoundToModeSqrtResult IeeeRoundingMode.towardZero x
/-- Directed-mode alias for square root rounded toward positive infinity. -/
noncomputable def ieeeRoundTowardPositiveSqrtResult
    (fmt : FloatingPointFormat) (x : ℝ) : IeeeOperationResult :=
  fmt.ieeeRoundToModeSqrtResult IeeeRoundingMode.towardPositive x
/-- Directed-mode alias for square root rounded toward negative infinity. -/
noncomputable def ieeeRoundTowardNegativeSqrtResult
    (fmt : FloatingPointFormat) (x : ℝ) : IeeeOperationResult :=
  fmt.ieeeRoundToModeSqrtResult IeeeRoundingMode.towardNegative x
theorem ieeeRoundToModeSqrtResult_nearestEven
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.ieeeRoundToModeSqrtResult IeeeRoundingMode.nearestEven x =
      fmt.ieeeRoundToNearestEvenSqrtResult x := by
  classical
  rfl
theorem ieeeRoundToModeSqrtResult_ieeeSqrtInvalidResult_of_neg
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx : x < 0) :
    ieeeSqrtInvalidResult x (fmt.ieeeRoundToModeSqrtResult mode x) := by
  classical
  simpa [ieeeRoundToModeSqrtResult, hx] using
    (ieeeSqrtInvalidDefaultResult_ieeeSqrtInvalidResult hx)
theorem ieeeRoundToModeSqrtResult_ieeeInvalidOperationResult_of_neg
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx : x < 0) :
    ieeeInvalidOperationResult
      (fmt.ieeeRoundToModeSqrtResult mode x) :=
  (fmt.ieeeRoundToModeSqrtResult_ieeeSqrtInvalidResult_of_neg
    (mode := mode) hx).2
theorem ieeeRoundToModeSqrtResult_value_of_neg
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx : x < 0) :
    (fmt.ieeeRoundToModeSqrtResult mode x).value = IeeeValue.nan :=
  ieeeInvalidOperationResult_value
    (fmt.ieeeRoundToModeSqrtResult_ieeeInvalidOperationResult_of_neg
      (mode := mode) hx)
theorem ieeeRoundToModeSqrtResult_hasInvalidOperationFlag_of_neg
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx : x < 0) :
    (fmt.ieeeRoundToModeSqrtResult mode x).hasFlag
      IeeeExceptionFlag.invalidOperation :=
  ieeeInvalidOperationResult_hasInvalidOperationFlag
    (fmt.ieeeRoundToModeSqrtResult_ieeeInvalidOperationResult_of_neg
      (mode := mode) hx)
theorem ieeeRoundToModeSqrtResult_toReal?_of_neg
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx : x < 0) :
    (fmt.ieeeRoundToModeSqrtResult mode x).value.toReal? = none := by
  rw [fmt.ieeeRoundToModeSqrtResult_value_of_neg (mode := mode) hx]
  rfl
theorem ieeeRoundToModeSqrtResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteOverflowRange (Real.sqrt x)) :
    fmt.ieeeOverflowResult mode (Real.sqrt x)
      (fmt.ieeeRoundToModeSqrtResult mode x) := by
  classical
  have hnot : ¬ x < 0 := not_lt.mpr hx_nonneg
  simpa [ieeeRoundToModeSqrtResult, hnot, hsqrt] using
    (fmt.ieeeOverflowDefaultResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := mode) hsqrt)
theorem ieeeRoundToModeSqrtResult_eq_finiteNoFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hover : ¬ fmt.finiteOverflowRange (Real.sqrt x))
    (hunder : ¬ fmt.finiteUnderflowRange (Real.sqrt x)) :
    fmt.ieeeRoundToModeSqrtResult mode x =
      IeeeOperationResult.finiteNoFlags
        (fmt.finiteRoundToModeSqrt mode x) := by
  classical
  have hnot : ¬ x < 0 := not_lt.mpr hx_nonneg
  simp [ieeeRoundToModeSqrtResult, hnot, hover, hunder]
theorem ieeeRoundToModeSqrtResult_noFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hover : ¬ fmt.finiteOverflowRange (Real.sqrt x))
    (hunder : ¬ fmt.finiteUnderflowRange (Real.sqrt x)) :
    (fmt.ieeeRoundToModeSqrtResult mode x).noFlags := by
  rw [
    fmt.ieeeRoundToModeSqrtResult_eq_finiteNoFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
      hx_nonneg hover hunder]
  exact IeeeOperationResult.finiteNoFlags_noFlags _
theorem ieeeRoundToModeSqrtResult_toReal?_of_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : ¬ fmt.finiteOverflowRange (Real.sqrt x)) :
    (fmt.ieeeRoundToModeSqrtResult mode x).value.toReal? =
      some (fmt.finiteRoundToModeSqrt mode x) := by
  classical
  have hnot : ¬ x < 0 := not_lt.mpr hx_nonneg
  by_cases hunder : fmt.finiteUnderflowRange (Real.sqrt x)
  · simpa [ieeeRoundToModeSqrtResult, hnot, hsqrt, hunder] using
      (fmt.ieeeUnderflowDefaultResult_toReal? (Real.sqrt x)
        (fmt.finiteRoundToModeSqrt mode x))
  · simpa [ieeeRoundToModeSqrtResult, hnot, hsqrt, hunder] using
      (IeeeOperationResult.finiteNoFlags_toReal?
        (fmt.finiteRoundToModeSqrt mode x))
/-- Finite-normal exact square-root results take the finite/no-flags branch for
any source-facing IEEE rounding mode wrapper. -/
theorem ieeeRoundToModeSqrtResult_eq_finiteNoFlags_of_finiteNormalRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    fmt.ieeeRoundToModeSqrtResult mode x =
      IeeeOperationResult.finiteNoFlags
        (fmt.finiteRoundToModeSqrt mode x) := by
  exact
    fmt.ieeeRoundToModeSqrtResult_eq_finiteNoFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
      hx_nonneg
      (fmt.finiteNormalRange_not_finiteOverflowRange hsqrt)
      (fmt.finiteNormalRange_not_finiteUnderflowRange hsqrt)
/-- Finite-normal exact square-root results do not raise IEEE flags for any
source-facing rounding mode wrapper. -/
theorem ieeeRoundToModeSqrtResult_noFlags_of_finiteNormalRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    (fmt.ieeeRoundToModeSqrtResult mode x).noFlags := by
  rw [fmt.ieeeRoundToModeSqrtResult_eq_finiteNoFlags_of_finiteNormalRange
    hx_nonneg hsqrt]
  exact IeeeOperationResult.finiteNoFlags_noFlags _
/-- Finite-normal exact square-root results expose the selected finite rounded
sqrt value for any source-facing IEEE rounding mode wrapper. -/
theorem ieeeRoundToModeSqrtResult_toReal?_of_finiteNormalRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    (fmt.ieeeRoundToModeSqrtResult mode x).value.toReal? =
      some (fmt.finiteRoundToModeSqrt mode x) := by
  rw [fmt.ieeeRoundToModeSqrtResult_eq_finiteNoFlags_of_finiteNormalRange
    hx_nonneg hsqrt]
  exact IeeeOperationResult.finiteNoFlags_toReal? _
theorem ieeeRoundToModeSqrtResult_ieeeUnderflowModeResult_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteUnderflowRange (Real.sqrt x)) :
    fmt.ieeeUnderflowModeResult mode (Real.sqrt x)
      (fmt.finiteRoundToModeSqrt mode x)
      (fmt.ieeeRoundToModeSqrtResult mode x) := by
  classical
  have hnot : ¬ x < 0 := not_lt.mpr hx_nonneg
  have hover : ¬ fmt.finiteOverflowRange (Real.sqrt x) := by
    intro hover
    have hle := fmt.minNormalMagnitude_le_maxFiniteMagnitude
    rw [finiteUnderflowRange] at hsqrt
    rw [finiteOverflowRange] at hover
    linarith
  simpa [ieeeRoundToModeSqrtResult, hnot, hover, hsqrt] using
    (fmt.ieeeUnderflowDefaultResult_ieeeUnderflowModeResult
      hsqrt
      (fmt.finiteRoundToModeSqrt_ieeeUnderflowModeRoundingEvidence_of_finiteUnderflowRange
        (mode := mode) hsqrt))
theorem ieeeRoundTowardZeroSqrtResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteOverflowRange (Real.sqrt x)) :
    fmt.ieeeOverflowResult IeeeRoundingMode.towardZero (Real.sqrt x)
      (fmt.ieeeRoundTowardZeroSqrtResult x) := by
  simpa [ieeeRoundTowardZeroSqrtResult] using
    (fmt.ieeeRoundToModeSqrtResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := IeeeRoundingMode.towardZero) hx_nonneg hsqrt)
theorem ieeeRoundTowardPositiveSqrtResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteOverflowRange (Real.sqrt x)) :
    fmt.ieeeOverflowResult IeeeRoundingMode.towardPositive (Real.sqrt x)
      (fmt.ieeeRoundTowardPositiveSqrtResult x) := by
  simpa [ieeeRoundTowardPositiveSqrtResult] using
    (fmt.ieeeRoundToModeSqrtResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := IeeeRoundingMode.towardPositive) hx_nonneg hsqrt)
theorem ieeeRoundTowardNegativeSqrtResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteOverflowRange (Real.sqrt x)) :
    fmt.ieeeOverflowResult IeeeRoundingMode.towardNegative (Real.sqrt x)
      (fmt.ieeeRoundTowardNegativeSqrtResult x) := by
  simpa [ieeeRoundTowardNegativeSqrtResult] using
    (fmt.ieeeRoundToModeSqrtResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := IeeeRoundingMode.towardNegative) hx_nonneg hsqrt)
/-- IEEE-facing nearest/even square-root wrapper over IEEE values.  Finite
payloads use the real-input wrapper above; non-finite special values take the
first explicit Chapter 2 special-value branches. -/
noncomputable def ieeeRoundToNearestEvenSqrtValueResult
    (fmt : FloatingPointFormat) : IeeeValue → IeeeOperationResult
  | IeeeValue.finite x => fmt.ieeeRoundToNearestEvenSqrtResult x
  | IeeeValue.posZero => IeeeOperationResult.valueNoFlags IeeeValue.posZero
  | IeeeValue.negZero => IeeeOperationResult.valueNoFlags IeeeValue.negZero
  | IeeeValue.posInf => IeeeOperationResult.valueNoFlags IeeeValue.posInf
  | IeeeValue.negInf => ieeeInvalidOperationDefaultResult
  | IeeeValue.nan => IeeeOperationResult.valueNoFlags IeeeValue.nan
theorem ieeeRoundToNearestEvenSqrtValueResult_finite
    {fmt : FloatingPointFormat} (x : ℝ) :
    fmt.ieeeRoundToNearestEvenSqrtValueResult (IeeeValue.finite x) =
      fmt.ieeeRoundToNearestEvenSqrtResult x := rfl
theorem ieeeRoundToNearestEvenSqrtValueResult_nan_special
    {fmt : FloatingPointFormat} :
    ieeeSqrtSpecialValueResult IeeeValue.nan
      (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.nan) :=
  ieeeSqrtSpecialValueResult_nan_valueNoFlags
theorem ieeeRoundToNearestEvenSqrtValueResult_posZero_signedZero
    {fmt : FloatingPointFormat} :
    ieeeSqrtSignedZeroResult IeeeValue.posZero
      (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.posZero) :=
  ieeeSqrtSignedZeroResult_posZero_valueNoFlags
theorem ieeeRoundToNearestEvenSqrtValueResult_negZero_signedZero
    {fmt : FloatingPointFormat} :
    ieeeSqrtSignedZeroResult IeeeValue.negZero
      (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.negZero) :=
  ieeeSqrtSignedZeroResult_negZero_valueNoFlags
theorem ieeeRoundToNearestEvenSqrtValueResult_posInf_special
    {fmt : FloatingPointFormat} :
    ieeeSqrtSpecialValueResult IeeeValue.posInf
      (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.posInf) :=
  ieeeSqrtSpecialValueResult_posInf_valueNoFlags
theorem ieeeRoundToNearestEvenSqrtValueResult_negInf_special
    {fmt : FloatingPointFormat} :
    ieeeSqrtSpecialValueResult IeeeValue.negInf
      (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.negInf) :=
  ieeeSqrtSpecialValueResult_negInf_invalid
theorem ieeeRoundToNearestEvenSqrtValueResult_nan_value
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.nan).value =
      IeeeValue.nan :=
  ieeeSqrtSpecialValueResult_value_nan
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_nan_special)
theorem ieeeRoundToNearestEvenSqrtValueResult_nan_noFlags
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.nan).noFlags :=
  ieeeSqrtSpecialValueResult_noFlags_nan
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_nan_special)
theorem ieeeRoundToNearestEvenSqrtValueResult_posZero_value
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.posZero).value =
      IeeeValue.posZero :=
  ieeeSqrtSignedZeroResult_value_posZero
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_posZero_signedZero)
theorem ieeeRoundToNearestEvenSqrtValueResult_posZero_noFlags
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.posZero).noFlags :=
  ieeeSqrtSignedZeroResult_noFlags_posZero
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_posZero_signedZero)
theorem ieeeRoundToNearestEvenSqrtValueResult_posZero_toReal?
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.posZero).value.toReal? =
      some 0 := by
  rw [fmt.ieeeRoundToNearestEvenSqrtValueResult_posZero_value]
  rfl
theorem ieeeRoundToNearestEvenSqrtValueResult_negZero_value
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.negZero).value =
      IeeeValue.negZero :=
  ieeeSqrtSignedZeroResult_value_negZero
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_negZero_signedZero)
theorem ieeeRoundToNearestEvenSqrtValueResult_negZero_noFlags
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.negZero).noFlags :=
  ieeeSqrtSignedZeroResult_noFlags_negZero
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_negZero_signedZero)
theorem ieeeRoundToNearestEvenSqrtValueResult_negZero_toReal?
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.negZero).value.toReal? =
      some 0 := by
  rw [fmt.ieeeRoundToNearestEvenSqrtValueResult_negZero_value]
  rfl
theorem ieeeRoundToNearestEvenSqrtValueResult_posInf_value
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.posInf).value =
      IeeeValue.posInf :=
  ieeeSqrtSpecialValueResult_value_posInf
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_posInf_special)
theorem ieeeRoundToNearestEvenSqrtValueResult_posInf_noFlags
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.posInf).noFlags :=
  ieeeSqrtSpecialValueResult_noFlags_posInf
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_posInf_special)
theorem ieeeRoundToNearestEvenSqrtValueResult_negInf_ieeeInvalidOperationResult
    {fmt : FloatingPointFormat} :
    ieeeInvalidOperationResult
      (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.negInf) :=
  ieeeSqrtSpecialValueResult_negInf_ieeeInvalidOperationResult
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_negInf_special)
theorem ieeeRoundToNearestEvenSqrtValueResult_negInf_value
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.negInf).value =
      IeeeValue.nan :=
  ieeeInvalidOperationResult_value
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_negInf_ieeeInvalidOperationResult)
theorem ieeeRoundToNearestEvenSqrtValueResult_negInf_hasInvalidOperationFlag
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.negInf).hasFlag
      IeeeExceptionFlag.invalidOperation :=
  ieeeInvalidOperationResult_hasInvalidOperationFlag
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_negInf_ieeeInvalidOperationResult)
/-- Mode-parameterized IEEE square-root value wrapper.  Finite real payloads
use the existing real-input mode wrapper, signed zeros preserve their sign, and
the currently modeled non-finite branches are independent of the rounding mode.
This remains a quiet/default layer: traps, signaling-NaN payloads, and a
complete hardware instruction semantics are not modeled here. -/
noncomputable def ieeeRoundToModeSqrtValueResult
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    IeeeValue → IeeeOperationResult
  | IeeeValue.finite x => fmt.ieeeRoundToModeSqrtResult mode x
  | IeeeValue.posZero => IeeeOperationResult.valueNoFlags IeeeValue.posZero
  | IeeeValue.negZero => IeeeOperationResult.valueNoFlags IeeeValue.negZero
  | IeeeValue.posInf => IeeeOperationResult.valueNoFlags IeeeValue.posInf
  | IeeeValue.negInf => ieeeInvalidOperationDefaultResult
  | IeeeValue.nan => IeeeOperationResult.valueNoFlags IeeeValue.nan
/-- Directed-mode value alias for square root rounded toward zero. -/
noncomputable def ieeeRoundTowardZeroSqrtValueResult
    (fmt : FloatingPointFormat) : IeeeValue → IeeeOperationResult :=
  fmt.ieeeRoundToModeSqrtValueResult IeeeRoundingMode.towardZero
/-- Directed-mode value alias for square root rounded toward positive
infinity. -/
noncomputable def ieeeRoundTowardPositiveSqrtValueResult
    (fmt : FloatingPointFormat) : IeeeValue → IeeeOperationResult :=
  fmt.ieeeRoundToModeSqrtValueResult IeeeRoundingMode.towardPositive
/-- Directed-mode value alias for square root rounded toward negative
infinity. -/
noncomputable def ieeeRoundTowardNegativeSqrtValueResult
    (fmt : FloatingPointFormat) : IeeeValue → IeeeOperationResult :=
  fmt.ieeeRoundToModeSqrtValueResult IeeeRoundingMode.towardNegative
theorem ieeeRoundToModeSqrtValueResult_nearestEven
    (fmt : FloatingPointFormat) (v : IeeeValue) :
    fmt.ieeeRoundToModeSqrtValueResult IeeeRoundingMode.nearestEven v =
      fmt.ieeeRoundToNearestEvenSqrtValueResult v := by
  cases v <;> rfl
theorem ieeeRoundToModeSqrtValueResult_finite
    {fmt : FloatingPointFormat} (mode : IeeeRoundingMode) (x : ℝ) :
    fmt.ieeeRoundToModeSqrtValueResult mode (IeeeValue.finite x) =
      fmt.ieeeRoundToModeSqrtResult mode x := rfl
theorem ieeeRoundToModeSqrtValueResult_nan_special
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} :
    ieeeSqrtSpecialValueResult IeeeValue.nan
      (fmt.ieeeRoundToModeSqrtValueResult mode IeeeValue.nan) :=
  ieeeSqrtSpecialValueResult_nan_valueNoFlags
theorem ieeeRoundToModeSqrtValueResult_posZero_signedZero
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} :
    ieeeSqrtSignedZeroResult IeeeValue.posZero
      (fmt.ieeeRoundToModeSqrtValueResult mode IeeeValue.posZero) :=
  ieeeSqrtSignedZeroResult_posZero_valueNoFlags
theorem ieeeRoundToModeSqrtValueResult_negZero_signedZero
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} :
    ieeeSqrtSignedZeroResult IeeeValue.negZero
      (fmt.ieeeRoundToModeSqrtValueResult mode IeeeValue.negZero) :=
  ieeeSqrtSignedZeroResult_negZero_valueNoFlags
theorem ieeeRoundToModeSqrtValueResult_posInf_special
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} :
    ieeeSqrtSpecialValueResult IeeeValue.posInf
      (fmt.ieeeRoundToModeSqrtValueResult mode IeeeValue.posInf) :=
  ieeeSqrtSpecialValueResult_posInf_valueNoFlags
theorem ieeeRoundToModeSqrtValueResult_negInf_special
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} :
    ieeeSqrtSpecialValueResult IeeeValue.negInf
      (fmt.ieeeRoundToModeSqrtValueResult mode IeeeValue.negInf) :=
  ieeeSqrtSpecialValueResult_negInf_invalid
theorem ieeeRoundToModeSqrtValueResult_nan_value
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} :
    (fmt.ieeeRoundToModeSqrtValueResult mode IeeeValue.nan).value =
      IeeeValue.nan :=
  ieeeSqrtSpecialValueResult_value_nan
    (fmt.ieeeRoundToModeSqrtValueResult_nan_special)
theorem ieeeRoundToModeSqrtValueResult_nan_noFlags
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} :
    (fmt.ieeeRoundToModeSqrtValueResult mode IeeeValue.nan).noFlags :=
  ieeeSqrtSpecialValueResult_noFlags_nan
    (fmt.ieeeRoundToModeSqrtValueResult_nan_special)
theorem ieeeRoundToModeSqrtValueResult_posZero_value
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} :
    (fmt.ieeeRoundToModeSqrtValueResult mode IeeeValue.posZero).value =
      IeeeValue.posZero :=
  ieeeSqrtSignedZeroResult_value_posZero
    (fmt.ieeeRoundToModeSqrtValueResult_posZero_signedZero)
theorem ieeeRoundToModeSqrtValueResult_posZero_noFlags
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} :
    (fmt.ieeeRoundToModeSqrtValueResult mode IeeeValue.posZero).noFlags :=
  ieeeSqrtSignedZeroResult_noFlags_posZero
    (fmt.ieeeRoundToModeSqrtValueResult_posZero_signedZero)
theorem ieeeRoundToModeSqrtValueResult_posZero_toReal?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} :
    (fmt.ieeeRoundToModeSqrtValueResult mode IeeeValue.posZero).value.toReal? =
      some 0 := by
  rw [fmt.ieeeRoundToModeSqrtValueResult_posZero_value]
  rfl
theorem ieeeRoundToModeSqrtValueResult_negZero_value
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} :
    (fmt.ieeeRoundToModeSqrtValueResult mode IeeeValue.negZero).value =
      IeeeValue.negZero :=
  ieeeSqrtSignedZeroResult_value_negZero
    (fmt.ieeeRoundToModeSqrtValueResult_negZero_signedZero)
theorem ieeeRoundToModeSqrtValueResult_negZero_noFlags
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} :
    (fmt.ieeeRoundToModeSqrtValueResult mode IeeeValue.negZero).noFlags :=
  ieeeSqrtSignedZeroResult_noFlags_negZero
    (fmt.ieeeRoundToModeSqrtValueResult_negZero_signedZero)
theorem ieeeRoundToModeSqrtValueResult_negZero_toReal?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} :
    (fmt.ieeeRoundToModeSqrtValueResult mode IeeeValue.negZero).value.toReal? =
      some 0 := by
  rw [fmt.ieeeRoundToModeSqrtValueResult_negZero_value]
  rfl
theorem ieeeRoundToModeSqrtValueResult_posInf_value
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} :
    (fmt.ieeeRoundToModeSqrtValueResult mode IeeeValue.posInf).value =
      IeeeValue.posInf :=
  ieeeSqrtSpecialValueResult_value_posInf
    (fmt.ieeeRoundToModeSqrtValueResult_posInf_special)
theorem ieeeRoundToModeSqrtValueResult_posInf_noFlags
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} :
    (fmt.ieeeRoundToModeSqrtValueResult mode IeeeValue.posInf).noFlags :=
  ieeeSqrtSpecialValueResult_noFlags_posInf
    (fmt.ieeeRoundToModeSqrtValueResult_posInf_special)
theorem ieeeRoundToModeSqrtValueResult_negInf_ieeeInvalidOperationResult
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} :
    ieeeInvalidOperationResult
      (fmt.ieeeRoundToModeSqrtValueResult mode IeeeValue.negInf) :=
  ieeeSqrtSpecialValueResult_negInf_ieeeInvalidOperationResult
    (fmt.ieeeRoundToModeSqrtValueResult_negInf_special)
theorem ieeeRoundToModeSqrtValueResult_negInf_value
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} :
    (fmt.ieeeRoundToModeSqrtValueResult mode IeeeValue.negInf).value =
      IeeeValue.nan :=
  ieeeInvalidOperationResult_value
    (fmt.ieeeRoundToModeSqrtValueResult_negInf_ieeeInvalidOperationResult)
theorem ieeeRoundToModeSqrtValueResult_negInf_hasInvalidOperationFlag
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} :
    (fmt.ieeeRoundToModeSqrtValueResult mode IeeeValue.negInf).hasFlag
      IeeeExceptionFlag.invalidOperation :=
  ieeeInvalidOperationResult_hasInvalidOperationFlag
    (fmt.ieeeRoundToModeSqrtValueResult_negInf_ieeeInvalidOperationResult)
/-- Concrete selector for the currently modeled mode-aware IEEE square-root
value wrapper.  This is total over the repository's quiet/default `IeeeValue`
wrapper; it is not a complete hardware instruction semantics with traps,
signaling-NaN payloads, or environment state. -/
noncomputable def ieeeRoundToModeSqrtValueResult?
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (x : IeeeValue) : Option IeeeOperationResult :=
  some (fmt.ieeeRoundToModeSqrtValueResult mode x)
/-- Nearest/even selector alias for the modeled IEEE square-root value wrapper. -/
noncomputable def ieeeRoundToNearestEvenSqrtValueResult?
    (fmt : FloatingPointFormat) (x : IeeeValue) :
    Option IeeeOperationResult :=
  fmt.ieeeRoundToModeSqrtValueResult? IeeeRoundingMode.nearestEven x
theorem ieeeRoundToModeSqrtValueResult?_eq_some
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : IeeeValue) :
    fmt.ieeeRoundToModeSqrtValueResult? mode x =
      some (fmt.ieeeRoundToModeSqrtValueResult mode x) :=
  rfl
theorem ieeeRoundToModeSqrtValueResult?_finite
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    fmt.ieeeRoundToModeSqrtValueResult? mode (IeeeValue.finite x) =
      some (fmt.ieeeRoundToModeSqrtResult mode x) :=
  rfl
theorem ieeeRoundToModeSqrtValueResult?_nan
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeSqrtValueResult? mode IeeeValue.nan =
      some (IeeeOperationResult.valueNoFlags IeeeValue.nan) :=
  rfl
theorem ieeeRoundToModeSqrtValueResult?_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeSqrtValueResult? mode IeeeValue.posZero =
      some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  rfl
theorem ieeeRoundToModeSqrtValueResult?_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeSqrtValueResult? mode IeeeValue.negZero =
      some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  rfl
theorem ieeeRoundToModeSqrtValueResult?_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeSqrtValueResult? mode IeeeValue.posInf =
      some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  rfl
theorem ieeeRoundToModeSqrtValueResult?_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeSqrtValueResult? mode IeeeValue.negInf =
      some ieeeInvalidOperationDefaultResult :=
  rfl
theorem ieeeRoundToModeSqrtValueResult?_sound
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {x : IeeeValue} {r : IeeeOperationResult}
    (h : fmt.ieeeRoundToModeSqrtValueResult? mode x = some r) :
    r = fmt.ieeeRoundToModeSqrtValueResult mode x := by
  simpa [ieeeRoundToModeSqrtValueResult?] using h.symm
theorem ieeeRoundToNearestEvenSqrtValueResult?_eq_some
    (fmt : FloatingPointFormat) (x : IeeeValue) :
    fmt.ieeeRoundToNearestEvenSqrtValueResult? x =
      some (fmt.ieeeRoundToNearestEvenSqrtValueResult x) := by
  rw [ieeeRoundToNearestEvenSqrtValueResult?]
  rw [ieeeRoundToModeSqrtValueResult?_eq_some]
  rw [ieeeRoundToModeSqrtValueResult_nearestEven]
theorem ieeeRoundToNearestEvenSqrtValueResult?_sound
    {fmt : FloatingPointFormat} {x : IeeeValue} {r : IeeeOperationResult}
    (h : fmt.ieeeRoundToNearestEvenSqrtValueResult? x = some r) :
    r = fmt.ieeeRoundToNearestEvenSqrtValueResult x := by
  have hs :
      r = fmt.ieeeRoundToModeSqrtValueResult IeeeRoundingMode.nearestEven x :=
    ieeeRoundToModeSqrtValueResult?_sound
      (fmt := fmt) (mode := IeeeRoundingMode.nearestEven) (x := x) h
  simpa [ieeeRoundToModeSqrtValueResult_nearestEven] using hs
/-- Finite-normal finite inputs take the mode-aware finite square-root branch
through the value wrapper, raise no flags, and expose the selected finite
rounded real value. -/
theorem ieeeRoundToModeSqrtValueResult_noFlags_toReal?_of_finiteNormalRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx_nonneg : 0 ≤ x) (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    (fmt.ieeeRoundToModeSqrtValueResult mode (IeeeValue.finite x)).noFlags ∧
      (fmt.ieeeRoundToModeSqrtValueResult mode
          (IeeeValue.finite x)).value.toReal? =
        some (fmt.finiteRoundToModeSqrt mode x) := by
  change
    (fmt.ieeeRoundToModeSqrtResult mode x).noFlags ∧
      (fmt.ieeeRoundToModeSqrtResult mode x).value.toReal? =
        some (fmt.finiteRoundToModeSqrt mode x)
  exact
    ⟨fmt.ieeeRoundToModeSqrtResult_noFlags_of_finiteNormalRange
        hx_nonneg hsqrt,
      fmt.ieeeRoundToModeSqrtResult_toReal?_of_finiteNormalRange
        hx_nonneg hsqrt⟩
/-- Nearest/even finite-normal finite inputs inherit the strict standard-model
square-root value equation through the value wrapper. -/
theorem ieeeRoundToNearestEvenSqrtValueResult_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x) (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        (fmt.ieeeRoundToNearestEvenSqrtValueResult
          (IeeeValue.finite x)).noFlags ∧
          (fmt.ieeeRoundToNearestEvenSqrtValueResult
            (IeeeValue.finite x)).value.toReal? =
            some (Real.sqrt x * (1 + δ)) := by
  change
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        (fmt.ieeeRoundToNearestEvenSqrtResult x).noFlags ∧
          (fmt.ieeeRoundToNearestEvenSqrtResult x).value.toReal? =
            some (Real.sqrt x * (1 + δ))
  exact
    fmt.ieeeRoundToNearestEvenSqrtResult_standardModel_lt_of_finiteNormalRange
      hx_nonneg hsqrt

end FloatingPointFormat

end

end NumStability
