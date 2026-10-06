import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace NumStability

/-!
# IeeeValue

Extracted without change from FloatingPointArithmetic.
-/

noncomputable section

/-- IEEE rounding-direction vocabulary from Chapter 2's IEEE discussion.  The
source-facing finite selectors below currently implement only nearest/even as a
real-valued finite policy; the other modes are named so future IEEE semantics
do not hide a directed-rounding assumption. -/
inductive IeeeRoundingMode where
  | nearestEven
  | towardZero
  | towardPositive
  | towardNegative
  deriving DecidableEq, Repr
/-- IEEE exception-flag vocabulary from Chapter 2. -/
inductive IeeeExceptionFlag where
  | invalidOperation
  | divisionByZero
  | overflow
  | underflow
  | inexact
  deriving DecidableEq, Repr
/-- IEEE-facing scalar result vocabulary.  This separates real finite results
from infinities and NaNs, unlike the source-facing finite selectors that always
return real numbers. -/
inductive IeeeValue where
  | finite (x : ℝ)
  | posZero
  | negZero
  | posInf
  | negInf
  | nan
/-- Four-way IEEE comparison classification for the modeled quiet/default
value layer.  This records the ordinary unordered/less/equal/greater split; it
does not model signaling-NaN traps or payload behavior. -/
inductive IeeeComparisonClass where
  | unordered
  | less
  | equal
  | greater
  deriving DecidableEq, Repr
namespace IeeeRoundingMode

/-- IEEE's signed-zero result for an exact zero sum.  Round toward negative
infinity selects `-0`; the other modeled modes select `+0`. -/
def zeroSumSignedZeroValue : IeeeRoundingMode → IeeeValue
  | towardNegative => IeeeValue.negZero
  | nearestEven => IeeeValue.posZero
  | towardZero => IeeeValue.posZero
  | towardPositive => IeeeValue.posZero
@[simp] theorem zeroSumSignedZeroValue_nearestEven :
    zeroSumSignedZeroValue IeeeRoundingMode.nearestEven = IeeeValue.posZero := rfl
@[simp] theorem zeroSumSignedZeroValue_towardZero :
    zeroSumSignedZeroValue IeeeRoundingMode.towardZero = IeeeValue.posZero := rfl
@[simp] theorem zeroSumSignedZeroValue_towardPositive :
    zeroSumSignedZeroValue IeeeRoundingMode.towardPositive = IeeeValue.posZero := rfl
@[simp] theorem zeroSumSignedZeroValue_towardNegative :
    zeroSumSignedZeroValue IeeeRoundingMode.towardNegative = IeeeValue.negZero := rfl
end IeeeRoundingMode

namespace IeeeValue

/-- Predicate that an IEEE-facing value is an ordinary finite real. -/
def isFinite : IeeeValue → Prop
  | finite _ => True
  | posZero => True
  | negZero => True
  | posInf => False
  | negInf => False
  | nan => False
/-- Predicate for the IEEE NaN value.  This does not distinguish quiet from
signaling NaNs or preserve payloads. -/
def isNaN : IeeeValue → Prop
  | nan => True
  | _ => False
/-- Predicate for IEEE infinities. -/
def isInfinite : IeeeValue → Prop
  | posInf => True
  | negInf => True
  | _ => False
/-- Predicate for IEEE zero values.  The ordinary finite value `0` and the
signed zero values all count as zero for invalid-operation examples such as
`0/0` and `0 * infinity`. -/
def isZero : IeeeValue → Prop
  | finite x => x = 0
  | posZero => True
  | negZero => True
  | _ => False
/-- Predicate for IEEE signed-zero values.  The ordinary modeled finite value
`finite 0` is intentionally not a signed zero; it is treated as the local
positive-zero default only by sign-class predicates. -/
def isSignedZero : IeeeValue → Prop
  | posZero => True
  | negZero => True
  | _ => False
/-- Positive nonzero IEEE-facing values for sign-sensitive special-value
branches.  This includes positive finite reals and positive infinity, and
excludes all zeros, negative values, and NaNs. -/
def isPositiveNonzero : IeeeValue → Prop
  | finite x => 0 < x
  | posInf => True
  | _ => False
/-- Negative nonzero IEEE-facing values for sign-sensitive special-value
branches.  This includes negative finite reals and negative infinity, and
excludes all zeros, positive values, and NaNs. -/
def isNegativeNonzero : IeeeValue → Prop
  | finite x => x < 0
  | negInf => True
  | _ => False
/-- IEEE-facing nonnegative sign class for signed-zero result rules.  The
ordinary modeled `finite 0` carries no sign bit, so this predicate treats it as
the local positive-zero default. -/
def isNonnegativeSigned : IeeeValue → Prop
  | finite x => 0 ≤ x
  | posZero => True
  | posInf => True
  | _ => False
/-- IEEE-facing negative sign class for signed-zero result rules. -/
def isNegativeSigned : IeeeValue → Prop
  | finite x => x < 0
  | negZero => True
  | negInf => True
  | _ => False
/-- Two IEEE-facing values are the same signed infinity. -/
def sameSignedInfinities (x y : IeeeValue) : Prop :=
  (x = IeeeValue.posInf ∧ y = IeeeValue.posInf) ∨
    (x = IeeeValue.negInf ∧ y = IeeeValue.negInf)
/-- Two IEEE-facing values are opposite signed infinities. -/
def oppositeSignedInfinities (x y : IeeeValue) : Prop :=
  (x = IeeeValue.posInf ∧ y = IeeeValue.negInf) ∨
    (x = IeeeValue.negInf ∧ y = IeeeValue.posInf)
/-- IEEE unordered comparison predicate.  In the modeled quiet/default layer,
unordered means that at least one operand is the modeled NaN value. -/
def ieeeUnordered (x y : IeeeValue) : Prop :=
  x.isNaN ∨ y.isNaN
/-- IEEE equality predicate for the modeled value layer.  NaNs are unequal to
everything, including themselves; signed zeros compare equal. -/
def ieeeEq : IeeeValue → IeeeValue → Prop
  | nan, _ => False
  | _, nan => False
  | finite x, finite y => x = y
  | finite x, posZero => x = 0
  | finite x, negZero => x = 0
  | posZero, finite y => y = 0
  | negZero, finite y => y = 0
  | posZero, posZero => True
  | posZero, negZero => True
  | negZero, posZero => True
  | negZero, negZero => True
  | posInf, posInf => True
  | negInf, negInf => True
  | _, _ => False
/-- IEEE less-than predicate for the modeled value layer.  NaNs are unordered
and hence not less than anything; signed zeros compare equal. -/
def ieeeLt : IeeeValue → IeeeValue → Prop
  | nan, _ => False
  | _, nan => False
  | negInf, negInf => False
  | negInf, _ => True
  | _, negInf => False
  | posInf, _ => False
  | _, posInf => True
  | finite x, finite y => x < y
  | finite x, posZero => x < 0
  | finite x, negZero => x < 0
  | posZero, finite y => 0 < y
  | negZero, finite y => 0 < y
  | posZero, posZero => False
  | posZero, negZero => False
  | negZero, posZero => False
  | negZero, negZero => False
/-- IEEE greater-than predicate, defined by reversing less-than. -/
def ieeeGt (x y : IeeeValue) : Prop :=
  ieeeLt y x
/-- Concrete four-way comparison selector for the modeled quiet/default IEEE
value layer.  NaNs are classified as unordered, signed zeros compare equal, and
otherwise the real/infinity order predicates determine the result. -/
def ieeeCompareClass (x y : IeeeValue) : IeeeComparisonClass := by
  classical
  exact
    if x.ieeeUnordered y then IeeeComparisonClass.unordered
    else if x.ieeeLt y then IeeeComparisonClass.less
    else if x.ieeeEq y then IeeeComparisonClass.equal
    else IeeeComparisonClass.greater
/-- Extract the real payload of a finite IEEE-facing value. -/
def toReal? : IeeeValue → Option ℝ
  | finite x => some x
  | posZero => some 0
  | negZero => some 0
  | posInf => none
  | negInf => none
  | nan => none
theorem finite_isFinite (x : ℝ) :
    (IeeeValue.finite x).isFinite := by
  simp [isFinite]
theorem posZero_isFinite :
    IeeeValue.posZero.isFinite := by
  simp [isFinite]
theorem negZero_isFinite :
    IeeeValue.negZero.isFinite := by
  simp [isFinite]
theorem nan_isNaN :
    IeeeValue.nan.isNaN := by
  simp [isNaN]
theorem posInf_isInfinite :
    IeeeValue.posInf.isInfinite := by
  simp [isInfinite]
theorem negInf_isInfinite :
    IeeeValue.negInf.isInfinite := by
  simp [isInfinite]
theorem finite_zero_isZero :
    (IeeeValue.finite 0).isZero := by
  simp [isZero]
theorem posZero_isZero :
    IeeeValue.posZero.isZero := by
  simp [isZero]
theorem negZero_isZero :
    IeeeValue.negZero.isZero := by
  simp [isZero]
theorem posZero_isSignedZero :
    IeeeValue.posZero.isSignedZero := by
  simp [isSignedZero]
theorem negZero_isSignedZero :
    IeeeValue.negZero.isSignedZero := by
  simp [isSignedZero]
theorem finite_pos_isPositiveNonzero
    {x : ℝ} (hx : 0 < x) :
    (IeeeValue.finite x).isPositiveNonzero := by
  simpa [isPositiveNonzero] using hx
theorem finite_neg_isNegativeNonzero
    {x : ℝ} (hx : x < 0) :
    (IeeeValue.finite x).isNegativeNonzero := by
  simpa [isNegativeNonzero] using hx
theorem posInf_isPositiveNonzero :
    IeeeValue.posInf.isPositiveNonzero := by
  simp [isPositiveNonzero]
theorem negInf_isNegativeNonzero :
    IeeeValue.negInf.isNegativeNonzero := by
  simp [isNegativeNonzero]
theorem finite_nonneg_isNonnegativeSigned
    {x : ℝ} (hx : 0 ≤ x) :
    (IeeeValue.finite x).isNonnegativeSigned := by
  simpa [isNonnegativeSigned] using hx
theorem finite_zero_isNonnegativeSigned :
    (IeeeValue.finite 0).isNonnegativeSigned := by
  simp [isNonnegativeSigned]
theorem finite_pos_isNonnegativeSigned
    {x : ℝ} (hx : 0 < x) :
    (IeeeValue.finite x).isNonnegativeSigned :=
  finite_nonneg_isNonnegativeSigned (le_of_lt hx)
theorem finite_neg_isNegativeSigned
    {x : ℝ} (hx : x < 0) :
    (IeeeValue.finite x).isNegativeSigned := by
  simpa [isNegativeSigned] using hx
theorem posZero_isNonnegativeSigned :
    IeeeValue.posZero.isNonnegativeSigned := by
  simp [isNonnegativeSigned]
theorem negZero_isNegativeSigned :
    IeeeValue.negZero.isNegativeSigned := by
  simp [isNegativeSigned]
theorem posInf_isNonnegativeSigned :
    IeeeValue.posInf.isNonnegativeSigned := by
  simp [isNonnegativeSigned]
theorem negInf_isNegativeSigned :
    IeeeValue.negInf.isNegativeSigned := by
  simp [isNegativeSigned]
theorem isPositiveNonzero_not_isZero
    {x : IeeeValue} (hx : x.isPositiveNonzero) :
    ¬ x.isZero := by
  cases x <;> simp [isPositiveNonzero, isZero] at hx ⊢
  exact ne_of_gt hx
theorem isNegativeNonzero_not_isZero
    {x : IeeeValue} (hx : x.isNegativeNonzero) :
    ¬ x.isZero := by
  cases x <;> simp [isNegativeNonzero, isZero] at hx ⊢
  exact ne_of_lt hx
theorem ieeeUnordered_left_nan
    (y : IeeeValue) :
    IeeeValue.ieeeUnordered IeeeValue.nan y := by
  exact Or.inl IeeeValue.nan_isNaN
theorem ieeeUnordered_right_nan
    (x : IeeeValue) :
    IeeeValue.ieeeUnordered x IeeeValue.nan := by
  exact Or.inr IeeeValue.nan_isNaN
theorem ieeeUnordered_nan_self :
    IeeeValue.ieeeUnordered IeeeValue.nan IeeeValue.nan := by
  exact ieeeUnordered_left_nan IeeeValue.nan
theorem not_ieeeEq_left_nan
    (y : IeeeValue) :
    ¬ IeeeValue.ieeeEq IeeeValue.nan y := by
  cases y <;> simp [ieeeEq]
theorem not_ieeeEq_right_nan
    (x : IeeeValue) :
    ¬ IeeeValue.ieeeEq x IeeeValue.nan := by
  cases x <;> simp [ieeeEq]
theorem not_ieeeEq_nan_self :
    ¬ IeeeValue.ieeeEq IeeeValue.nan IeeeValue.nan := by
  simp [ieeeEq]
theorem not_ieeeEq_self_iff_isNaN
    (x : IeeeValue) :
    ¬ IeeeValue.ieeeEq x x ↔ x.isNaN := by
  cases x <;> simp [ieeeEq, isNaN]
theorem not_ieeeLt_left_nan
    (y : IeeeValue) :
    ¬ IeeeValue.ieeeLt IeeeValue.nan y := by
  cases y <;> simp [ieeeLt]
theorem not_ieeeLt_right_nan
    (x : IeeeValue) :
    ¬ IeeeValue.ieeeLt x IeeeValue.nan := by
  cases x <;> simp [ieeeLt]
theorem not_ieeeGt_left_nan
    (y : IeeeValue) :
    ¬ IeeeValue.ieeeGt IeeeValue.nan y :=
  not_ieeeLt_right_nan y
theorem not_ieeeGt_right_nan
    (x : IeeeValue) :
    ¬ IeeeValue.ieeeGt x IeeeValue.nan :=
  not_ieeeLt_left_nan x
theorem ieeeEq_posZero_negZero :
    IeeeValue.ieeeEq IeeeValue.posZero IeeeValue.negZero := by
  simp [ieeeEq]
theorem ieeeEq_negZero_posZero :
    IeeeValue.ieeeEq IeeeValue.negZero IeeeValue.posZero := by
  simp [ieeeEq]
theorem ieeeEq_self_of_not_isNaN
    {x : IeeeValue} (hx : ¬ x.isNaN) :
    x.ieeeEq x := by
  cases x <;> simp [ieeeEq, isNaN] at hx ⊢
theorem not_ieeeLt_self
    (x : IeeeValue) :
    ¬ x.ieeeLt x := by
  cases x <;> simp [ieeeLt]
theorem not_ieeeGt_self
    (x : IeeeValue) :
    ¬ x.ieeeGt x := by
  simpa [ieeeGt] using not_ieeeLt_self x
theorem ieeeComparison_complete
    (x y : IeeeValue) :
    x.ieeeUnordered y ∨ x.ieeeLt y ∨ x.ieeeEq y ∨ x.ieeeGt y := by
  cases x with
  | finite a =>
      cases y with
      | finite b =>
          simpa [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
            using (lt_trichotomy a b)
      | posZero =>
          simpa [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
            using (lt_trichotomy a (0 : ℝ))
      | negZero =>
          simpa [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
            using (lt_trichotomy a (0 : ℝ))
      | posInf => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | negInf => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | nan => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
  | posZero =>
      cases y with
      | finite b =>
          simpa [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt, eq_comm]
            using (lt_trichotomy (0 : ℝ) b)
      | posZero => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | negZero => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | posInf => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | negInf => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | nan => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
  | negZero =>
      cases y with
      | finite b =>
          simpa [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt, eq_comm]
            using (lt_trichotomy (0 : ℝ) b)
      | posZero => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | negZero => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | posInf => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | negInf => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | nan => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
  | posInf =>
      cases y <;> simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
  | negInf =>
      cases y <;> simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
  | nan =>
      cases y <;> simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
theorem ieeeComparison_ordered_of_not_unordered
    {x y : IeeeValue} (h : ¬ x.ieeeUnordered y) :
    x.ieeeLt y ∨ x.ieeeEq y ∨ x.ieeeGt y := by
  rcases ieeeComparison_complete x y with hunordered | hordered
  · exact False.elim (h hunordered)
  · exact hordered
theorem ieeeCompareClass_unordered
    {x y : IeeeValue} (h : x.ieeeUnordered y) :
    x.ieeeCompareClass y = IeeeComparisonClass.unordered := by
  simp [ieeeCompareClass, h]
theorem ieeeCompareClass_less
    {x y : IeeeValue} (hunordered : ¬ x.ieeeUnordered y)
    (hlt : x.ieeeLt y) :
    x.ieeeCompareClass y = IeeeComparisonClass.less := by
  simp [ieeeCompareClass, hunordered, hlt]
theorem ieeeCompareClass_equal
    {x y : IeeeValue} (hunordered : ¬ x.ieeeUnordered y)
    (hlt : ¬ x.ieeeLt y) (heq : x.ieeeEq y) :
    x.ieeeCompareClass y = IeeeComparisonClass.equal := by
  simp [ieeeCompareClass, hunordered, hlt, heq]
theorem ieeeCompareClass_greater
    {x y : IeeeValue} (hunordered : ¬ x.ieeeUnordered y)
    (hlt : ¬ x.ieeeLt y) (heq : ¬ x.ieeeEq y) :
    x.ieeeCompareClass y = IeeeComparisonClass.greater := by
  simp [ieeeCompareClass, hunordered, hlt, heq]
theorem ieeeCompareClass_unordered_sound
    {x y : IeeeValue}
    (h : x.ieeeCompareClass y = IeeeComparisonClass.unordered) :
    x.ieeeUnordered y := by
  classical
  by_cases hunordered : x.ieeeUnordered y
  · exact hunordered
  · by_cases hlt : x.ieeeLt y
    · simp [ieeeCompareClass, hunordered, hlt] at h
    · by_cases heq : x.ieeeEq y
      · simp [ieeeCompareClass, hunordered, hlt, heq] at h
      · simp [ieeeCompareClass, hunordered, hlt, heq] at h
theorem ieeeCompareClass_less_sound
    {x y : IeeeValue}
    (h : x.ieeeCompareClass y = IeeeComparisonClass.less) :
    x.ieeeLt y := by
  classical
  by_cases hunordered : x.ieeeUnordered y
  · simp [ieeeCompareClass, hunordered] at h
  · by_cases hlt : x.ieeeLt y
    · exact hlt
    · by_cases heq : x.ieeeEq y
      · simp [ieeeCompareClass, hunordered, hlt, heq] at h
      · simp [ieeeCompareClass, hunordered, hlt, heq] at h
theorem ieeeCompareClass_equal_sound
    {x y : IeeeValue}
    (h : x.ieeeCompareClass y = IeeeComparisonClass.equal) :
    x.ieeeEq y := by
  classical
  by_cases hunordered : x.ieeeUnordered y
  · simp [ieeeCompareClass, hunordered] at h
  · by_cases hlt : x.ieeeLt y
    · simp [ieeeCompareClass, hunordered, hlt] at h
    · by_cases heq : x.ieeeEq y
      · exact heq
      · simp [ieeeCompareClass, hunordered, hlt, heq] at h
theorem ieeeCompareClass_greater_sound
    {x y : IeeeValue}
    (h : x.ieeeCompareClass y = IeeeComparisonClass.greater) :
    x.ieeeGt y := by
  classical
  by_cases hunordered : x.ieeeUnordered y
  · simp [ieeeCompareClass, hunordered] at h
  · by_cases hlt : x.ieeeLt y
    · simp [ieeeCompareClass, hunordered, hlt] at h
    · by_cases heq : x.ieeeEq y
      · simp [ieeeCompareClass, hunordered, hlt, heq] at h
      · rcases ieeeComparison_ordered_of_not_unordered hunordered with hlt' | heq_or_gt
        · exact False.elim (hlt hlt')
        · rcases heq_or_gt with heq' | hgt
          · exact False.elim (heq heq')
          · exact hgt
theorem ieeeCompareClass_nan_left
    (y : IeeeValue) :
    IeeeValue.nan.ieeeCompareClass y = IeeeComparisonClass.unordered :=
  ieeeCompareClass_unordered (ieeeUnordered_left_nan y)
theorem ieeeCompareClass_nan_right
    (x : IeeeValue) :
    x.ieeeCompareClass IeeeValue.nan = IeeeComparisonClass.unordered :=
  ieeeCompareClass_unordered (ieeeUnordered_right_nan x)
theorem ieeeCompareClass_posZero_negZero :
    IeeeValue.posZero.ieeeCompareClass IeeeValue.negZero =
      IeeeComparisonClass.equal := by
  simp [ieeeCompareClass, ieeeUnordered, isNaN, ieeeLt, ieeeEq]
theorem ieeeCompareClass_finite_lt
    {x y : ℝ} (hxy : x < y) :
    (IeeeValue.finite x).ieeeCompareClass (IeeeValue.finite y) =
      IeeeComparisonClass.less := by
  simp [ieeeCompareClass, ieeeUnordered, isNaN, ieeeLt, hxy]
theorem ieeeCompareClass_finite_eq
    {x y : ℝ} (hxy : x = y) :
    (IeeeValue.finite x).ieeeCompareClass (IeeeValue.finite y) =
      IeeeComparisonClass.equal := by
  subst y
  simp [ieeeCompareClass, ieeeUnordered, isNaN, ieeeLt, ieeeEq]
theorem ieeeCompareClass_finite_gt
    {x y : ℝ} (hyx : y < x) :
    (IeeeValue.finite x).ieeeCompareClass (IeeeValue.finite y) =
      IeeeComparisonClass.greater := by
  have hnot_lt : ¬ x < y := not_lt.mpr (le_of_lt hyx)
  have hne : x ≠ y := Ne.symm (ne_of_lt hyx)
  simp [ieeeCompareClass, ieeeUnordered, isNaN, ieeeLt, ieeeEq, hnot_lt, hne]
theorem toReal?_finite (x : ℝ) :
    (IeeeValue.finite x).toReal? = some x := rfl
theorem toReal?_posZero :
    IeeeValue.posZero.toReal? = some 0 := rfl
theorem toReal?_negZero :
    IeeeValue.negZero.toReal? = some 0 := rfl
theorem isFinite_iff_exists {v : IeeeValue} :
    v.isFinite ↔
      (∃ x : ℝ, v = IeeeValue.finite x) ∨
        v = IeeeValue.posZero ∨ v = IeeeValue.negZero := by
  cases v <;> simp [isFinite]
end IeeeValue

/-- IEEE-facing operation result: a value together with the exception flags
raised by the operation.  Flags are a predicate so later semantics can state
sets of flags without committing now to a bit-vector representation. -/
structure IeeeOperationResult where
  value : IeeeValue
  flag : IeeeExceptionFlag → Prop
namespace IeeeOperationResult

/-- The finite, no-exception result associated with a real-valued source
selector. -/
def finiteNoFlags (x : ℝ) : IeeeOperationResult where
  value := IeeeValue.finite x
  flag := fun _ => False
/-- A general no-exception result associated with an IEEE-facing value.  This
is used for non-finite special-value branches that do not raise a flag. -/
def valueNoFlags (value : IeeeValue) : IeeeOperationResult where
  value := value
  flag := fun _ => False
def hasFlag (r : IeeeOperationResult) (flag : IeeeExceptionFlag) : Prop :=
  r.flag flag
def noFlags (r : IeeeOperationResult) : Prop :=
  ∀ flag, ¬ r.hasFlag flag
def isFinite (r : IeeeOperationResult) : Prop :=
  r.value.isFinite
theorem finiteNoFlags_value (x : ℝ) :
    (finiteNoFlags x).value = IeeeValue.finite x := rfl
theorem valueNoFlags_value (value : IeeeValue) :
    (valueNoFlags value).value = value := rfl
theorem finiteNoFlags_noFlags (x : ℝ) :
    (finiteNoFlags x).noFlags := by
  intro flag
  simp [finiteNoFlags, hasFlag]
theorem valueNoFlags_noFlags (value : IeeeValue) :
    (valueNoFlags value).noFlags := by
  intro flag
  simp [valueNoFlags, hasFlag]
theorem not_hasFlag_of_noFlags {r : IeeeOperationResult}
    {flag : IeeeExceptionFlag} (h : r.noFlags) :
    ¬ r.hasFlag flag :=
  h flag
theorem finiteNoFlags_not_hasFlag (x : ℝ) (flag : IeeeExceptionFlag) :
    ¬ (finiteNoFlags x).hasFlag flag :=
  not_hasFlag_of_noFlags (finiteNoFlags_noFlags x)
theorem valueNoFlags_not_hasFlag (value : IeeeValue)
    (flag : IeeeExceptionFlag) :
    ¬ (valueNoFlags value).hasFlag flag :=
  not_hasFlag_of_noFlags (valueNoFlags_noFlags value)
theorem finiteNoFlags_isFinite (x : ℝ) :
    (finiteNoFlags x).isFinite := by
  simp [finiteNoFlags, isFinite, IeeeValue.isFinite]
theorem valueNoFlags_isFinite_iff (value : IeeeValue) :
    (valueNoFlags value).isFinite ↔ value.isFinite := by
  rfl
theorem finiteNoFlags_toReal? (x : ℝ) :
    (finiteNoFlags x).value.toReal? = some x := rfl
theorem valueNoFlags_toReal? (value : IeeeValue) :
    (valueNoFlags value).value.toReal? = value.toReal? := rfl

end IeeeOperationResult

end

end NumStability
