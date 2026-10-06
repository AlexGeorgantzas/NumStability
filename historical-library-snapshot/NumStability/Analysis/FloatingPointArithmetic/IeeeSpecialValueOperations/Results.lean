-- NumStability/Analysis/FloatingPointArithmetic/IeeeSpecialValueOperations/Results.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Analysis.FloatingPointArithmetic`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import NumStability.Analysis.Error.Measures.All
import NumStability.Analysis.FloatingPointArithmetic.ErrorModels.All
import NumStability.Analysis.FloatingPointArithmetic.ExactSubtraction
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.IeeeExceptions
import NumStability.Analysis.FloatingPointArithmetic.IeeeOperations
import NumStability.Analysis.FloatingPointArithmetic.IeeeValue
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.FloatingPointArithmetic.Rounding
import NumStability.Analysis.FloatingPointArithmetic.RoundToEvenLocalError
import NumStability.Analysis.FloatingPointArithmetic.StandardModel

/-!
# Results

Relocated from `NumStability.Analysis.FloatingPointArithmetic` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# Floating point arithmetic (compatibility module)

Compatibility facade retained so existing imports of
`NumStability.Analysis.FloatingPointArithmetic`
keep resolving. Most declarations moved unchanged to the reusable and Higham
Chapter 2 modules imported above. Two hundred thirty-four declarations remain
here because private declarations and their user closures must preserve the
original module identity. The module's original imports are re-stated so
consumers reaching identifiers transitively through this path retain the same
surface.
-/

namespace NumStability

noncomputable section

private theorem ieeeInfinityFiniteSignOption_pos_sound
    {x : ℝ} {r : IeeeOperationResult}
    (h :
      (if 0 < x then
          some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
        else if x < 0 then
          some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
        else
          none) = some r) :
    ∃ value,
      (0 < x ∧ value = IeeeValue.posInf ∨
          x < 0 ∧ value = IeeeValue.negInf) ∧
        r = IeeeOperationResult.valueNoFlags value := by
  by_cases hxpos : 0 < x
  · simp [hxpos] at h
    cases h
    exact ⟨IeeeValue.posInf, ⟨Or.inl ⟨hxpos, rfl⟩, rfl⟩⟩
  · by_cases hxneg : x < 0
    · simp [hxpos, hxneg] at h
      cases h
      exact ⟨IeeeValue.negInf, ⟨Or.inr ⟨hxneg, rfl⟩, rfl⟩⟩
    · simp [hxpos, hxneg] at h
private theorem ieeeInfinityFiniteSignOption_neg_sound
    {x : ℝ} {r : IeeeOperationResult}
    (h :
      (if 0 < x then
          some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
        else if x < 0 then
          some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
        else
          none) = some r) :
    ∃ value,
      (x < 0 ∧ value = IeeeValue.posInf ∨
          0 < x ∧ value = IeeeValue.negInf) ∧
        r = IeeeOperationResult.valueNoFlags value := by
  by_cases hxpos : 0 < x
  · simp [hxpos] at h
    cases h
    exact ⟨IeeeValue.negInf, ⟨Or.inr ⟨hxpos, rfl⟩, rfl⟩⟩
  · by_cases hxneg : x < 0
    · simp [hxpos, hxneg] at h
      cases h
      exact ⟨IeeeValue.posInf, ⟨Or.inl ⟨hxneg, rfl⟩, rfl⟩⟩
    · simp [hxpos, hxneg] at h
theorem ieeePrimitiveInfinityPropagationResult?_sound
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInfinityPropagationResult? op x y = some r) :
    ieeePrimitiveInfinityPropagationResult op x y r := by
  classical
  revert r
  cases op <;> cases x <;> cases y <;> intro r h <;>
    simp [ieeePrimitiveInfinityPropagationResult?,
      ieeePrimitiveInfinityPropagationResult,
      ieeePrimitiveMulInfinityPropagationResult,
      ieeePrimitiveMulInfinityValue,
      ieeePrimitiveDivInfinityPropagationResult,
      ieeePrimitiveDivInfinityValue,
      IeeeValue.isFinite, IeeeValue.isInfinite,
      IeeeValue.isPositiveNonzero, IeeeValue.isNegativeNonzero] at h ⊢
  all_goals
    first
    | (symm; exact h)
    | exact ieeeInfinityFiniteSignOption_pos_sound h
    | exact ieeeInfinityFiniteSignOption_neg_sound h
theorem ieeePrimitiveSpecialValueResult_infinityDefault?
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInfinityPropagationResult? op x y = some r) :
    ieeePrimitiveSpecialValueResult op x y r :=
  ieeePrimitiveSpecialValueResult_infinity
    (ieeePrimitiveInfinityPropagationResult?_sound h)
theorem ieeePrimitiveSpecialValueResult?_sound
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveSpecialValueResult? op x y = some r) :
    ieeePrimitiveSpecialValueResult op x y r := by
  classical
  unfold ieeePrimitiveSpecialValueResult? at h
  cases hnan : ieeeQuietNaNPropagationResult? x y with
  | some rnan =>
      rw [hnan] at h
      cases h
      exact ieeePrimitiveSpecialValueResult_quietNaNDefault? hnan
  | none =>
      rw [hnan] at h
      cases hinvalid : ieeePrimitiveInvalidOperationResult? op x y with
      | some rinvalid =>
          rw [hinvalid] at h
          cases h
          exact
            ieeePrimitiveSpecialValueResult_invalidOperationDefault? hinvalid
      | none =>
          rw [hinvalid] at h
          cases hinf : ieeePrimitiveInfinityPropagationResult? op x y with
          | some rinf =>
              rw [hinf] at h
              cases h
              exact ieeePrimitiveSpecialValueResult_infinityDefault? hinf
          | none =>
              rw [hinf] at h
              cases hfininf :
                  ieeePrimitiveFiniteOverInfinityResult? op x y with
              | some rfininf =>
                  rw [hfininf] at h
                  cases h
                  exact
                    ieeePrimitiveSpecialValueResult_finiteOverInfinityDefault?
                      hfininf
              | none =>
                  rw [hfininf] at h
                  cases op with
                  | add =>
                      cases hzero :
                          ieeePrimitiveAddSubSignedZeroResult?
                            BasicOp.add x y with
                      | some rzero =>
                          rw [hzero] at h
                          cases h
                          exact
                            ieeePrimitiveSpecialValueResult_addSubSignedZeroDefault?
                              hzero
                      | none =>
                          rw [hzero] at h
                          exact
                            ieeePrimitiveSpecialValueResult_addSubFiniteSignedZeroDefault?
                              h
                  | sub =>
                      cases hzero :
                          ieeePrimitiveAddSubSignedZeroResult?
                            BasicOp.sub x y with
                      | some rzero =>
                          rw [hzero] at h
                          cases h
                          exact
                            ieeePrimitiveSpecialValueResult_addSubSignedZeroDefault?
                              hzero
                      | none =>
                          rw [hzero] at h
                          exact
                            ieeePrimitiveSpecialValueResult_addSubFiniteSignedZeroDefault?
                              h
                  | mul =>
                      exact
                        ieeePrimitiveSpecialValueResult_mulSignedZeroDefault? h
                  | div =>
                      exact
                        ieeePrimitiveSpecialValueResult_signedZeroOverFiniteDefault?
                          h
theorem ieeePrimitiveValueBranchResult_infinityDefault?
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInfinityPropagationResult? op x y = some r) :
    ieeePrimitiveValueBranchResult op x y r :=
  ieeePrimitiveValueBranchResult_special
    (ieeePrimitiveSpecialValueResult_infinityDefault? h)
theorem ieeePrimitiveValueBranchResult?_sound
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveValueBranchResult? op x y = some r) :
    ieeePrimitiveValueBranchResult op x y r := by
  classical
  unfold ieeePrimitiveValueBranchResult? at h
  cases hspecial : ieeePrimitiveSpecialValueResult? op x y with
  | some rspecial =>
      rw [hspecial] at h
      cases h
      exact
        ieeePrimitiveValueBranchResult_special
          (ieeePrimitiveSpecialValueResult?_sound hspecial)
  | none =>
      rw [hspecial] at h
      cases op with
      | add => simp at h
      | sub => simp at h
      | mul => simp at h
      | div =>
          exact
            ieeePrimitiveValueBranchResult_divisionByZero
              (ieeeDivisionByZeroDefaultResult?_sound h)
namespace FloatingPointFormat

theorem ieeeRoundToModeOpValueResult_primitiveValueBranchDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveValueBranchResult? op x y = some r) :
    fmt.ieeeRoundToModeOpValueResult mode op x y r :=
  fmt.ieeeRoundToModeOpValueResult_branch
    (ieeePrimitiveValueBranchResult?_sound h)
theorem ieeeRoundToModeOpValueResult_infinityDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInfinityPropagationResult? op x y = some r) :
    fmt.ieeeRoundToModeOpValueResult mode op x y r :=
  fmt.ieeeRoundToModeOpValueResult_branch
    (ieeePrimitiveValueBranchResult_infinityDefault? h)
theorem ieeeRoundToModeOpValueResult_add_posInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.add
      IeeeValue.posInf IeeeValue.posInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpValueResult_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_add_posInf_posInf
theorem ieeeRoundToModeOpValueResult_sub_posInf_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.sub
      IeeeValue.posInf IeeeValue.negInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpValueResult_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_sub_posInf_negInf
theorem ieeeRoundToModeOpValueResult_mul_negInf_of_posInf_finite_neg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y < 0) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.mul
      IeeeValue.posInf (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpValueResult_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_mul_negInf_of_posInf_finite_neg hy)
theorem ieeeRoundToModeOpValueResult_div_posInf_finite_pos
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : 0 < y) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.div
      IeeeValue.posInf (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpValueResult_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_posInf_finite_pos hy)
theorem ieeeRoundToModeOpValueResult_add_posInf_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.add
      IeeeValue.posInf IeeeValue.negInf
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_add_posInf_negInf
theorem ieeeRoundToModeOpValueResult_div_posInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.div
      IeeeValue.posInf IeeeValue.posInf
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_div_posInf_posInf
theorem ieeeRoundToModeOpValueResult_div_finite_pos_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 < x) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.posZero
      (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpValueResult_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_pos_posZero hx)
theorem ieeeRoundToModeOpValueResult_div_finite_neg_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.posZero
      (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpValueResult_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_neg_posZero hx)
theorem ieeeRoundToModeOpValueResult_div_finite_pos_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 < x) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.negZero
      (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpValueResult_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_pos_negZero hx)
theorem ieeeRoundToModeOpValueResult_div_finite_neg_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.negZero
      (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpValueResult_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_neg_negZero hx)
theorem ieeeRoundToModeOpValueResult_div_finite_pos_finite_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 < x) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.div
      (IeeeValue.finite x) (IeeeValue.finite 0)
      (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpValueResult_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_pos_finite_zero hx)
theorem ieeeRoundToModeOpValueResult_div_finite_neg_finite_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.div
      (IeeeValue.finite x) (IeeeValue.finite 0)
      (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpValueResult_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_neg_finite_zero hx)
theorem ieeeRoundToModeOpValueResult_div_finite_zero_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.div
      (IeeeValue.finite 0) IeeeValue.posZero
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_div_finite_zero_posZero
theorem ieeeRoundToModeOpValueResult_div_finite_zero_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.div
      (IeeeValue.finite 0) IeeeValue.negZero
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_div_finite_zero_negZero
theorem ieeeRoundToModeOpValueResult_div_finite_zero_finite_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult mode BasicOp.div
      (IeeeValue.finite 0) (IeeeValue.finite 0)
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_div_finite_zero_finite_zero
theorem ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveValueBranchResult? op x y = some r) :
    fmt.ieeeRoundToModeOpValueResult? mode op x y = some r ∧
      ieeePrimitiveValueBranchResult op x y r := by
  exact
    ⟨by simp [ieeeRoundToModeOpValueResult?, h],
      ieeePrimitiveValueBranchResult?_sound h⟩
theorem ieeeRoundToModeOpValueResult?_quietNaNDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeQuietNaNPropagationResult? x y = some r) :
    fmt.ieeeRoundToModeOpValueResult? mode op x y = some r ∧
      ieeeQuietNaNPropagationResult x y r :=
  ⟨(fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
      (ieeePrimitiveValueBranchResult?_quietNaNDefault? h)).1,
    ieeeQuietNaNPropagationResult?_sound h⟩
theorem ieeeRoundToModeOpValueResult?_left_nan
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) (y : IeeeValue) :
    fmt.ieeeRoundToModeOpValueResult? mode op IeeeValue.nan y =
      some (IeeeOperationResult.valueNoFlags IeeeValue.nan) :=
  (fmt.ieeeRoundToModeOpValueResult?_quietNaNDefault? (mode := mode)
    (ieeeQuietNaNPropagationResult?_left_nan y)).1
theorem ieeeRoundToModeOpValueResult?_right_nan
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) (x : IeeeValue) :
    fmt.ieeeRoundToModeOpValueResult? mode op x IeeeValue.nan =
      some (IeeeOperationResult.valueNoFlags IeeeValue.nan) :=
  (fmt.ieeeRoundToModeOpValueResult?_quietNaNDefault? (mode := mode)
    (ieeeQuietNaNPropagationResult?_right_nan x)).1
theorem ieeeRoundToModeOpValueResult?_add_posZero_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.add
      IeeeValue.posZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_add_posZero_posZero).1
theorem ieeeRoundToModeOpValueResult?_add_negZero_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.add
      IeeeValue.negZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_add_negZero_negZero).1
theorem ieeeRoundToModeOpValueResult?_sub_posZero_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.sub
      IeeeValue.posZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_sub_posZero_negZero).1
theorem ieeeRoundToModeOpValueResult?_sub_negZero_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.sub
      IeeeValue.negZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_sub_negZero_posZero).1
theorem ieeeRoundToModeOpValueResult?_div_posZero_finite_pos
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : 0 < y) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_posZero_finite_pos hy)).1
theorem ieeeRoundToModeOpValueResult?_div_posZero_finite_neg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y < 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_posZero_finite_neg hy)).1
theorem ieeeRoundToModeOpValueResult?_div_negZero_finite_pos
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : 0 < y) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_negZero_finite_pos hy)).1
theorem ieeeRoundToModeOpValueResult?_div_negZero_finite_neg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y < 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_negZero_finite_neg hy)).1
theorem ieeeRoundToModeOpValueResult?_finiteOverInfinityDefault?
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveFiniteOverInfinityResult? op x y = some r) :
    fmt.ieeeRoundToModeOpValueResult? mode op x y = some r :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_finiteOverInfinityDefault? h)).1
theorem ieeeRoundToModeOpValueResult?_div_posZero_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      IeeeValue.posZero IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpValueResult?_finiteOverInfinityDefault? mode
    ieeePrimitiveFiniteOverInfinityResult?_posZero_posInf
theorem ieeeRoundToModeOpValueResult?_div_negZero_of_posZero_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      IeeeValue.posZero IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpValueResult?_finiteOverInfinityDefault? mode
    ieeePrimitiveFiniteOverInfinityResult?_negZero_of_posZero_negInf
theorem ieeeRoundToModeOpValueResult?_div_negZero_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      IeeeValue.negZero IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpValueResult?_finiteOverInfinityDefault? mode
    ieeePrimitiveFiniteOverInfinityResult?_negZero_posInf
theorem ieeeRoundToModeOpValueResult?_div_posZero_of_negZero_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      IeeeValue.negZero IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpValueResult?_finiteOverInfinityDefault? mode
    ieeePrimitiveFiniteOverInfinityResult?_posZero_of_negZero_negInf
theorem ieeeRoundToModeOpValueResult?_div_finite_nonneg_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 ≤ x) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpValueResult?_finiteOverInfinityDefault? mode
    (ieeePrimitiveFiniteOverInfinityResult?_finite_nonneg_posInf hx)
theorem ieeeRoundToModeOpValueResult?_div_negZero_of_finite_neg_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpValueResult?_finiteOverInfinityDefault? mode
    (ieeePrimitiveFiniteOverInfinityResult?_negZero_of_finite_neg_posInf hx)
theorem ieeeRoundToModeOpValueResult?_div_finite_nonneg_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 ≤ x) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpValueResult?_finiteOverInfinityDefault? mode
    (ieeePrimitiveFiniteOverInfinityResult?_finite_nonneg_negInf hx)
theorem ieeeRoundToModeOpValueResult?_div_posZero_of_finite_neg_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpValueResult?_finiteOverInfinityDefault? mode
    (ieeePrimitiveFiniteOverInfinityResult?_posZero_of_finite_neg_negInf hx)
theorem ieeeRoundToModeOpValueResult?_div_finite_zero_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      (IeeeValue.finite 0) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpValueResult?_finiteOverInfinityDefault? mode
    ieeePrimitiveFiniteOverInfinityResult?_finite_zero_posInf
theorem ieeeRoundToModeOpValueResult?_div_finite_zero_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      (IeeeValue.finite 0) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpValueResult?_finiteOverInfinityDefault? mode
    ieeePrimitiveFiniteOverInfinityResult?_finite_zero_negInf
theorem ieeeRoundToModeOpValueResult?_mulSignedZeroDefault?
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveMulSignedZeroResult? x y = some r) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul x y = some r :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_mulSignedZeroDefault? h)).1
theorem ieeeRoundToModeOpValueResult?_mul_posZero_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      IeeeValue.posZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpValueResult?_mulSignedZeroDefault? mode
    ieeePrimitiveMulSignedZeroResult?_posZero_posZero
theorem ieeeRoundToModeOpValueResult?_mul_posZero_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      IeeeValue.posZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpValueResult?_mulSignedZeroDefault? mode
    ieeePrimitiveMulSignedZeroResult?_posZero_negZero
theorem ieeeRoundToModeOpValueResult?_mul_negZero_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      IeeeValue.negZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpValueResult?_mulSignedZeroDefault? mode
    ieeePrimitiveMulSignedZeroResult?_negZero_posZero
theorem ieeeRoundToModeOpValueResult?_mul_negZero_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      IeeeValue.negZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpValueResult?_mulSignedZeroDefault? mode
    ieeePrimitiveMulSignedZeroResult?_negZero_negZero
theorem ieeeRoundToModeOpValueResult?_mul_posZero_finite_nonneg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : 0 ≤ y) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpValueResult?_mulSignedZeroDefault? mode
    (ieeePrimitiveMulSignedZeroResult?_posZero_finite_nonneg hy)
theorem ieeeRoundToModeOpValueResult?_mul_negZero_of_posZero_finite_neg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y < 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpValueResult?_mulSignedZeroDefault? mode
    (ieeePrimitiveMulSignedZeroResult?_negZero_of_posZero_finite_neg hy)
theorem ieeeRoundToModeOpValueResult?_mul_finite_nonneg_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 ≤ x) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      (IeeeValue.finite x) IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpValueResult?_mulSignedZeroDefault? mode
    (ieeePrimitiveMulSignedZeroResult?_finite_nonneg_posZero hx)
theorem ieeeRoundToModeOpValueResult?_mul_negZero_of_finite_neg_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      (IeeeValue.finite x) IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpValueResult?_mulSignedZeroDefault? mode
    (ieeePrimitiveMulSignedZeroResult?_negZero_of_finite_neg_posZero hx)
theorem ieeeRoundToModeOpValueResult?_mul_negZero_finite_nonneg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : 0 ≤ y) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpValueResult?_mulSignedZeroDefault? mode
    (ieeePrimitiveMulSignedZeroResult?_negZero_finite_nonneg hy)
theorem ieeeRoundToModeOpValueResult?_mul_posZero_of_negZero_finite_neg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y < 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpValueResult?_mulSignedZeroDefault? mode
    (ieeePrimitiveMulSignedZeroResult?_posZero_of_negZero_finite_neg hy)
theorem ieeeRoundToModeOpValueResult?_mul_finite_nonneg_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 ≤ x) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      (IeeeValue.finite x) IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpValueResult?_mulSignedZeroDefault? mode
    (ieeePrimitiveMulSignedZeroResult?_finite_nonneg_negZero hx)
theorem ieeeRoundToModeOpValueResult?_mul_posZero_of_finite_neg_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      (IeeeValue.finite x) IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpValueResult?_mulSignedZeroDefault? mode
    (ieeePrimitiveMulSignedZeroResult?_posZero_of_finite_neg_negZero hx)
theorem ieeeRoundToModeOpValueResult?_add_finite_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x ≠ 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.add
      (IeeeValue.finite x) IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_add_finite_posZero hx)).1
theorem ieeeRoundToModeOpValueResult?_add_finite_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x ≠ 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.add
      (IeeeValue.finite x) IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_add_finite_negZero hx)).1
theorem ieeeRoundToModeOpValueResult?_add_posZero_finite
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y ≠ 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.add
      IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite y)) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_add_posZero_finite hy)).1
theorem ieeeRoundToModeOpValueResult?_add_negZero_finite
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y ≠ 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.add
      IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite y)) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_add_negZero_finite hy)).1
theorem ieeeRoundToModeOpValueResult?_sub_finite_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x ≠ 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.sub
      (IeeeValue.finite x) IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_sub_finite_posZero hx)).1
theorem ieeeRoundToModeOpValueResult?_sub_finite_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x ≠ 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.sub
      (IeeeValue.finite x) IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_sub_finite_negZero hx)).1
theorem ieeeRoundToModeOpValueResult?_sub_posZero_finite
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y ≠ 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.sub
      IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite (-y))) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_sub_posZero_finite hy)).1
theorem ieeeRoundToModeOpValueResult?_sub_negZero_finite
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y ≠ 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.sub
      IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite (-y))) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_sub_negZero_finite hy)).1
theorem ieeeRoundToModeOpValueResult?_add_posInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.add
      IeeeValue.posInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_add_posInf_posInf).1
theorem ieeeRoundToModeOpValueResult?_sub_posInf_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.sub
      IeeeValue.posInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_sub_posInf_negInf).1
theorem ieeeRoundToModeOpValueResult?_mul_negInf_of_posInf_finite_neg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y < 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_mul_negInf_of_posInf_finite_neg hy)).1
theorem ieeeRoundToModeOpValueResult?_div_posInf_finite_pos
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : 0 < y) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_posInf_finite_pos hy)).1
theorem ieeeRoundToModeOpValueResult?_infinityDefault?
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInfinityPropagationResult? op x y = some r) :
    fmt.ieeeRoundToModeOpValueResult? mode op x y = some r :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_infinityDefault? h)).1
theorem ieeeRoundToModeOpValueResult?_add_negInf_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.add
      IeeeValue.negInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    ieeePrimitiveInfinityPropagationResult?_add_negInf_negInf
theorem ieeeRoundToModeOpValueResult?_add_posInf_finite
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.add
      IeeeValue.posInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_add_posInf_finite x)
theorem ieeeRoundToModeOpValueResult?_add_finite_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.add
      (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_add_finite_posInf x)
theorem ieeeRoundToModeOpValueResult?_add_negInf_finite
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.add
      IeeeValue.negInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_add_negInf_finite x)
theorem ieeeRoundToModeOpValueResult?_add_finite_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.add
      (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_add_finite_negInf x)
theorem ieeeRoundToModeOpValueResult?_sub_negInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.sub
      IeeeValue.negInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    ieeePrimitiveInfinityPropagationResult?_sub_negInf_posInf
theorem ieeeRoundToModeOpValueResult?_sub_posInf_finite
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.sub
      IeeeValue.posInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_sub_posInf_finite x)
theorem ieeeRoundToModeOpValueResult?_sub_finite_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.sub
      (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_sub_finite_posInf x)
theorem ieeeRoundToModeOpValueResult?_sub_negInf_finite
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.sub
      IeeeValue.negInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_sub_negInf_finite x)
theorem ieeeRoundToModeOpValueResult?_sub_finite_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.sub
      (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_sub_finite_negInf x)
theorem ieeeRoundToModeOpValueResult?_mul_posInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      IeeeValue.posInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    ieeePrimitiveInfinityPropagationResult?_mul_posInf_posInf
theorem ieeeRoundToModeOpValueResult?_mul_posInf_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      IeeeValue.posInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    ieeePrimitiveInfinityPropagationResult?_mul_posInf_negInf
theorem ieeeRoundToModeOpValueResult?_mul_negInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      IeeeValue.negInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    ieeePrimitiveInfinityPropagationResult?_mul_negInf_posInf
theorem ieeeRoundToModeOpValueResult?_mul_negInf_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      IeeeValue.negInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    ieeePrimitiveInfinityPropagationResult?_mul_negInf_negInf
theorem ieeeRoundToModeOpValueResult?_mul_posInf_finite_pos
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : 0 < y) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_mul_posInf_finite_pos hy)
theorem ieeeRoundToModeOpValueResult?_mul_negInf_finite_pos
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : 0 < y) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_mul_negInf_finite_pos hy)
theorem ieeeRoundToModeOpValueResult?_mul_posInf_of_negInf_finite_neg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y < 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_mul_posInf_of_negInf_finite_neg hy)
theorem ieeeRoundToModeOpValueResult?_mul_finite_pos_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 < x) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_mul_finite_pos_posInf hx)
theorem ieeeRoundToModeOpValueResult?_mul_negInf_of_finite_neg_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_mul_negInf_of_finite_neg_posInf hx)
theorem ieeeRoundToModeOpValueResult?_mul_finite_pos_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 < x) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_mul_finite_pos_negInf hx)
theorem ieeeRoundToModeOpValueResult?_mul_posInf_of_finite_neg_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul
      (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_mul_posInf_of_finite_neg_negInf hx)
theorem ieeeRoundToModeOpValueResult?_div_negInf_of_posInf_finite_neg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y < 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_div_negInf_of_posInf_finite_neg hy)
theorem ieeeRoundToModeOpValueResult?_div_negInf_finite_pos
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : 0 < y) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_div_negInf_finite_pos hy)
theorem ieeeRoundToModeOpValueResult?_div_posInf_of_negInf_finite_neg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y < 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_div_posInf_of_negInf_finite_neg hy)
theorem ieeeRoundToModeOpValueResult?_of_invalidOperationInput
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {op : BasicOp} {x y : IeeeValue}
    (hinput : ieeePrimitiveInvalidOperationInput op x y) :
    fmt.ieeeRoundToModeOpValueResult? mode op x y =
      some ieeeInvalidOperationDefaultResult :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_of_invalidOperationInput hinput)).1
theorem ieeeRoundToModeOpValueResult?_add_posInf_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.add
      IeeeValue.posInf IeeeValue.negInf =
        some ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult?_of_invalidOperationInput mode
    ieeePrimitiveInvalidOperationInput_add_posInf_negInf
theorem ieeeRoundToModeOpValueResult?_add_negInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.add
      IeeeValue.negInf IeeeValue.posInf =
        some ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult?_of_invalidOperationInput mode
    ieeePrimitiveInvalidOperationInput_add_negInf_posInf
theorem ieeeRoundToModeOpValueResult?_sub_posInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.sub
      IeeeValue.posInf IeeeValue.posInf =
        some ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult?_of_invalidOperationInput mode
    ieeePrimitiveInvalidOperationInput_sub_posInf_posInf
theorem ieeeRoundToModeOpValueResult?_sub_negInf_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.sub
      IeeeValue.negInf IeeeValue.negInf =
        some ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult?_of_invalidOperationInput mode
    ieeePrimitiveInvalidOperationInput_sub_negInf_negInf
theorem ieeeRoundToModeOpValueResult?_mul_zero_inf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : IeeeValue} (hx : x.isZero) (hy : y.isInfinite) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul x y =
      some ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult?_of_invalidOperationInput mode
    (ieeePrimitiveInvalidOperationInput_mul_zero_inf hx hy)
theorem ieeeRoundToModeOpValueResult?_mul_inf_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : IeeeValue} (hx : x.isInfinite) (hy : y.isZero) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.mul x y =
      some ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult?_of_invalidOperationInput mode
    (ieeePrimitiveInvalidOperationInput_mul_inf_zero hx hy)
theorem ieeeRoundToModeOpValueResult?_div_zero_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : IeeeValue} (hx : x.isZero) (hy : y.isZero) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div x y =
      some ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult?_of_invalidOperationInput mode
    (ieeePrimitiveInvalidOperationInput_div_zero_zero hx hy)
theorem ieeeRoundToModeOpValueResult?_div_inf_inf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : IeeeValue} (hx : x.isInfinite) (hy : y.isInfinite) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div x y =
      some ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpValueResult?_of_invalidOperationInput mode
    (ieeePrimitiveInvalidOperationInput_div_inf_inf hx hy)
theorem ieeeRoundToModeOpValueResult?_div_posInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      IeeeValue.posInf IeeeValue.posInf =
        some ieeeInvalidOperationDefaultResult :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_div_posInf_posInf).1
theorem ieeeRoundToModeOpValueResult?_div_finite_pos_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 < x) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.posZero =
        some (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_pos_posZero hx)).1
theorem ieeeRoundToModeOpValueResult?_div_finite_neg_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.posZero =
        some (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_neg_posZero hx)).1
theorem ieeeRoundToModeOpValueResult?_div_finite_pos_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 < x) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.negZero =
        some (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_pos_negZero hx)).1
theorem ieeeRoundToModeOpValueResult?_div_finite_neg_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.negZero =
        some (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_neg_negZero hx)).1
theorem ieeeRoundToModeOpValueResult?_div_finite_pos_finite_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 < x) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      (IeeeValue.finite x) (IeeeValue.finite 0) =
        some (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_pos_finite_zero hx)).1
theorem ieeeRoundToModeOpValueResult?_div_finite_neg_finite_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      (IeeeValue.finite x) (IeeeValue.finite 0) =
        some (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_neg_finite_zero hx)).1
theorem ieeeRoundToModeOpValueResult?_div_finite_zero_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      (IeeeValue.finite 0) IeeeValue.posZero =
        some ieeeInvalidOperationDefaultResult :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_div_finite_zero_posZero).1
theorem ieeeRoundToModeOpValueResult?_div_finite_zero_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      (IeeeValue.finite 0) IeeeValue.negZero =
        some ieeeInvalidOperationDefaultResult :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_div_finite_zero_negZero).1
theorem ieeeRoundToModeOpValueResult?_div_finite_zero_finite_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpValueResult? mode BasicOp.div
      (IeeeValue.finite 0) (IeeeValue.finite 0) =
        some ieeeInvalidOperationDefaultResult :=
  (fmt.ieeeRoundToModeOpValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_div_finite_zero_finite_zero).1
theorem ieeeRoundToModeOpValueResult?_finite_of_no_value_branch
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hno : ¬ ∃ r, ieeePrimitiveValueBranchResult op
      (IeeeValue.finite x) (IeeeValue.finite y) r) :
    fmt.ieeeRoundToModeOpValueResult? mode op
      (IeeeValue.finite x) (IeeeValue.finite y) =
      some (fmt.ieeeRoundToModeOpResult mode op x y) := by
  classical
  have hbranch :
      ieeePrimitiveValueBranchResult? op
        (IeeeValue.finite x) (IeeeValue.finite y) = none := by
    cases hbranch :
        ieeePrimitiveValueBranchResult? op
          (IeeeValue.finite x) (IeeeValue.finite y) with
    | none => rfl
    | some r =>
        exact False.elim
          (hno ⟨r, ieeePrimitiveValueBranchResult?_sound hbranch⟩)
  have hzero :
      ieeePrimitiveAddSubZeroSumResult? mode op
        (IeeeValue.finite x) (IeeeValue.finite y) = none := by
    cases hzero :
        ieeePrimitiveAddSubZeroSumResult? mode op
          (IeeeValue.finite x) (IeeeValue.finite y) with
    | none => rfl
    | some r =>
        exact False.elim
          ((ieeePrimitiveAddSubZeroSumResult_finite_absurd mode op x y)
            ⟨r, ieeePrimitiveAddSubZeroSumResult?_sound hzero⟩)
  simp [ieeeRoundToModeOpValueResult?, hbranch, hzero]
theorem ieeeRoundToModeOpValueResult?_sound
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : fmt.ieeeRoundToModeOpValueResult? mode op x y = some r) :
    fmt.ieeeRoundToModeOpValueResult mode op x y r := by
  classical
  cases hbranch : ieeePrimitiveValueBranchResult? op x y with
  | some rbranch =>
      have hr : r = rbranch := by
        simpa [ieeeRoundToModeOpValueResult?, hbranch] using h.symm
      subst r
      exact
        fmt.ieeeRoundToModeOpValueResult_branch
          (ieeePrimitiveValueBranchResult?_sound hbranch)
  | none =>
      cases hzero : ieeePrimitiveAddSubZeroSumResult? mode op x y with
      | some rzero =>
          have hr : r = rzero := by
            simpa [ieeeRoundToModeOpValueResult?, hbranch, hzero] using h.symm
          subst r
          exact
            fmt.ieeeRoundToModeOpValueResult_addSubZeroSum
              (ieeePrimitiveAddSubZeroSumResult?_sound hzero)
      | none =>
          cases x <;> cases y <;>
            simp [ieeeRoundToModeOpValueResult?, hbranch, hzero] at h
          · cases h
            exact
              fmt.ieeeRoundToModeOpValueResult_finite_of_no_value_branch
                (ieeePrimitiveValueBranchResult_finite_absurd_of_valueBranchDefault?_none
                  hbranch)
theorem ieeeRoundToModeOpValueResult?_finite_of_division_guard
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) {x y : ℝ}
    (hdiv : op = BasicOp.div → y ≠ 0) :
    fmt.ieeeRoundToModeOpValueResult? mode op
      (IeeeValue.finite x) (IeeeValue.finite y) =
      some (fmt.ieeeRoundToModeOpResult mode op x y) :=
  fmt.ieeeRoundToModeOpValueResult?_finite_of_no_value_branch
    (ieeePrimitiveValueBranchResult_finite_absurd_of_division_guard op hdiv)
theorem ieeeRoundToModeOpValueResult?_noFlags_toReal?_of_finiteNormalRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y))
    (hdiv : op = BasicOp.div → y ≠ 0) :
    fmt.ieeeRoundToModeOpValueResult? mode op
        (IeeeValue.finite x) (IeeeValue.finite y) =
        some (fmt.ieeeRoundToModeOpResult mode op x y) ∧
      (fmt.ieeeRoundToModeOpResult mode op x y).noFlags ∧
        (fmt.ieeeRoundToModeOpResult mode op x y).value.toReal? =
          some (fmt.finiteRoundToModeOp mode op x y) :=
  ⟨fmt.ieeeRoundToModeOpValueResult?_finite_of_division_guard
      mode op hdiv,
    fmt.ieeeRoundToModeOpResult_noFlags_of_finiteNormalRange hxy,
    fmt.ieeeRoundToModeOpResult_toReal?_of_finiteNormalRange hxy⟩
theorem ieeeRoundToModeOpInexactAwareValueResult_primitiveValueBranchDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveValueBranchResult? op x y = some r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode op x y r :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_branch
    (ieeePrimitiveValueBranchResult?_sound h)
theorem ieeeRoundToModeOpInexactAwareValueResult_infinityDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInfinityPropagationResult? op x y = some r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode op x y r :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_branch
    (ieeePrimitiveValueBranchResult_infinityDefault? h)
theorem ieeeRoundToModeOpInexactAwareValueResult_add_posInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.add
      IeeeValue.posInf IeeeValue.posInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_add_posInf_posInf
theorem ieeeRoundToModeOpInexactAwareValueResult_sub_posInf_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.sub
      IeeeValue.posInf IeeeValue.negInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_sub_posInf_negInf
theorem ieeeRoundToModeOpInexactAwareValueResult_mul_negInf_of_posInf_finite_neg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.mul
      IeeeValue.posInf (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_mul_negInf_of_posInf_finite_neg hy)
theorem ieeeRoundToModeOpInexactAwareValueResult_div_posInf_finite_pos
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : 0 < y) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.div
      IeeeValue.posInf (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_posInf_finite_pos hy)
theorem ieeeRoundToModeOpInexactAwareValueResult_add_posInf_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.add
      IeeeValue.posInf IeeeValue.negInf
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_add_posInf_negInf
theorem ieeeRoundToModeOpInexactAwareValueResult_div_posInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.div
      IeeeValue.posInf IeeeValue.posInf
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_div_posInf_posInf
theorem ieeeRoundToModeOpInexactAwareValueResult_div_finite_pos_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 < x) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.posZero
      (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_pos_posZero hx)
theorem ieeeRoundToModeOpInexactAwareValueResult_div_finite_neg_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.posZero
      (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_neg_posZero hx)
theorem ieeeRoundToModeOpInexactAwareValueResult_div_finite_pos_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 < x) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.negZero
      (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_pos_negZero hx)
theorem ieeeRoundToModeOpInexactAwareValueResult_div_finite_neg_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.negZero
      (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_neg_negZero hx)
theorem ieeeRoundToModeOpInexactAwareValueResult_div_finite_pos_finite_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 < x) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.div
      (IeeeValue.finite x) (IeeeValue.finite 0)
      (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_pos_finite_zero hx)
theorem ieeeRoundToModeOpInexactAwareValueResult_div_finite_neg_finite_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.div
      (IeeeValue.finite x) (IeeeValue.finite 0)
      (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_neg_finite_zero hx)
theorem ieeeRoundToModeOpInexactAwareValueResult_div_finite_zero_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.div
      (IeeeValue.finite 0) IeeeValue.posZero
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_div_finite_zero_posZero
theorem ieeeRoundToModeOpInexactAwareValueResult_div_finite_zero_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.div
      (IeeeValue.finite 0) IeeeValue.negZero
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_div_finite_zero_negZero
theorem ieeeRoundToModeOpInexactAwareValueResult_div_finite_zero_finite_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode BasicOp.div
      (IeeeValue.finite 0) (IeeeValue.finite 0)
      ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_div_finite_zero_finite_zero
theorem ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveValueBranchResult? op x y = some r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode op x y =
        some r ∧
      ieeePrimitiveValueBranchResult op x y r := by
  exact
    ⟨by simp [ieeeRoundToModeOpInexactAwareValueResult?, h],
      ieeePrimitiveValueBranchResult?_sound h⟩
theorem ieeeRoundToModeOpInexactAwareValueResult?_quietNaNDefault?
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeQuietNaNPropagationResult? x y = some r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode op x y =
        some r ∧
      ieeeQuietNaNPropagationResult x y r :=
  ⟨(fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
      (ieeePrimitiveValueBranchResult?_quietNaNDefault? h)).1,
    ieeeQuietNaNPropagationResult?_sound h⟩
theorem ieeeRoundToModeOpInexactAwareValueResult?_left_nan
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) (y : IeeeValue) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode op IeeeValue.nan y =
      some (IeeeOperationResult.valueNoFlags IeeeValue.nan) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_quietNaNDefault? (mode := mode)
    (ieeeQuietNaNPropagationResult?_left_nan y)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_right_nan
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) (x : IeeeValue) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode op x IeeeValue.nan =
      some (IeeeOperationResult.valueNoFlags IeeeValue.nan) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_quietNaNDefault? (mode := mode)
    (ieeeQuietNaNPropagationResult?_right_nan x)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_add_posZero_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.add
      IeeeValue.posZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_add_posZero_posZero).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_add_negZero_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.add
      IeeeValue.negZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_add_negZero_negZero).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_sub_posZero_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.sub
      IeeeValue.posZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_sub_posZero_negZero).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_sub_negZero_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.sub
      IeeeValue.negZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_sub_negZero_posZero).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_posZero_finite_pos
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : 0 < y) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_posZero_finite_pos hy)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_posZero_finite_neg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_posZero_finite_neg hy)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_negZero_finite_pos
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : 0 < y) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_negZero_finite_pos hy)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_negZero_finite_neg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_negZero_finite_neg hy)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_finiteOverInfinityDefault?
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveFiniteOverInfinityResult? op x y = some r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode op x y =
      some r :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_finiteOverInfinityDefault? h)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_posZero_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      IeeeValue.posZero IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_finiteOverInfinityDefault?
    mode ieeePrimitiveFiniteOverInfinityResult?_posZero_posInf
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_negZero_of_posZero_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      IeeeValue.posZero IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_finiteOverInfinityDefault?
    mode ieeePrimitiveFiniteOverInfinityResult?_negZero_of_posZero_negInf
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_negZero_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      IeeeValue.negZero IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_finiteOverInfinityDefault?
    mode ieeePrimitiveFiniteOverInfinityResult?_negZero_posInf
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_posZero_of_negZero_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      IeeeValue.negZero IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_finiteOverInfinityDefault?
    mode ieeePrimitiveFiniteOverInfinityResult?_posZero_of_negZero_negInf
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_finite_nonneg_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 ≤ x) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_finiteOverInfinityDefault?
    mode (ieeePrimitiveFiniteOverInfinityResult?_finite_nonneg_posInf hx)
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_negZero_of_finite_neg_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_finiteOverInfinityDefault?
    mode (ieeePrimitiveFiniteOverInfinityResult?_negZero_of_finite_neg_posInf hx)
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_finite_nonneg_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 ≤ x) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_finiteOverInfinityDefault?
    mode (ieeePrimitiveFiniteOverInfinityResult?_finite_nonneg_negInf hx)
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_posZero_of_finite_neg_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_finiteOverInfinityDefault?
    mode (ieeePrimitiveFiniteOverInfinityResult?_posZero_of_finite_neg_negInf hx)
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_finite_zero_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      (IeeeValue.finite 0) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_finiteOverInfinityDefault?
    mode ieeePrimitiveFiniteOverInfinityResult?_finite_zero_posInf
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_finite_zero_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      (IeeeValue.finite 0) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_finiteOverInfinityDefault?
    mode ieeePrimitiveFiniteOverInfinityResult?_finite_zero_negInf
theorem ieeeRoundToModeOpInexactAwareValueResult?_mulSignedZeroDefault?
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveMulSignedZeroResult? x y = some r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul x y =
      some r :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_mulSignedZeroDefault? h)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_posZero_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      IeeeValue.posZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_mulSignedZeroDefault? mode
    ieeePrimitiveMulSignedZeroResult?_posZero_posZero
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_posZero_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      IeeeValue.posZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_mulSignedZeroDefault? mode
    ieeePrimitiveMulSignedZeroResult?_posZero_negZero
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_negZero_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      IeeeValue.negZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_mulSignedZeroDefault? mode
    ieeePrimitiveMulSignedZeroResult?_negZero_posZero
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_negZero_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      IeeeValue.negZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_mulSignedZeroDefault? mode
    ieeePrimitiveMulSignedZeroResult?_negZero_negZero
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_posZero_finite_nonneg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : 0 ≤ y) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_mulSignedZeroDefault? mode
    (ieeePrimitiveMulSignedZeroResult?_posZero_finite_nonneg hy)
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_negZero_of_posZero_finite_neg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_mulSignedZeroDefault? mode
    (ieeePrimitiveMulSignedZeroResult?_negZero_of_posZero_finite_neg hy)
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_finite_nonneg_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 ≤ x) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      (IeeeValue.finite x) IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_mulSignedZeroDefault? mode
    (ieeePrimitiveMulSignedZeroResult?_finite_nonneg_posZero hx)
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_negZero_of_finite_neg_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      (IeeeValue.finite x) IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_mulSignedZeroDefault? mode
    (ieeePrimitiveMulSignedZeroResult?_negZero_of_finite_neg_posZero hx)
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_negZero_finite_nonneg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : 0 ≤ y) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_mulSignedZeroDefault? mode
    (ieeePrimitiveMulSignedZeroResult?_negZero_finite_nonneg hy)
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_posZero_of_negZero_finite_neg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_mulSignedZeroDefault? mode
    (ieeePrimitiveMulSignedZeroResult?_posZero_of_negZero_finite_neg hy)
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_finite_nonneg_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 ≤ x) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      (IeeeValue.finite x) IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_mulSignedZeroDefault? mode
    (ieeePrimitiveMulSignedZeroResult?_finite_nonneg_negZero hx)
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_posZero_of_finite_neg_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      (IeeeValue.finite x) IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_mulSignedZeroDefault? mode
    (ieeePrimitiveMulSignedZeroResult?_posZero_of_finite_neg_negZero hx)
theorem ieeeRoundToModeOpInexactAwareValueResult?_add_finite_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x ≠ 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.add
      (IeeeValue.finite x) IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_add_finite_posZero hx)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_add_finite_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x ≠ 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.add
      (IeeeValue.finite x) IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_add_finite_negZero hx)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_add_posZero_finite
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y ≠ 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.add
      IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite y)) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_add_posZero_finite hy)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_add_negZero_finite
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y ≠ 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.add
      IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite y)) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_add_negZero_finite hy)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_sub_finite_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x ≠ 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.sub
      (IeeeValue.finite x) IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_sub_finite_posZero hx)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_sub_finite_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x ≠ 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.sub
      (IeeeValue.finite x) IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_sub_finite_negZero hx)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_sub_posZero_finite
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y ≠ 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.sub
      IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite (-y))) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_sub_posZero_finite hy)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_sub_negZero_finite
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y ≠ 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.sub
      IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite (-y))) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_sub_negZero_finite hy)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_add_posInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.add
      IeeeValue.posInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_add_posInf_posInf).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_sub_posInf_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.sub
      IeeeValue.posInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_sub_posInf_negInf).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_negInf_of_posInf_finite_neg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_mul_negInf_of_posInf_finite_neg hy)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_posInf_finite_pos
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : 0 < y) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_posInf_finite_pos hy)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault?
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInfinityPropagationResult? op x y = some r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode op x y =
      some r :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_infinityDefault? h)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_add_negInf_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.add
      IeeeValue.negInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    ieeePrimitiveInfinityPropagationResult?_add_negInf_negInf
theorem ieeeRoundToModeOpInexactAwareValueResult?_add_posInf_finite
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.add
      IeeeValue.posInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_add_posInf_finite x)
theorem ieeeRoundToModeOpInexactAwareValueResult?_add_finite_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.add
      (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_add_finite_posInf x)
theorem ieeeRoundToModeOpInexactAwareValueResult?_add_negInf_finite
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.add
      IeeeValue.negInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_add_negInf_finite x)
theorem ieeeRoundToModeOpInexactAwareValueResult?_add_finite_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.add
      (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_add_finite_negInf x)
theorem ieeeRoundToModeOpInexactAwareValueResult?_sub_negInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.sub
      IeeeValue.negInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    ieeePrimitiveInfinityPropagationResult?_sub_negInf_posInf
theorem ieeeRoundToModeOpInexactAwareValueResult?_sub_posInf_finite
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.sub
      IeeeValue.posInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_sub_posInf_finite x)
theorem ieeeRoundToModeOpInexactAwareValueResult?_sub_finite_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.sub
      (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_sub_finite_posInf x)
theorem ieeeRoundToModeOpInexactAwareValueResult?_sub_negInf_finite
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.sub
      IeeeValue.negInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_sub_negInf_finite x)
theorem ieeeRoundToModeOpInexactAwareValueResult?_sub_finite_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.sub
      (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_sub_finite_negInf x)
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_posInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      IeeeValue.posInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    ieeePrimitiveInfinityPropagationResult?_mul_posInf_posInf
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_posInf_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      IeeeValue.posInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    ieeePrimitiveInfinityPropagationResult?_mul_posInf_negInf
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_negInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      IeeeValue.negInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    ieeePrimitiveInfinityPropagationResult?_mul_negInf_posInf
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_negInf_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      IeeeValue.negInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    ieeePrimitiveInfinityPropagationResult?_mul_negInf_negInf
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_posInf_finite_pos
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : 0 < y) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_mul_posInf_finite_pos hy)
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_negInf_finite_pos
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : 0 < y) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_mul_negInf_finite_pos hy)
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_posInf_of_negInf_finite_neg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_mul_posInf_of_negInf_finite_neg hy)
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_finite_pos_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 < x) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_mul_finite_pos_posInf hx)
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_negInf_of_finite_neg_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_mul_negInf_of_finite_neg_posInf hx)
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_finite_pos_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 < x) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_mul_finite_pos_negInf hx)
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_posInf_of_finite_neg_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul
      (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_mul_posInf_of_finite_neg_negInf hx)
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_negInf_of_posInf_finite_neg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_div_negInf_of_posInf_finite_neg hy)
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_negInf_finite_pos
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : 0 < y) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_div_negInf_finite_pos hy)
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_posInf_of_negInf_finite_neg
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {y : ℝ} (hy : y < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_infinityDefault? mode
    (ieeePrimitiveInfinityPropagationResult?_div_posInf_of_negInf_finite_neg hy)
theorem ieeeRoundToModeOpInexactAwareValueResult?_of_invalidOperationInput
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {op : BasicOp} {x y : IeeeValue}
    (hinput : ieeePrimitiveInvalidOperationInput op x y) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode op x y =
      some ieeeInvalidOperationDefaultResult :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_of_invalidOperationInput hinput)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_add_posInf_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.add
      IeeeValue.posInf IeeeValue.negInf =
        some ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_of_invalidOperationInput mode
    ieeePrimitiveInvalidOperationInput_add_posInf_negInf
theorem ieeeRoundToModeOpInexactAwareValueResult?_add_negInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.add
      IeeeValue.negInf IeeeValue.posInf =
        some ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_of_invalidOperationInput mode
    ieeePrimitiveInvalidOperationInput_add_negInf_posInf
theorem ieeeRoundToModeOpInexactAwareValueResult?_sub_posInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.sub
      IeeeValue.posInf IeeeValue.posInf =
        some ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_of_invalidOperationInput mode
    ieeePrimitiveInvalidOperationInput_sub_posInf_posInf
theorem ieeeRoundToModeOpInexactAwareValueResult?_sub_negInf_negInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.sub
      IeeeValue.negInf IeeeValue.negInf =
        some ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_of_invalidOperationInput mode
    ieeePrimitiveInvalidOperationInput_sub_negInf_negInf
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_zero_inf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : IeeeValue} (hx : x.isZero) (hy : y.isInfinite) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul x y =
      some ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_of_invalidOperationInput mode
    (ieeePrimitiveInvalidOperationInput_mul_zero_inf hx hy)
theorem ieeeRoundToModeOpInexactAwareValueResult?_mul_inf_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : IeeeValue} (hx : x.isInfinite) (hy : y.isZero) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.mul x y =
      some ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_of_invalidOperationInput mode
    (ieeePrimitiveInvalidOperationInput_mul_inf_zero hx hy)
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_zero_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : IeeeValue} (hx : x.isZero) (hy : y.isZero) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div x y =
      some ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_of_invalidOperationInput mode
    (ieeePrimitiveInvalidOperationInput_div_zero_zero hx hy)
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_inf_inf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x y : IeeeValue} (hx : x.isInfinite) (hy : y.isInfinite) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div x y =
      some ieeeInvalidOperationDefaultResult :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_of_invalidOperationInput mode
    (ieeePrimitiveInvalidOperationInput_div_inf_inf hx hy)
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_posInf_posInf
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      IeeeValue.posInf IeeeValue.posInf =
        some ieeeInvalidOperationDefaultResult :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_div_posInf_posInf).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_finite_pos_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 < x) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.posZero =
        some (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_pos_posZero hx)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_finite_neg_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.posZero =
        some (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_neg_posZero hx)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_finite_pos_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 < x) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.negZero =
        some (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_pos_negZero hx)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_finite_neg_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      (IeeeValue.finite x) IeeeValue.negZero =
        some (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_neg_negZero hx)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_finite_pos_finite_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : 0 < x) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      (IeeeValue.finite x) (IeeeValue.finite 0) =
        some (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_pos_finite_zero hx)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_finite_neg_finite_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    {x : ℝ} (hx : x < 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      (IeeeValue.finite x) (IeeeValue.finite 0) =
        some (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    (ieeePrimitiveValueBranchResult?_div_finite_neg_finite_zero hx)).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_finite_zero_posZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      (IeeeValue.finite 0) IeeeValue.posZero =
        some ieeeInvalidOperationDefaultResult :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_div_finite_zero_posZero).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_finite_zero_negZero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      (IeeeValue.finite 0) IeeeValue.negZero =
        some ieeeInvalidOperationDefaultResult :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_div_finite_zero_negZero).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_div_finite_zero_finite_zero
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode BasicOp.div
      (IeeeValue.finite 0) (IeeeValue.finite 0) =
        some ieeeInvalidOperationDefaultResult :=
  (fmt.ieeeRoundToModeOpInexactAwareValueResult?_primitiveValueBranchDefault?
    ieeePrimitiveValueBranchResult?_div_finite_zero_finite_zero).1
theorem ieeeRoundToModeOpInexactAwareValueResult?_finite_of_no_value_branch
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hno : ¬ ∃ r, ieeePrimitiveValueBranchResult op
      (IeeeValue.finite x) (IeeeValue.finite y) r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode op
      (IeeeValue.finite x) (IeeeValue.finite y) =
      some (fmt.ieeeRoundToModeOpInexactAwareResult mode op x y) := by
  classical
  have hbranch :
      ieeePrimitiveValueBranchResult? op
        (IeeeValue.finite x) (IeeeValue.finite y) = none := by
    cases hbranch :
        ieeePrimitiveValueBranchResult? op
          (IeeeValue.finite x) (IeeeValue.finite y) with
    | none => rfl
    | some r =>
        exact False.elim
          (hno ⟨r, ieeePrimitiveValueBranchResult?_sound hbranch⟩)
  have hzero :
      ieeePrimitiveAddSubZeroSumResult? mode op
        (IeeeValue.finite x) (IeeeValue.finite y) = none := by
    cases hzero :
        ieeePrimitiveAddSubZeroSumResult? mode op
          (IeeeValue.finite x) (IeeeValue.finite y) with
    | none => rfl
    | some r =>
        exact False.elim
          ((ieeePrimitiveAddSubZeroSumResult_finite_absurd mode op x y)
            ⟨r, ieeePrimitiveAddSubZeroSumResult?_sound hzero⟩)
  simp [ieeeRoundToModeOpInexactAwareValueResult?, hbranch, hzero]
theorem ieeeRoundToModeOpInexactAwareValueResult?_sound
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : fmt.ieeeRoundToModeOpInexactAwareValueResult? mode op x y =
        some r) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult mode op x y r := by
  classical
  cases hbranch : ieeePrimitiveValueBranchResult? op x y with
  | some rbranch =>
      have hr : r = rbranch := by
        simpa [ieeeRoundToModeOpInexactAwareValueResult?, hbranch] using h.symm
      subst r
      exact
        fmt.ieeeRoundToModeOpInexactAwareValueResult_branch
          (ieeePrimitiveValueBranchResult?_sound hbranch)
  | none =>
      cases hzero : ieeePrimitiveAddSubZeroSumResult? mode op x y with
      | some rzero =>
          have hr : r = rzero := by
            simpa [ieeeRoundToModeOpInexactAwareValueResult?, hbranch, hzero]
              using h.symm
          subst r
          exact
            fmt.ieeeRoundToModeOpInexactAwareValueResult_addSubZeroSum
              (ieeePrimitiveAddSubZeroSumResult?_sound hzero)
      | none =>
          cases x <;> cases y <;>
            simp [ieeeRoundToModeOpInexactAwareValueResult?, hbranch, hzero] at h
          · cases h
            exact
              fmt.ieeeRoundToModeOpInexactAwareValueResult_finite_of_no_value_branch
                (ieeePrimitiveValueBranchResult_finite_absurd_of_valueBranchDefault?_none
                  hbranch)
theorem ieeeRoundToModeOpInexactAwareValueResult?_finite_of_division_guard
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) {x y : ℝ}
    (hdiv : op = BasicOp.div → y ≠ 0) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode op
      (IeeeValue.finite x) (IeeeValue.finite y) =
      some (fmt.ieeeRoundToModeOpInexactAwareResult mode op x y) :=
  fmt.ieeeRoundToModeOpInexactAwareValueResult?_finite_of_no_value_branch
    (ieeePrimitiveValueBranchResult_finite_absurd_of_division_guard op hdiv)
theorem ieeeRoundToModeOpInexactAwareValueResult?_ieeeInexactResult_of_finiteNormalRange_of_ne
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y))
    (hdiv : op = BasicOp.div → y ≠ 0)
    (hne :
      fmt.finiteRoundToModeOp mode op x y ≠ BasicOp.exact op x y) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode op
        (IeeeValue.finite x) (IeeeValue.finite y) =
        some (fmt.ieeeRoundToModeOpInexactAwareResult mode op x y) ∧
      fmt.ieeeRoundToModeOpInexactAwareValueResult mode op
        (IeeeValue.finite x) (IeeeValue.finite y)
        (fmt.ieeeRoundToModeOpInexactAwareResult mode op x y) ∧
      ieeeInexactResult (BasicOp.exact op x y)
        (fmt.finiteRoundToModeOp mode op x y)
        (fmt.ieeeRoundToModeOpInexactAwareResult mode op x y) :=
  ⟨fmt.ieeeRoundToModeOpInexactAwareValueResult?_finite_of_division_guard
      mode op hdiv,
    fmt.ieeeRoundToModeOpInexactAwareValueResult_finite_of_division_guard
      mode op hdiv,
    fmt.ieeeRoundToModeOpInexactAwareResult_ieeeInexactResult_of_finiteNormalRange_of_ne
      hxy hne⟩
theorem ieeeRoundToModeOpInexactAwareValueResult?_finiteNoFlags_of_finiteNormalRange_of_eq
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y))
    (hdiv : op = BasicOp.div → y ≠ 0)
    (heq :
      fmt.finiteRoundToModeOp mode op x y = BasicOp.exact op x y) :
    fmt.ieeeRoundToModeOpInexactAwareValueResult? mode op
        (IeeeValue.finite x) (IeeeValue.finite y) =
        some (fmt.ieeeRoundToModeOpInexactAwareResult mode op x y) ∧
      fmt.ieeeRoundToModeOpInexactAwareValueResult mode op
        (IeeeValue.finite x) (IeeeValue.finite y)
        (fmt.ieeeRoundToModeOpInexactAwareResult mode op x y) ∧
      fmt.ieeeRoundToModeOpInexactAwareResult mode op x y =
        IeeeOperationResult.finiteNoFlags
          (fmt.finiteRoundToModeOp mode op x y) :=
  ⟨fmt.ieeeRoundToModeOpInexactAwareValueResult?_finite_of_division_guard
      mode op hdiv,
    fmt.ieeeRoundToModeOpInexactAwareValueResult_finite_of_division_guard
      mode op hdiv,
    fmt.ieeeRoundToModeOpInexactAwareResult_eq_finiteNoFlags_of_finiteNormalRange_of_eq
      hxy heq⟩

end FloatingPointFormat

end

end NumStability
