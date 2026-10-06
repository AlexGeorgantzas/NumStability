import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic.IeeeValue
import NumStability.FloatingPoint.Model

namespace NumStability

/-!
# IeeeExceptions

Extracted without change from FloatingPointArithmetic.
-/

noncomputable section

/-- IEEE-facing finite inexact result: the operation returns the correctly
rounded finite value but raises the inexact flag because the rounded value is
not the exact real result.  This is the Table 2.2 finite branch; underflow and
overflow have their own predicates because they may raise additional flags. -/
def ieeeInexactResult
    (exact rounded : ℝ) (r : IeeeOperationResult) : Prop :=
  rounded ≠ exact ∧
    r.value = IeeeValue.finite rounded ∧
      r.hasFlag IeeeExceptionFlag.inexact
/-- Default finite inexact result with exactly the inexact flag set. -/
def ieeeInexactDefaultResult (rounded : ℝ) : IeeeOperationResult where
  value := IeeeValue.finite rounded
  flag := fun flag => flag = IeeeExceptionFlag.inexact
theorem ieeeInexactDefaultResult_value (rounded : ℝ) :
    (ieeeInexactDefaultResult rounded).value = IeeeValue.finite rounded := rfl
theorem ieeeInexactDefaultResult_hasFlag_iff
    (rounded : ℝ) (flag : IeeeExceptionFlag) :
    (ieeeInexactDefaultResult rounded).hasFlag flag ↔
      flag = IeeeExceptionFlag.inexact := by
  rfl
theorem ieeeInexactDefaultResult_hasInexactFlag
    (rounded : ℝ) :
    (ieeeInexactDefaultResult rounded).hasFlag IeeeExceptionFlag.inexact := by
  simp [ieeeInexactDefaultResult, IeeeOperationResult.hasFlag]
theorem ieeeInexactDefaultResult_ieeeInexactResult
    {exact rounded : ℝ} (hne : rounded ≠ exact) :
    ieeeInexactResult exact rounded (ieeeInexactDefaultResult rounded) := by
  exact ⟨hne, rfl, ieeeInexactDefaultResult_hasInexactFlag rounded⟩
theorem ieeeInexactResult_rounded_ne_exact
    {exact rounded : ℝ} {r : IeeeOperationResult}
    (h : ieeeInexactResult exact rounded r) :
    rounded ≠ exact :=
  h.1
theorem ieeeInexactResult_value
    {exact rounded : ℝ} {r : IeeeOperationResult}
    (h : ieeeInexactResult exact rounded r) :
    r.value = IeeeValue.finite rounded :=
  h.2.1
theorem ieeeInexactResult_hasInexactFlag
    {exact rounded : ℝ} {r : IeeeOperationResult}
    (h : ieeeInexactResult exact rounded r) :
    r.hasFlag IeeeExceptionFlag.inexact :=
  h.2.2
theorem ieeeInexactResult_not_noFlags
    {exact rounded : ℝ} {r : IeeeOperationResult}
    (h : ieeeInexactResult exact rounded r) :
    ¬ r.noFlags := by
  intro hno
  exact hno IeeeExceptionFlag.inexact
    (ieeeInexactResult_hasInexactFlag h)
theorem ieeeInexactResult_not_finiteNoFlags
    {exact rounded z : ℝ} :
    ¬ ieeeInexactResult exact rounded (IeeeOperationResult.finiteNoFlags z) := by
  intro h
  exact IeeeOperationResult.finiteNoFlags_not_hasFlag z
    IeeeExceptionFlag.inexact
    (ieeeInexactResult_hasInexactFlag h)
/-- Generic IEEE-facing invalid-operation result: the value is NaN and the
invalid-operation flag is set.  This is the common result predicate used by
operation-specific invalid branches. -/
def ieeeInvalidOperationResult (r : IeeeOperationResult) : Prop :=
  r.value = IeeeValue.nan ∧
    r.hasFlag IeeeExceptionFlag.invalidOperation
/-- Default invalid-operation result, returning NaN and setting exactly the
invalid-operation flag. -/
def ieeeInvalidOperationDefaultResult : IeeeOperationResult where
  value := IeeeValue.nan
  flag := fun flag => flag = IeeeExceptionFlag.invalidOperation
theorem ieeeInvalidOperationDefaultResult_value :
    ieeeInvalidOperationDefaultResult.value = IeeeValue.nan := rfl
theorem ieeeInvalidOperationDefaultResult_hasFlag_iff
    (flag : IeeeExceptionFlag) :
    ieeeInvalidOperationDefaultResult.hasFlag flag ↔
      flag = IeeeExceptionFlag.invalidOperation := by
  rfl
theorem ieeeInvalidOperationDefaultResult_hasInvalidOperationFlag :
    ieeeInvalidOperationDefaultResult.hasFlag
      IeeeExceptionFlag.invalidOperation := by
  simp [ieeeInvalidOperationDefaultResult, IeeeOperationResult.hasFlag]
theorem ieeeInvalidOperationDefaultResult_ieeeInvalidOperationResult :
    ieeeInvalidOperationResult ieeeInvalidOperationDefaultResult := by
  exact ⟨rfl, ieeeInvalidOperationDefaultResult_hasInvalidOperationFlag⟩
theorem ieeeInvalidOperationResult_value
    {r : IeeeOperationResult} (h : ieeeInvalidOperationResult r) :
    r.value = IeeeValue.nan :=
  h.1
theorem ieeeInvalidOperationResult_hasInvalidOperationFlag
    {r : IeeeOperationResult} (h : ieeeInvalidOperationResult r) :
    r.hasFlag IeeeExceptionFlag.invalidOperation :=
  h.2
theorem ieeeInvalidOperationResult_not_noFlags
    {r : IeeeOperationResult} (h : ieeeInvalidOperationResult r) :
    ¬ r.noFlags := by
  intro hno
  exact hno IeeeExceptionFlag.invalidOperation
    (ieeeInvalidOperationResult_hasInvalidOperationFlag h)
theorem ieeeInvalidOperationResult_not_finiteNoFlags {x : ℝ} :
    ¬ ieeeInvalidOperationResult (IeeeOperationResult.finiteNoFlags x) := by
  intro h
  exact IeeeOperationResult.finiteNoFlags_not_hasFlag x
    IeeeExceptionFlag.invalidOperation
    (ieeeInvalidOperationResult_hasInvalidOperationFlag h)
/-- IEEE division-by-zero input predicate for Table 2.2's `finite nonzero/0`
case.  The zero denominator may be either signed zero or the ordinary modeled
finite zero. -/
def ieeeDivisionByZeroInput (x y : IeeeValue) : Prop :=
  x.isFinite ∧ ¬ x.isZero ∧ y.isZero
/-- IEEE division-by-zero result predicate: a finite nonzero value divided by
zero returns an infinity and raises the division-by-zero flag.  The sign of the
infinity is intentionally left to a later full IEEE operation semantics. -/
def ieeeDivisionByZeroResult
    (x y : IeeeValue) (r : IeeeOperationResult) : Prop :=
  ieeeDivisionByZeroInput x y ∧
    r.value.isInfinite ∧ r.hasFlag IeeeExceptionFlag.divisionByZero
/-- Default division-by-zero result with a supplied infinity value and exactly
the division-by-zero flag.  The supplied value lets this predicate layer avoid
committing to a sign-selection rule before full signed-zero operation semantics
is available. -/
def ieeeDivisionByZeroDefaultResult (value : IeeeValue) : IeeeOperationResult where
  value := value
  flag := fun flag => flag = IeeeExceptionFlag.divisionByZero
/-- Signed default infinity for the finite-nonzero divided by signed-zero
cases.  A denominator represented only as `finite 0` has no IEEE sign bit in
this local value model, so the selector returns `none` there. -/
def ieeeDivisionByZeroSignedValue : IeeeValue → IeeeValue → Option IeeeValue
  | IeeeValue.finite x, IeeeValue.posZero =>
      if 0 < x then some IeeeValue.posInf
      else if x < 0 then some IeeeValue.negInf
      else none
  | IeeeValue.finite x, IeeeValue.negZero =>
      if 0 < x then some IeeeValue.negInf
      else if x < 0 then some IeeeValue.posInf
      else none
  | _, _ => none
theorem ieeeDivisionByZeroInput_finite_nonzero
    {x : ℝ} {y : IeeeValue} (hx : x ≠ 0) (hy : y.isZero) :
    ieeeDivisionByZeroInput (IeeeValue.finite x) y := by
  exact ⟨IeeeValue.finite_isFinite x, by simpa [IeeeValue.isZero] using hx, hy⟩
theorem ieeeDivisionByZeroInput_finite_nonzero_posZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeeDivisionByZeroInput (IeeeValue.finite x) IeeeValue.posZero :=
  ieeeDivisionByZeroInput_finite_nonzero hx IeeeValue.posZero_isZero
theorem ieeeDivisionByZeroInput_finite_nonzero_negZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeeDivisionByZeroInput (IeeeValue.finite x) IeeeValue.negZero :=
  ieeeDivisionByZeroInput_finite_nonzero hx IeeeValue.negZero_isZero
theorem ieeeDivisionByZeroInput_finite_nonzero_finite_zero
    {x : ℝ} (hx : x ≠ 0) :
    ieeeDivisionByZeroInput (IeeeValue.finite x) (IeeeValue.finite 0) :=
  ieeeDivisionByZeroInput_finite_nonzero hx IeeeValue.finite_zero_isZero
theorem ieeeDivisionByZeroSignedValue_pos_over_posZero
    {x : ℝ} (hx : 0 < x) :
    ieeeDivisionByZeroSignedValue (IeeeValue.finite x) IeeeValue.posZero =
      some IeeeValue.posInf := by
  simp [ieeeDivisionByZeroSignedValue, hx]
theorem ieeeDivisionByZeroSignedValue_neg_over_posZero
    {x : ℝ} (hx : x < 0) :
    ieeeDivisionByZeroSignedValue (IeeeValue.finite x) IeeeValue.posZero =
      some IeeeValue.negInf := by
  have hnot : ¬ 0 < x := not_lt.mpr (le_of_lt hx)
  simp [ieeeDivisionByZeroSignedValue, hnot, hx]
theorem ieeeDivisionByZeroSignedValue_pos_over_negZero
    {x : ℝ} (hx : 0 < x) :
    ieeeDivisionByZeroSignedValue (IeeeValue.finite x) IeeeValue.negZero =
      some IeeeValue.negInf := by
  simp [ieeeDivisionByZeroSignedValue, hx]
theorem ieeeDivisionByZeroSignedValue_neg_over_negZero
    {x : ℝ} (hx : x < 0) :
    ieeeDivisionByZeroSignedValue (IeeeValue.finite x) IeeeValue.negZero =
      some IeeeValue.posInf := by
  have hnot : ¬ 0 < x := not_lt.mpr (le_of_lt hx)
  simp [ieeeDivisionByZeroSignedValue, hnot, hx]
theorem ieeeDivisionByZeroSignedValue_none_finite_zero
    (x : ℝ) :
    ieeeDivisionByZeroSignedValue (IeeeValue.finite x) (IeeeValue.finite 0) =
      none := by
  simp [ieeeDivisionByZeroSignedValue]
/-- Repository default infinity selector for the ordinary modeled `finite 0`
denominator branch.  Since `finite 0` carries no signed-zero bit in
`IeeeValue`, this records the signless finite-zero convention separately from
the true signed-zero selectors above. -/
def ieeeDivisionByZeroFiniteZeroDefaultValue (x : ℝ) : IeeeValue :=
  if 0 < x then IeeeValue.posInf else IeeeValue.negInf
theorem ieeeDivisionByZeroFiniteZeroDefaultValue_pos
    {x : ℝ} (hx : 0 < x) :
    ieeeDivisionByZeroFiniteZeroDefaultValue x = IeeeValue.posInf := by
  simp [ieeeDivisionByZeroFiniteZeroDefaultValue, hx]
theorem ieeeDivisionByZeroFiniteZeroDefaultValue_neg
    {x : ℝ} (hx : x < 0) :
    ieeeDivisionByZeroFiniteZeroDefaultValue x = IeeeValue.negInf := by
  have hnot : ¬ 0 < x := not_lt.mpr (le_of_lt hx)
  simp [ieeeDivisionByZeroFiniteZeroDefaultValue, hnot]
theorem ieeeDivisionByZeroFiniteZeroDefaultValue_isInfinite
    (x : ℝ) :
    (ieeeDivisionByZeroFiniteZeroDefaultValue x).isInfinite := by
  by_cases hpos : 0 < x
  · simp [ieeeDivisionByZeroFiniteZeroDefaultValue, hpos, IeeeValue.isInfinite]
  · simp [ieeeDivisionByZeroFiniteZeroDefaultValue, hpos, IeeeValue.isInfinite]
theorem ieeeDivisionByZeroDefaultResult_value
    (value : IeeeValue) :
    (ieeeDivisionByZeroDefaultResult value).value = value := rfl
theorem ieeeDivisionByZeroDefaultResult_hasFlag_iff
    (value : IeeeValue) (flag : IeeeExceptionFlag) :
    (ieeeDivisionByZeroDefaultResult value).hasFlag flag ↔
      flag = IeeeExceptionFlag.divisionByZero := by
  rfl
theorem ieeeDivisionByZeroDefaultResult_hasDivisionByZeroFlag
    (value : IeeeValue) :
    (ieeeDivisionByZeroDefaultResult value).hasFlag
      IeeeExceptionFlag.divisionByZero := by
  simp [ieeeDivisionByZeroDefaultResult, IeeeOperationResult.hasFlag]
theorem ieeeDivisionByZeroDefaultResult_ieeeDivisionByZeroResult
    {x y value : IeeeValue}
    (hinput : ieeeDivisionByZeroInput x y) (hvalue : value.isInfinite) :
    ieeeDivisionByZeroResult x y
      (ieeeDivisionByZeroDefaultResult value) := by
  exact
    ⟨hinput, by simpa [ieeeDivisionByZeroDefaultResult] using hvalue,
      ieeeDivisionByZeroDefaultResult_hasDivisionByZeroFlag value⟩
theorem ieeeDivisionByZeroDefaultResult_posInf_ieeeDivisionByZeroResult
    {x y : IeeeValue} (hinput : ieeeDivisionByZeroInput x y) :
    ieeeDivisionByZeroResult x y
      (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) :=
  ieeeDivisionByZeroDefaultResult_ieeeDivisionByZeroResult
    hinput IeeeValue.posInf_isInfinite
theorem ieeeDivisionByZeroDefaultResult_negInf_ieeeDivisionByZeroResult
    {x y : IeeeValue} (hinput : ieeeDivisionByZeroInput x y) :
    ieeeDivisionByZeroResult x y
      (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) :=
  ieeeDivisionByZeroDefaultResult_ieeeDivisionByZeroResult
    hinput IeeeValue.negInf_isInfinite
theorem ieeeDivisionByZeroDefaultResult_pos_over_posZero
    {x : ℝ} (hx : 0 < x) :
    ieeeDivisionByZeroResult (IeeeValue.finite x) IeeeValue.posZero
      (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) :=
  ieeeDivisionByZeroDefaultResult_posInf_ieeeDivisionByZeroResult
    (ieeeDivisionByZeroInput_finite_nonzero_posZero (ne_of_gt hx))
theorem ieeeDivisionByZeroDefaultResult_neg_over_posZero
    {x : ℝ} (hx : x < 0) :
    ieeeDivisionByZeroResult (IeeeValue.finite x) IeeeValue.posZero
      (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) :=
  ieeeDivisionByZeroDefaultResult_negInf_ieeeDivisionByZeroResult
    (ieeeDivisionByZeroInput_finite_nonzero_posZero (ne_of_lt hx))
theorem ieeeDivisionByZeroDefaultResult_pos_over_negZero
    {x : ℝ} (hx : 0 < x) :
    ieeeDivisionByZeroResult (IeeeValue.finite x) IeeeValue.negZero
      (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) :=
  ieeeDivisionByZeroDefaultResult_negInf_ieeeDivisionByZeroResult
    (ieeeDivisionByZeroInput_finite_nonzero_negZero (ne_of_gt hx))
theorem ieeeDivisionByZeroDefaultResult_neg_over_negZero
    {x : ℝ} (hx : x < 0) :
    ieeeDivisionByZeroResult (IeeeValue.finite x) IeeeValue.negZero
      (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) :=
  ieeeDivisionByZeroDefaultResult_posInf_ieeeDivisionByZeroResult
    (ieeeDivisionByZeroInput_finite_nonzero_negZero (ne_of_lt hx))
theorem ieeeDivisionByZeroDefaultResult_finite_zero
    {x : ℝ} (hx : x ≠ 0) :
    ieeeDivisionByZeroResult (IeeeValue.finite x) (IeeeValue.finite 0)
      (ieeeDivisionByZeroDefaultResult
        (ieeeDivisionByZeroFiniteZeroDefaultValue x)) :=
  ieeeDivisionByZeroDefaultResult_ieeeDivisionByZeroResult
    (ieeeDivisionByZeroInput_finite_nonzero_finite_zero hx)
    (ieeeDivisionByZeroFiniteZeroDefaultValue_isInfinite x)
theorem ieeeDivisionByZeroDefaultResult_pos_over_finite_zero
    {x : ℝ} (hx : 0 < x) :
    ieeeDivisionByZeroResult (IeeeValue.finite x) (IeeeValue.finite 0)
      (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) := by
  rw [← ieeeDivisionByZeroFiniteZeroDefaultValue_pos hx]
  exact ieeeDivisionByZeroDefaultResult_finite_zero (ne_of_gt hx)
theorem ieeeDivisionByZeroDefaultResult_neg_over_finite_zero
    {x : ℝ} (hx : x < 0) :
    ieeeDivisionByZeroResult (IeeeValue.finite x) (IeeeValue.finite 0)
      (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) := by
  rw [← ieeeDivisionByZeroFiniteZeroDefaultValue_neg hx]
  exact ieeeDivisionByZeroDefaultResult_finite_zero (ne_of_lt hx)
/-- Concrete default selector for the modeled IEEE division-by-zero branch.
It covers finite nonzero numerators divided by a signed zero, and the local
signless `finite 0` denominator convention.  The invalid `0/0` cases return
`none` here because they belong to the invalid-operation branch. -/
noncomputable def ieeeDivisionByZeroDefaultResult?
    (x y : IeeeValue) : Option IeeeOperationResult := by
  classical
  exact
    match x, y with
    | IeeeValue.finite xr, IeeeValue.posZero =>
        if 0 < xr then
          some (ieeeDivisionByZeroDefaultResult IeeeValue.posInf)
        else if xr < 0 then
          some (ieeeDivisionByZeroDefaultResult IeeeValue.negInf)
        else
          none
    | IeeeValue.finite xr, IeeeValue.negZero =>
        if 0 < xr then
          some (ieeeDivisionByZeroDefaultResult IeeeValue.negInf)
        else if xr < 0 then
          some (ieeeDivisionByZeroDefaultResult IeeeValue.posInf)
        else
          none
    | IeeeValue.finite xr, IeeeValue.finite yr =>
        if yr = 0 then
          if 0 < xr then
            some (ieeeDivisionByZeroDefaultResult IeeeValue.posInf)
          else if xr < 0 then
            some (ieeeDivisionByZeroDefaultResult IeeeValue.negInf)
          else
            none
        else
          none
    | _, _ => none
theorem ieeeDivisionByZeroDefaultResult?_pos_over_posZero
    {x : ℝ} (hx : 0 < x) :
    ieeeDivisionByZeroDefaultResult?
        (IeeeValue.finite x) IeeeValue.posZero =
      some (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) := by
  simp [ieeeDivisionByZeroDefaultResult?, hx]
theorem ieeeDivisionByZeroDefaultResult?_neg_over_posZero
    {x : ℝ} (hx : x < 0) :
    ieeeDivisionByZeroDefaultResult?
        (IeeeValue.finite x) IeeeValue.posZero =
      some (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) := by
  have hnot : ¬ 0 < x := not_lt.mpr (le_of_lt hx)
  simp [ieeeDivisionByZeroDefaultResult?, hnot, hx]
theorem ieeeDivisionByZeroDefaultResult?_pos_over_negZero
    {x : ℝ} (hx : 0 < x) :
    ieeeDivisionByZeroDefaultResult?
        (IeeeValue.finite x) IeeeValue.negZero =
      some (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) := by
  simp [ieeeDivisionByZeroDefaultResult?, hx]
theorem ieeeDivisionByZeroDefaultResult?_neg_over_negZero
    {x : ℝ} (hx : x < 0) :
    ieeeDivisionByZeroDefaultResult?
        (IeeeValue.finite x) IeeeValue.negZero =
      some (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) := by
  have hnot : ¬ 0 < x := not_lt.mpr (le_of_lt hx)
  simp [ieeeDivisionByZeroDefaultResult?, hnot, hx]
theorem ieeeDivisionByZeroDefaultResult?_pos_over_finite_zero
    {x : ℝ} (hx : 0 < x) :
    ieeeDivisionByZeroDefaultResult?
        (IeeeValue.finite x) (IeeeValue.finite 0) =
      some (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) := by
  simp [ieeeDivisionByZeroDefaultResult?, hx]
theorem ieeeDivisionByZeroDefaultResult?_neg_over_finite_zero
    {x : ℝ} (hx : x < 0) :
    ieeeDivisionByZeroDefaultResult?
        (IeeeValue.finite x) (IeeeValue.finite 0) =
      some (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) := by
  have hnot : ¬ 0 < x := not_lt.mpr (le_of_lt hx)
  simp [ieeeDivisionByZeroDefaultResult?, hnot, hx]
theorem ieeeDivisionByZeroDefaultResult?_sound
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeDivisionByZeroDefaultResult? x y = some r) :
    ieeeDivisionByZeroResult x y r := by
  classical
  cases x <;> cases y <;> simp [ieeeDivisionByZeroDefaultResult?] at h
  · rename_i x y
    by_cases hy : y = 0
    · subst y
      by_cases hpos : 0 < x
      · simp [hpos] at h
        cases h
        exact ieeeDivisionByZeroDefaultResult_pos_over_finite_zero hpos
      · by_cases hneg : x < 0
        · simp [hpos, hneg] at h
          cases h
          exact ieeeDivisionByZeroDefaultResult_neg_over_finite_zero hneg
        · simp [hpos, hneg] at h
    · simp [hy] at h
  · rename_i x
    by_cases hpos : 0 < x
    · simp [hpos] at h
      cases h
      exact ieeeDivisionByZeroDefaultResult_pos_over_posZero hpos
    · by_cases hneg : x < 0
      · simp [hpos, hneg] at h
        cases h
        exact ieeeDivisionByZeroDefaultResult_neg_over_posZero hneg
      · simp [hpos, hneg] at h
  · rename_i x
    by_cases hpos : 0 < x
    · simp [hpos] at h
      cases h
      exact ieeeDivisionByZeroDefaultResult_pos_over_negZero hpos
    · by_cases hneg : x < 0
      · simp [hpos, hneg] at h
        cases h
        exact ieeeDivisionByZeroDefaultResult_neg_over_negZero hneg
      · simp [hpos, hneg] at h
theorem ieeeDivisionByZeroResult_input
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeDivisionByZeroResult x y r) :
    ieeeDivisionByZeroInput x y :=
  h.1
theorem ieeeDivisionByZeroResult_value_isInfinite
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeDivisionByZeroResult x y r) :
    r.value.isInfinite :=
  h.2.1
theorem ieeeDivisionByZeroResult_hasDivisionByZeroFlag
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeDivisionByZeroResult x y r) :
    r.hasFlag IeeeExceptionFlag.divisionByZero :=
  h.2.2
theorem ieeeDivisionByZeroResult_not_noFlags
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeDivisionByZeroResult x y r) :
    ¬ r.noFlags := by
  intro hno
  exact hno IeeeExceptionFlag.divisionByZero
    (ieeeDivisionByZeroResult_hasDivisionByZeroFlag h)
theorem ieeeDivisionByZeroResult_not_finiteNoFlags
    {x y : IeeeValue} {z : ℝ} :
    ¬ ieeeDivisionByZeroResult x y (IeeeOperationResult.finiteNoFlags z) := by
  intro h
  exact IeeeOperationResult.finiteNoFlags_not_hasFlag z
    IeeeExceptionFlag.divisionByZero
    (ieeeDivisionByZeroResult_hasDivisionByZeroFlag h)
/-- IEEE square-root invalid-operation branch for negative real inputs. -/
def ieeeSqrtInvalidResult (x : ℝ) (r : IeeeOperationResult) : Prop :=
  x < 0 ∧ ieeeInvalidOperationResult r
/-- Default square-root invalid-operation result.  The input is retained in the
API so the constructor lines up with `ieeeSqrtInvalidResult`. -/
def ieeeSqrtInvalidDefaultResult (_x : ℝ) : IeeeOperationResult :=
  ieeeInvalidOperationDefaultResult
theorem ieeeSqrtInvalidDefaultResult_ieeeSqrtInvalidResult
    {x : ℝ} (hx : x < 0) :
    ieeeSqrtInvalidResult x (ieeeSqrtInvalidDefaultResult x) := by
  exact ⟨hx, ieeeInvalidOperationDefaultResult_ieeeInvalidOperationResult⟩
theorem ieeeSqrtInvalidResult_input_neg
    {x : ℝ} {r : IeeeOperationResult}
    (h : ieeeSqrtInvalidResult x r) :
    x < 0 :=
  h.1
theorem ieeeSqrtInvalidResult_ieeeInvalidOperationResult
    {x : ℝ} {r : IeeeOperationResult}
    (h : ieeeSqrtInvalidResult x r) :
    ieeeInvalidOperationResult r :=
  h.2
theorem ieeeSqrtInvalidResult_value
    {x : ℝ} {r : IeeeOperationResult}
    (h : ieeeSqrtInvalidResult x r) :
    r.value = IeeeValue.nan :=
  ieeeInvalidOperationResult_value h.2
theorem ieeeSqrtInvalidResult_hasInvalidOperationFlag
    {x : ℝ} {r : IeeeOperationResult}
    (h : ieeeSqrtInvalidResult x r) :
    r.hasFlag IeeeExceptionFlag.invalidOperation :=
  ieeeInvalidOperationResult_hasInvalidOperationFlag h.2
/-- IEEE-facing square-root special-value predicate for non-finite inputs.
This records the quiet/default branches modeled here: NaN propagates to NaN
with no flags, positive infinity maps to positive infinity with no flags, and
negative infinity raises invalid operation and returns NaN.  Signaling NaNs,
payloads, traps, and signed-zero behavior remain outside this predicate. -/
def ieeeSqrtSpecialValueResult
    (v : IeeeValue) (r : IeeeOperationResult) : Prop :=
  match v with
  | IeeeValue.finite _ => False
  | IeeeValue.posZero => False
  | IeeeValue.negZero => False
  | IeeeValue.posInf => r.value = IeeeValue.posInf ∧ r.noFlags
  | IeeeValue.negInf => ieeeInvalidOperationResult r
  | IeeeValue.nan => r.value = IeeeValue.nan ∧ r.noFlags
theorem ieeeSqrtSpecialValueResult_nan_valueNoFlags :
    ieeeSqrtSpecialValueResult IeeeValue.nan
      (IeeeOperationResult.valueNoFlags IeeeValue.nan) := by
  exact ⟨rfl, IeeeOperationResult.valueNoFlags_noFlags IeeeValue.nan⟩
theorem ieeeSqrtSpecialValueResult_posInf_valueNoFlags :
    ieeeSqrtSpecialValueResult IeeeValue.posInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  exact ⟨rfl, IeeeOperationResult.valueNoFlags_noFlags IeeeValue.posInf⟩
theorem ieeeSqrtSpecialValueResult_negInf_invalid :
    ieeeSqrtSpecialValueResult IeeeValue.negInf
      ieeeInvalidOperationDefaultResult :=
  ieeeInvalidOperationDefaultResult_ieeeInvalidOperationResult
theorem ieeeSqrtSpecialValueResult_value_nan
    {r : IeeeOperationResult}
    (h : ieeeSqrtSpecialValueResult IeeeValue.nan r) :
    r.value = IeeeValue.nan :=
  h.1
theorem ieeeSqrtSpecialValueResult_noFlags_nan
    {r : IeeeOperationResult}
    (h : ieeeSqrtSpecialValueResult IeeeValue.nan r) :
    r.noFlags :=
  h.2
theorem ieeeSqrtSpecialValueResult_value_posInf
    {r : IeeeOperationResult}
    (h : ieeeSqrtSpecialValueResult IeeeValue.posInf r) :
    r.value = IeeeValue.posInf :=
  h.1
theorem ieeeSqrtSpecialValueResult_noFlags_posInf
    {r : IeeeOperationResult}
    (h : ieeeSqrtSpecialValueResult IeeeValue.posInf r) :
    r.noFlags :=
  h.2
theorem ieeeSqrtSpecialValueResult_negInf_ieeeInvalidOperationResult
    {r : IeeeOperationResult}
    (h : ieeeSqrtSpecialValueResult IeeeValue.negInf r) :
    ieeeInvalidOperationResult r :=
  h
/-- IEEE square-root signed-zero predicate: square root preserves the sign of
zero and raises no flags.  The ordinary real payload `finite 0` remains the
source-facing real zero; IEEE signed zeros use `posZero` and `negZero`. -/
def ieeeSqrtSignedZeroResult
    (v : IeeeValue) (r : IeeeOperationResult) : Prop :=
  match v with
  | IeeeValue.posZero => r.value = IeeeValue.posZero ∧ r.noFlags
  | IeeeValue.negZero => r.value = IeeeValue.negZero ∧ r.noFlags
  | _ => False
theorem ieeeSqrtSignedZeroResult_posZero_valueNoFlags :
    ieeeSqrtSignedZeroResult IeeeValue.posZero
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  exact ⟨rfl, IeeeOperationResult.valueNoFlags_noFlags IeeeValue.posZero⟩
theorem ieeeSqrtSignedZeroResult_negZero_valueNoFlags :
    ieeeSqrtSignedZeroResult IeeeValue.negZero
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  exact ⟨rfl, IeeeOperationResult.valueNoFlags_noFlags IeeeValue.negZero⟩
theorem ieeeSqrtSignedZeroResult_value_posZero
    {r : IeeeOperationResult}
    (h : ieeeSqrtSignedZeroResult IeeeValue.posZero r) :
    r.value = IeeeValue.posZero :=
  h.1
theorem ieeeSqrtSignedZeroResult_noFlags_posZero
    {r : IeeeOperationResult}
    (h : ieeeSqrtSignedZeroResult IeeeValue.posZero r) :
    r.noFlags :=
  h.2
theorem ieeeSqrtSignedZeroResult_value_negZero
    {r : IeeeOperationResult}
    (h : ieeeSqrtSignedZeroResult IeeeValue.negZero r) :
    r.value = IeeeValue.negZero :=
  h.1
theorem ieeeSqrtSignedZeroResult_noFlags_negZero
    {r : IeeeOperationResult}
    (h : ieeeSqrtSignedZeroResult IeeeValue.negZero r) :
    r.noFlags :=
  h.2
/-- IEEE quiet/default NaN propagation for primitive binary operations:
if either input is the modeled NaN value, the result is NaN with no flags.
Signaling NaNs and payload propagation are intentionally not modeled here. -/
def ieeeQuietNaNPropagationResult
    (x y : IeeeValue) (r : IeeeOperationResult) : Prop :=
  (x.isNaN ∨ y.isNaN) ∧ r.value = IeeeValue.nan ∧ r.noFlags
theorem ieeeQuietNaNPropagationResult_left_nan
    (y : IeeeValue) :
    ieeeQuietNaNPropagationResult IeeeValue.nan y
      (IeeeOperationResult.valueNoFlags IeeeValue.nan) := by
  exact
    ⟨Or.inl IeeeValue.nan_isNaN, rfl,
      IeeeOperationResult.valueNoFlags_noFlags IeeeValue.nan⟩
theorem ieeeQuietNaNPropagationResult_right_nan
    (x : IeeeValue) :
    ieeeQuietNaNPropagationResult x IeeeValue.nan
      (IeeeOperationResult.valueNoFlags IeeeValue.nan) := by
  exact
    ⟨Or.inr IeeeValue.nan_isNaN, rfl,
      IeeeOperationResult.valueNoFlags_noFlags IeeeValue.nan⟩
theorem ieeeQuietNaNPropagationResult_value
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeQuietNaNPropagationResult x y r) :
    r.value = IeeeValue.nan :=
  h.2.1
theorem ieeeQuietNaNPropagationResult_noFlags
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeQuietNaNPropagationResult x y r) :
    r.noFlags :=
  h.2.2
/-- Concrete selector for the modeled quiet/default NaN propagation branch.
The repository currently has a single `nan` value, so this selector does not
attempt to model signaling NaNs, payload selection, or trap behavior. -/
def ieeeQuietNaNPropagationResult?
    (x y : IeeeValue) : Option IeeeOperationResult :=
  match x, y with
  | IeeeValue.nan, _ =>
      some (IeeeOperationResult.valueNoFlags IeeeValue.nan)
  | _, IeeeValue.nan =>
      some (IeeeOperationResult.valueNoFlags IeeeValue.nan)
  | _, _ => none
theorem ieeeQuietNaNPropagationResult?_left_nan
    (y : IeeeValue) :
    ieeeQuietNaNPropagationResult? IeeeValue.nan y =
      some (IeeeOperationResult.valueNoFlags IeeeValue.nan) := by
  rfl
theorem ieeeQuietNaNPropagationResult?_right_nan
    (x : IeeeValue) :
    ieeeQuietNaNPropagationResult? x IeeeValue.nan =
      some (IeeeOperationResult.valueNoFlags IeeeValue.nan) := by
  cases x <;> rfl
theorem ieeeQuietNaNPropagationResult?_none_of_not_isNaN
    {x y : IeeeValue} (hx : ¬ x.isNaN) (hy : ¬ y.isNaN) :
    ieeeQuietNaNPropagationResult? x y = none := by
  cases x <;> cases y <;>
    simp [ieeeQuietNaNPropagationResult?, IeeeValue.isNaN] at hx hy ⊢
theorem ieeeQuietNaNPropagationResult?_sound
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeQuietNaNPropagationResult? x y = some r) :
    ieeeQuietNaNPropagationResult x y r := by
  cases x <;> cases y <;>
    simp [ieeeQuietNaNPropagationResult?, ieeeQuietNaNPropagationResult,
      IeeeValue.isNaN] at h ⊢
  all_goals
    cases h
    simp [IeeeOperationResult.valueNoFlags_value,
      IeeeOperationResult.valueNoFlags_noFlags]
/-- Source-facing predicate for the first primitive IEEE invalid-operation
special-value inputs described in Chapter 2: `0/0`, `0 * infinity`,
`infinity * 0`, `infinity / infinity`, and the usual indeterminate
infinity-plus/minus-infinity cases. -/
def ieeePrimitiveInvalidOperationInput
    (op : BasicOp) (x y : IeeeValue) : Prop :=
  match op with
  | BasicOp.add => IeeeValue.oppositeSignedInfinities x y
  | BasicOp.sub => IeeeValue.sameSignedInfinities x y
  | BasicOp.mul =>
      (x.isZero ∧ y.isInfinite) ∨ (x.isInfinite ∧ y.isZero)
  | BasicOp.div =>
      (x.isZero ∧ y.isZero) ∨ (x.isInfinite ∧ y.isInfinite)
/-- IEEE primitive-operation invalid-operation branch: the input pair is one
of the modeled invalid special-value combinations and the result is a NaN with
the invalid-operation flag. -/
def ieeePrimitiveInvalidOperationResult
    (op : BasicOp) (x y : IeeeValue)
    (r : IeeeOperationResult) : Prop :=
  ieeePrimitiveInvalidOperationInput op x y ∧ ieeeInvalidOperationResult r
theorem ieeePrimitiveInvalidOperationInput_div_zero_zero
    {x y : IeeeValue} (hx : x.isZero) (hy : y.isZero) :
    ieeePrimitiveInvalidOperationInput BasicOp.div x y := by
  change (x.isZero ∧ y.isZero) ∨ (x.isInfinite ∧ y.isInfinite)
  exact Or.inl ⟨hx, hy⟩
theorem ieeePrimitiveInvalidOperationInput_div_inf_inf
    {x y : IeeeValue} (hx : x.isInfinite) (hy : y.isInfinite) :
    ieeePrimitiveInvalidOperationInput BasicOp.div x y := by
  change (x.isZero ∧ y.isZero) ∨ (x.isInfinite ∧ y.isInfinite)
  exact Or.inr ⟨hx, hy⟩
theorem ieeePrimitiveInvalidOperationInput_mul_zero_inf
    {x y : IeeeValue} (hx : x.isZero) (hy : y.isInfinite) :
    ieeePrimitiveInvalidOperationInput BasicOp.mul x y := by
  change (x.isZero ∧ y.isInfinite) ∨ (x.isInfinite ∧ y.isZero)
  exact Or.inl ⟨hx, hy⟩
theorem ieeePrimitiveInvalidOperationInput_mul_inf_zero
    {x y : IeeeValue} (hx : x.isInfinite) (hy : y.isZero) :
    ieeePrimitiveInvalidOperationInput BasicOp.mul x y := by
  change (x.isZero ∧ y.isInfinite) ∨ (x.isInfinite ∧ y.isZero)
  exact Or.inr ⟨hx, hy⟩
theorem ieeePrimitiveInvalidOperationInput_add_posInf_negInf :
    ieeePrimitiveInvalidOperationInput BasicOp.add
      IeeeValue.posInf IeeeValue.negInf := by
  change IeeeValue.oppositeSignedInfinities IeeeValue.posInf IeeeValue.negInf
  exact Or.inl ⟨rfl, rfl⟩
theorem ieeePrimitiveInvalidOperationInput_add_negInf_posInf :
    ieeePrimitiveInvalidOperationInput BasicOp.add
      IeeeValue.negInf IeeeValue.posInf := by
  change IeeeValue.oppositeSignedInfinities IeeeValue.negInf IeeeValue.posInf
  exact Or.inr ⟨rfl, rfl⟩
theorem ieeePrimitiveInvalidOperationInput_sub_posInf_posInf :
    ieeePrimitiveInvalidOperationInput BasicOp.sub
      IeeeValue.posInf IeeeValue.posInf := by
  change IeeeValue.sameSignedInfinities IeeeValue.posInf IeeeValue.posInf
  exact Or.inl ⟨rfl, rfl⟩
theorem ieeePrimitiveInvalidOperationInput_sub_negInf_negInf :
    ieeePrimitiveInvalidOperationInput BasicOp.sub
      IeeeValue.negInf IeeeValue.negInf := by
  change IeeeValue.sameSignedInfinities IeeeValue.negInf IeeeValue.negInf
  exact Or.inr ⟨rfl, rfl⟩
theorem ieeePrimitiveInvalidOperationDefaultResult_ieeePrimitiveInvalidOperationResult
    {op : BasicOp} {x y : IeeeValue}
    (hinput : ieeePrimitiveInvalidOperationInput op x y) :
    ieeePrimitiveInvalidOperationResult op x y
      ieeeInvalidOperationDefaultResult := by
  exact ⟨hinput, ieeeInvalidOperationDefaultResult_ieeeInvalidOperationResult⟩
theorem ieeePrimitiveInvalidOperationResult_input
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInvalidOperationResult op x y r) :
    ieeePrimitiveInvalidOperationInput op x y :=
  h.1
theorem ieeePrimitiveInvalidOperationResult_ieeeInvalidOperationResult
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInvalidOperationResult op x y r) :
    ieeeInvalidOperationResult r :=
  h.2
theorem ieeePrimitiveInvalidOperationResult_value
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInvalidOperationResult op x y r) :
    r.value = IeeeValue.nan :=
  ieeeInvalidOperationResult_value h.2
theorem ieeePrimitiveInvalidOperationResult_hasInvalidOperationFlag
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInvalidOperationResult op x y r) :
    r.hasFlag IeeeExceptionFlag.invalidOperation :=
  ieeeInvalidOperationResult_hasInvalidOperationFlag h.2
/-- Concrete selector for the modeled primitive invalid-operation branch.
It returns the default NaN-with-invalid-operation-flag result exactly for the
source-facing invalid special-value input combinations currently modeled by
`ieeePrimitiveInvalidOperationInput`. -/
noncomputable def ieeePrimitiveInvalidOperationResult?
    (op : BasicOp) (x y : IeeeValue) : Option IeeeOperationResult := by
  classical
  exact
    if ieeePrimitiveInvalidOperationInput op x y then
      some ieeeInvalidOperationDefaultResult
    else
      none
theorem ieeePrimitiveInvalidOperationResult?_of_input
    {op : BasicOp} {x y : IeeeValue}
    (hinput : ieeePrimitiveInvalidOperationInput op x y) :
    ieeePrimitiveInvalidOperationResult? op x y =
      some ieeeInvalidOperationDefaultResult := by
  classical
  simp [ieeePrimitiveInvalidOperationResult?, hinput]
theorem ieeePrimitiveInvalidOperationResult?_none_of_not_input
    {op : BasicOp} {x y : IeeeValue}
    (hinput : ¬ ieeePrimitiveInvalidOperationInput op x y) :
    ieeePrimitiveInvalidOperationResult? op x y = none := by
  classical
  simp [ieeePrimitiveInvalidOperationResult?, hinput]
theorem ieeePrimitiveInvalidOperationResult?_div_zero_zero
    {x y : IeeeValue} (hx : x.isZero) (hy : y.isZero) :
    ieeePrimitiveInvalidOperationResult? BasicOp.div x y =
      some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveInvalidOperationResult?_of_input
    (ieeePrimitiveInvalidOperationInput_div_zero_zero hx hy)
theorem ieeePrimitiveInvalidOperationResult?_div_inf_inf
    {x y : IeeeValue} (hx : x.isInfinite) (hy : y.isInfinite) :
    ieeePrimitiveInvalidOperationResult? BasicOp.div x y =
      some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveInvalidOperationResult?_of_input
    (ieeePrimitiveInvalidOperationInput_div_inf_inf hx hy)
theorem ieeePrimitiveInvalidOperationResult?_mul_zero_inf
    {x y : IeeeValue} (hx : x.isZero) (hy : y.isInfinite) :
    ieeePrimitiveInvalidOperationResult? BasicOp.mul x y =
      some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveInvalidOperationResult?_of_input
    (ieeePrimitiveInvalidOperationInput_mul_zero_inf hx hy)
theorem ieeePrimitiveInvalidOperationResult?_mul_inf_zero
    {x y : IeeeValue} (hx : x.isInfinite) (hy : y.isZero) :
    ieeePrimitiveInvalidOperationResult? BasicOp.mul x y =
      some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveInvalidOperationResult?_of_input
    (ieeePrimitiveInvalidOperationInput_mul_inf_zero hx hy)
theorem ieeePrimitiveInvalidOperationResult?_add_posInf_negInf :
    ieeePrimitiveInvalidOperationResult? BasicOp.add
      IeeeValue.posInf IeeeValue.negInf =
      some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveInvalidOperationResult?_of_input
    ieeePrimitiveInvalidOperationInput_add_posInf_negInf
theorem ieeePrimitiveInvalidOperationResult?_add_negInf_posInf :
    ieeePrimitiveInvalidOperationResult? BasicOp.add
      IeeeValue.negInf IeeeValue.posInf =
      some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveInvalidOperationResult?_of_input
    ieeePrimitiveInvalidOperationInput_add_negInf_posInf
theorem ieeePrimitiveInvalidOperationResult?_sub_posInf_posInf :
    ieeePrimitiveInvalidOperationResult? BasicOp.sub
      IeeeValue.posInf IeeeValue.posInf =
      some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveInvalidOperationResult?_of_input
    ieeePrimitiveInvalidOperationInput_sub_posInf_posInf
theorem ieeePrimitiveInvalidOperationResult?_sub_negInf_negInf :
    ieeePrimitiveInvalidOperationResult? BasicOp.sub
      IeeeValue.negInf IeeeValue.negInf =
      some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveInvalidOperationResult?_of_input
    ieeePrimitiveInvalidOperationInput_sub_negInf_negInf
theorem ieeePrimitiveInvalidOperationResult?_sound
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInvalidOperationResult? op x y = some r) :
    ieeePrimitiveInvalidOperationResult op x y r := by
  classical
  by_cases hinput : ieeePrimitiveInvalidOperationInput op x y
  · simp [ieeePrimitiveInvalidOperationResult?, hinput] at h
    cases h
    exact
      ieeePrimitiveInvalidOperationDefaultResult_ieeePrimitiveInvalidOperationResult
        hinput
  · simp [ieeePrimitiveInvalidOperationResult?, hinput] at h
/-- Sign-selected infinity result for non-invalid IEEE multiplication.
At least one operand must be infinite; zero-times-infinity is handled by the
invalid-operation branch, and NaNs are handled by quiet propagation. -/
def ieeePrimitiveMulInfinityValue
    (x y value : IeeeValue) : Prop :=
  (x.isInfinite ∨ y.isInfinite) ∧
    ((((x.isPositiveNonzero ∧ y.isPositiveNonzero) ∨
          (x.isNegativeNonzero ∧ y.isNegativeNonzero)) ∧
        value = IeeeValue.posInf) ∨
      (((x.isPositiveNonzero ∧ y.isNegativeNonzero) ∨
          (x.isNegativeNonzero ∧ y.isPositiveNonzero)) ∧
        value = IeeeValue.negInf))
/-- No-flag result predicate for non-invalid IEEE multiplication cases whose
mathematical result is an infinity. -/
def ieeePrimitiveMulInfinityPropagationResult
    (x y : IeeeValue) (r : IeeeOperationResult) : Prop :=
  ∃ value : IeeeValue,
    ieeePrimitiveMulInfinityValue x y value ∧
      r = IeeeOperationResult.valueNoFlags value
/-- Sign-selected infinity result for non-invalid IEEE division with infinite
numerator and finite nonzero denominator.  The invalid `infinity / infinity`
and zero-denominator branches are kept separate. -/
def ieeePrimitiveDivInfinityValue
    (x y value : IeeeValue) : Prop :=
  x.isInfinite ∧ y.isFinite ∧
    ((((x.isPositiveNonzero ∧ y.isPositiveNonzero) ∨
          (x.isNegativeNonzero ∧ y.isNegativeNonzero)) ∧
        value = IeeeValue.posInf) ∨
      (((x.isPositiveNonzero ∧ y.isNegativeNonzero) ∨
          (x.isNegativeNonzero ∧ y.isPositiveNonzero)) ∧
        value = IeeeValue.negInf))
/-- No-flag result predicate for non-invalid IEEE division cases whose
mathematical result is an infinity. -/
def ieeePrimitiveDivInfinityPropagationResult
    (x y : IeeeValue) (r : IeeeOperationResult) : Prop :=
  ∃ value : IeeeValue,
    ieeePrimitiveDivInfinityValue x y value ∧
      r = IeeeOperationResult.valueNoFlags value
/-- Sign-selected signed-zero value for non-invalid IEEE division of a finite
or signed-zero numerator by an infinity.  The ordinary modeled `finite 0` is
treated as the local positive-zero default because it carries no sign bit in
`IeeeValue`. -/
def ieeePrimitiveFiniteOverInfinityZeroValue
    (x y value : IeeeValue) : Prop :=
  x.isFinite ∧ y.isInfinite ∧
    ((((x.isNonnegativeSigned ∧ y.isPositiveNonzero) ∨
          (x.isNegativeSigned ∧ y.isNegativeNonzero)) ∧
        value = IeeeValue.posZero) ∨
      (((x.isNonnegativeSigned ∧ y.isNegativeNonzero) ∨
          (x.isNegativeSigned ∧ y.isPositiveNonzero)) ∧
        value = IeeeValue.negZero))
/-- No-flag result predicate for `finite / infinity` IEEE branches.  Only
division has this branch; the other primitive operations return `False`. -/
def ieeePrimitiveFiniteOverInfinityResult
    (op : BasicOp) (x y : IeeeValue)
    (r : IeeeOperationResult) : Prop :=
  match op with
  | BasicOp.div =>
      ∃ value : IeeeValue,
        ieeePrimitiveFiniteOverInfinityZeroValue x y value ∧
          r = IeeeOperationResult.valueNoFlags value
  | _ => False
theorem ieeePrimitiveMulInfinityPropagationResult_posInf_of_positive_positive
    {x y : IeeeValue}
    (hinf : x.isInfinite ∨ y.isInfinite)
    (hx : x.isPositiveNonzero) (hy : y.isPositiveNonzero) :
    ieeePrimitiveMulInfinityPropagationResult x y
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  refine ⟨IeeeValue.posInf, ?_, rfl⟩
  exact ⟨hinf, Or.inl ⟨Or.inl ⟨hx, hy⟩, rfl⟩⟩
theorem ieeePrimitiveMulInfinityPropagationResult_posInf_of_negative_negative
    {x y : IeeeValue}
    (hinf : x.isInfinite ∨ y.isInfinite)
    (hx : x.isNegativeNonzero) (hy : y.isNegativeNonzero) :
    ieeePrimitiveMulInfinityPropagationResult x y
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  refine ⟨IeeeValue.posInf, ?_, rfl⟩
  exact ⟨hinf, Or.inl ⟨Or.inr ⟨hx, hy⟩, rfl⟩⟩
theorem ieeePrimitiveMulInfinityPropagationResult_negInf_of_positive_negative
    {x y : IeeeValue}
    (hinf : x.isInfinite ∨ y.isInfinite)
    (hx : x.isPositiveNonzero) (hy : y.isNegativeNonzero) :
    ieeePrimitiveMulInfinityPropagationResult x y
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  refine ⟨IeeeValue.negInf, ?_, rfl⟩
  exact ⟨hinf, Or.inr ⟨Or.inl ⟨hx, hy⟩, rfl⟩⟩
theorem ieeePrimitiveMulInfinityPropagationResult_negInf_of_negative_positive
    {x y : IeeeValue}
    (hinf : x.isInfinite ∨ y.isInfinite)
    (hx : x.isNegativeNonzero) (hy : y.isPositiveNonzero) :
    ieeePrimitiveMulInfinityPropagationResult x y
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  refine ⟨IeeeValue.negInf, ?_, rfl⟩
  exact ⟨hinf, Or.inr ⟨Or.inr ⟨hx, hy⟩, rfl⟩⟩
theorem ieeePrimitiveMulInfinityPropagationResult_posInf_posInf :
    ieeePrimitiveMulInfinityPropagationResult
      IeeeValue.posInf IeeeValue.posInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveMulInfinityPropagationResult_posInf_of_positive_positive
    (Or.inl IeeeValue.posInf_isInfinite)
    IeeeValue.posInf_isPositiveNonzero
    IeeeValue.posInf_isPositiveNonzero
theorem ieeePrimitiveMulInfinityPropagationResult_posInf_negInf :
    ieeePrimitiveMulInfinityPropagationResult
      IeeeValue.posInf IeeeValue.negInf
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveMulInfinityPropagationResult_negInf_of_positive_negative
    (Or.inl IeeeValue.posInf_isInfinite)
    IeeeValue.posInf_isPositiveNonzero
    IeeeValue.negInf_isNegativeNonzero
theorem ieeePrimitiveMulInfinityPropagationResult_negInf_posInf :
    ieeePrimitiveMulInfinityPropagationResult
      IeeeValue.negInf IeeeValue.posInf
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveMulInfinityPropagationResult_negInf_of_negative_positive
    (Or.inl IeeeValue.negInf_isInfinite)
    IeeeValue.negInf_isNegativeNonzero
    IeeeValue.posInf_isPositiveNonzero
theorem ieeePrimitiveMulInfinityPropagationResult_negInf_negInf :
    ieeePrimitiveMulInfinityPropagationResult
      IeeeValue.negInf IeeeValue.negInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveMulInfinityPropagationResult_posInf_of_negative_negative
    (Or.inl IeeeValue.negInf_isInfinite)
    IeeeValue.negInf_isNegativeNonzero
    IeeeValue.negInf_isNegativeNonzero
theorem ieeePrimitiveMulInfinityPropagationResult_posInf_of_finite_pos_posInf
    {x : ℝ} (hx : 0 < x) :
    ieeePrimitiveMulInfinityPropagationResult
      (IeeeValue.finite x) IeeeValue.posInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveMulInfinityPropagationResult_posInf_of_positive_positive
    (Or.inr IeeeValue.posInf_isInfinite)
    (IeeeValue.finite_pos_isPositiveNonzero hx)
    IeeeValue.posInf_isPositiveNonzero
theorem ieeePrimitiveMulInfinityPropagationResult_negInf_of_finite_neg_posInf
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveMulInfinityPropagationResult
      (IeeeValue.finite x) IeeeValue.posInf
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveMulInfinityPropagationResult_negInf_of_negative_positive
    (Or.inr IeeeValue.posInf_isInfinite)
    (IeeeValue.finite_neg_isNegativeNonzero hx)
    IeeeValue.posInf_isPositiveNonzero
theorem ieeePrimitiveMulInfinityPropagationResult_negInf_of_finite_pos_negInf
    {x : ℝ} (hx : 0 < x) :
    ieeePrimitiveMulInfinityPropagationResult
      (IeeeValue.finite x) IeeeValue.negInf
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveMulInfinityPropagationResult_negInf_of_positive_negative
    (Or.inr IeeeValue.negInf_isInfinite)
    (IeeeValue.finite_pos_isPositiveNonzero hx)
    IeeeValue.negInf_isNegativeNonzero
theorem ieeePrimitiveMulInfinityPropagationResult_posInf_of_finite_neg_negInf
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveMulInfinityPropagationResult
      (IeeeValue.finite x) IeeeValue.negInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveMulInfinityPropagationResult_posInf_of_negative_negative
    (Or.inr IeeeValue.negInf_isInfinite)
    (IeeeValue.finite_neg_isNegativeNonzero hx)
    IeeeValue.negInf_isNegativeNonzero
theorem ieeePrimitiveMulInfinityPropagationResult_posInf_of_posInf_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveMulInfinityPropagationResult
      IeeeValue.posInf (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveMulInfinityPropagationResult_posInf_of_positive_positive
    (Or.inl IeeeValue.posInf_isInfinite)
    IeeeValue.posInf_isPositiveNonzero
    (IeeeValue.finite_pos_isPositiveNonzero hy)
theorem ieeePrimitiveMulInfinityPropagationResult_negInf_of_posInf_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveMulInfinityPropagationResult
      IeeeValue.posInf (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveMulInfinityPropagationResult_negInf_of_positive_negative
    (Or.inl IeeeValue.posInf_isInfinite)
    IeeeValue.posInf_isPositiveNonzero
    (IeeeValue.finite_neg_isNegativeNonzero hy)
theorem ieeePrimitiveMulInfinityPropagationResult_negInf_of_negInf_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveMulInfinityPropagationResult
      IeeeValue.negInf (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveMulInfinityPropagationResult_negInf_of_negative_positive
    (Or.inl IeeeValue.negInf_isInfinite)
    IeeeValue.negInf_isNegativeNonzero
    (IeeeValue.finite_pos_isPositiveNonzero hy)
theorem ieeePrimitiveMulInfinityPropagationResult_posInf_of_negInf_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveMulInfinityPropagationResult
      IeeeValue.negInf (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveMulInfinityPropagationResult_posInf_of_negative_negative
    (Or.inl IeeeValue.negInf_isInfinite)
    IeeeValue.negInf_isNegativeNonzero
    (IeeeValue.finite_neg_isNegativeNonzero hy)
theorem ieeePrimitiveDivInfinityPropagationResult_posInf_of_positive_positive
    {x y : IeeeValue}
    (hxinf : x.isInfinite) (hyfinite : y.isFinite)
    (hx : x.isPositiveNonzero) (hy : y.isPositiveNonzero) :
    ieeePrimitiveDivInfinityPropagationResult x y
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  refine ⟨IeeeValue.posInf, ?_, rfl⟩
  exact ⟨hxinf, hyfinite, Or.inl ⟨Or.inl ⟨hx, hy⟩, rfl⟩⟩
theorem ieeePrimitiveDivInfinityPropagationResult_posInf_of_negative_negative
    {x y : IeeeValue}
    (hxinf : x.isInfinite) (hyfinite : y.isFinite)
    (hx : x.isNegativeNonzero) (hy : y.isNegativeNonzero) :
    ieeePrimitiveDivInfinityPropagationResult x y
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  refine ⟨IeeeValue.posInf, ?_, rfl⟩
  exact ⟨hxinf, hyfinite, Or.inl ⟨Or.inr ⟨hx, hy⟩, rfl⟩⟩
theorem ieeePrimitiveDivInfinityPropagationResult_negInf_of_positive_negative
    {x y : IeeeValue}
    (hxinf : x.isInfinite) (hyfinite : y.isFinite)
    (hx : x.isPositiveNonzero) (hy : y.isNegativeNonzero) :
    ieeePrimitiveDivInfinityPropagationResult x y
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  refine ⟨IeeeValue.negInf, ?_, rfl⟩
  exact ⟨hxinf, hyfinite, Or.inr ⟨Or.inl ⟨hx, hy⟩, rfl⟩⟩
theorem ieeePrimitiveDivInfinityPropagationResult_negInf_of_negative_positive
    {x y : IeeeValue}
    (hxinf : x.isInfinite) (hyfinite : y.isFinite)
    (hx : x.isNegativeNonzero) (hy : y.isPositiveNonzero) :
    ieeePrimitiveDivInfinityPropagationResult x y
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  refine ⟨IeeeValue.negInf, ?_, rfl⟩
  exact ⟨hxinf, hyfinite, Or.inr ⟨Or.inr ⟨hx, hy⟩, rfl⟩⟩
theorem ieeePrimitiveFiniteOverInfinityResult_posZero_of_nonnegative_positive
    {x y : IeeeValue}
    (hxfinite : x.isFinite) (hyinf : y.isInfinite)
    (hx : x.isNonnegativeSigned) (hy : y.isPositiveNonzero) :
    ieeePrimitiveFiniteOverInfinityResult BasicOp.div x y
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  refine ⟨IeeeValue.posZero, ?_, rfl⟩
  exact ⟨hxfinite, hyinf, Or.inl ⟨Or.inl ⟨hx, hy⟩, rfl⟩⟩
theorem ieeePrimitiveFiniteOverInfinityResult_posZero_of_negative_negative
    {x y : IeeeValue}
    (hxfinite : x.isFinite) (hyinf : y.isInfinite)
    (hx : x.isNegativeSigned) (hy : y.isNegativeNonzero) :
    ieeePrimitiveFiniteOverInfinityResult BasicOp.div x y
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  refine ⟨IeeeValue.posZero, ?_, rfl⟩
  exact ⟨hxfinite, hyinf, Or.inl ⟨Or.inr ⟨hx, hy⟩, rfl⟩⟩
theorem ieeePrimitiveFiniteOverInfinityResult_negZero_of_nonnegative_negative
    {x y : IeeeValue}
    (hxfinite : x.isFinite) (hyinf : y.isInfinite)
    (hx : x.isNonnegativeSigned) (hy : y.isNegativeNonzero) :
    ieeePrimitiveFiniteOverInfinityResult BasicOp.div x y
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  refine ⟨IeeeValue.negZero, ?_, rfl⟩
  exact ⟨hxfinite, hyinf, Or.inr ⟨Or.inl ⟨hx, hy⟩, rfl⟩⟩
theorem ieeePrimitiveFiniteOverInfinityResult_negZero_of_negative_positive
    {x y : IeeeValue}
    (hxfinite : x.isFinite) (hyinf : y.isInfinite)
    (hx : x.isNegativeSigned) (hy : y.isPositiveNonzero) :
    ieeePrimitiveFiniteOverInfinityResult BasicOp.div x y
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  refine ⟨IeeeValue.negZero, ?_, rfl⟩
  exact ⟨hxfinite, hyinf, Or.inr ⟨Or.inr ⟨hx, hy⟩, rfl⟩⟩
theorem ieeePrimitiveFiniteOverInfinityResult_posZero_posInf :
    ieeePrimitiveFiniteOverInfinityResult BasicOp.div
      IeeeValue.posZero IeeeValue.posInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveFiniteOverInfinityResult_posZero_of_nonnegative_positive
    IeeeValue.posZero_isFinite
    IeeeValue.posInf_isInfinite
    IeeeValue.posZero_isNonnegativeSigned
    IeeeValue.posInf_isPositiveNonzero
theorem ieeePrimitiveFiniteOverInfinityResult_posZero_negInf :
    ieeePrimitiveFiniteOverInfinityResult BasicOp.div
      IeeeValue.posZero IeeeValue.negInf
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveFiniteOverInfinityResult_negZero_of_nonnegative_negative
    IeeeValue.posZero_isFinite
    IeeeValue.negInf_isInfinite
    IeeeValue.posZero_isNonnegativeSigned
    IeeeValue.negInf_isNegativeNonzero
theorem ieeePrimitiveFiniteOverInfinityResult_negZero_posInf :
    ieeePrimitiveFiniteOverInfinityResult BasicOp.div
      IeeeValue.negZero IeeeValue.posInf
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveFiniteOverInfinityResult_negZero_of_negative_positive
    IeeeValue.negZero_isFinite
    IeeeValue.posInf_isInfinite
    IeeeValue.negZero_isNegativeSigned
    IeeeValue.posInf_isPositiveNonzero
theorem ieeePrimitiveFiniteOverInfinityResult_negZero_negInf :
    ieeePrimitiveFiniteOverInfinityResult BasicOp.div
      IeeeValue.negZero IeeeValue.negInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveFiniteOverInfinityResult_posZero_of_negative_negative
    IeeeValue.negZero_isFinite
    IeeeValue.negInf_isInfinite
    IeeeValue.negZero_isNegativeSigned
    IeeeValue.negInf_isNegativeNonzero
theorem ieeePrimitiveFiniteOverInfinityResult_finite_zero_posInf :
    ieeePrimitiveFiniteOverInfinityResult BasicOp.div
      (IeeeValue.finite 0) IeeeValue.posInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveFiniteOverInfinityResult_posZero_of_nonnegative_positive
    (IeeeValue.finite_isFinite 0)
    IeeeValue.posInf_isInfinite
    IeeeValue.finite_zero_isNonnegativeSigned
    IeeeValue.posInf_isPositiveNonzero
theorem ieeePrimitiveFiniteOverInfinityResult_finite_zero_negInf :
    ieeePrimitiveFiniteOverInfinityResult BasicOp.div
      (IeeeValue.finite 0) IeeeValue.negInf
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveFiniteOverInfinityResult_negZero_of_nonnegative_negative
    (IeeeValue.finite_isFinite 0)
    IeeeValue.negInf_isInfinite
    IeeeValue.finite_zero_isNonnegativeSigned
    IeeeValue.negInf_isNegativeNonzero
theorem ieeePrimitiveFiniteOverInfinityResult_posZero_of_finite_nonneg_posInf
    {x : ℝ} (hx : 0 ≤ x) :
    ieeePrimitiveFiniteOverInfinityResult BasicOp.div
      (IeeeValue.finite x) IeeeValue.posInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveFiniteOverInfinityResult_posZero_of_nonnegative_positive
    (IeeeValue.finite_isFinite x)
    IeeeValue.posInf_isInfinite
    (IeeeValue.finite_nonneg_isNonnegativeSigned hx)
    IeeeValue.posInf_isPositiveNonzero
theorem ieeePrimitiveFiniteOverInfinityResult_negZero_of_finite_nonneg_negInf
    {x : ℝ} (hx : 0 ≤ x) :
    ieeePrimitiveFiniteOverInfinityResult BasicOp.div
      (IeeeValue.finite x) IeeeValue.negInf
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveFiniteOverInfinityResult_negZero_of_nonnegative_negative
    (IeeeValue.finite_isFinite x)
    IeeeValue.negInf_isInfinite
    (IeeeValue.finite_nonneg_isNonnegativeSigned hx)
    IeeeValue.negInf_isNegativeNonzero
theorem ieeePrimitiveFiniteOverInfinityResult_negZero_of_finite_neg_posInf
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveFiniteOverInfinityResult BasicOp.div
      (IeeeValue.finite x) IeeeValue.posInf
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveFiniteOverInfinityResult_negZero_of_negative_positive
    (IeeeValue.finite_isFinite x)
    IeeeValue.posInf_isInfinite
    (IeeeValue.finite_neg_isNegativeSigned hx)
    IeeeValue.posInf_isPositiveNonzero
theorem ieeePrimitiveFiniteOverInfinityResult_posZero_of_finite_neg_negInf
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveFiniteOverInfinityResult BasicOp.div
      (IeeeValue.finite x) IeeeValue.negInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveFiniteOverInfinityResult_posZero_of_negative_negative
    (IeeeValue.finite_isFinite x)
    IeeeValue.negInf_isInfinite
    (IeeeValue.finite_neg_isNegativeSigned hx)
    IeeeValue.negInf_isNegativeNonzero
theorem ieeePrimitiveMulInfinityPropagationResult_noFlags
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveMulInfinityPropagationResult x y r) :
    r.noFlags := by
  rcases h with ⟨value, _, hr⟩
  rw [hr]
  exact IeeeOperationResult.valueNoFlags_noFlags value
theorem ieeePrimitiveDivInfinityPropagationResult_noFlags
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveDivInfinityPropagationResult x y r) :
    r.noFlags := by
  rcases h with ⟨value, _, hr⟩
  rw [hr]
  exact IeeeOperationResult.valueNoFlags_noFlags value
theorem ieeePrimitiveFiniteOverInfinityResult_noFlags
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveFiniteOverInfinityResult op x y r) :
    r.noFlags := by
  cases op <;> simp [ieeePrimitiveFiniteOverInfinityResult] at h
  rcases h with ⟨value, _, hr⟩
  rw [hr]
  exact IeeeOperationResult.valueNoFlags_noFlags value
theorem ieeePrimitiveFiniteOverInfinityResult_left_nan
    {op : BasicOp} {y : IeeeValue} {r : IeeeOperationResult} :
    ¬ ieeePrimitiveFiniteOverInfinityResult op IeeeValue.nan y r := by
  cases op <;>
    simp [ieeePrimitiveFiniteOverInfinityResult,
      ieeePrimitiveFiniteOverInfinityZeroValue,
      IeeeValue.isFinite, IeeeValue.isInfinite,
      IeeeValue.isNonnegativeSigned, IeeeValue.isNegativeSigned,
      IeeeValue.isPositiveNonzero, IeeeValue.isNegativeNonzero]
theorem ieeePrimitiveFiniteOverInfinityResult_right_nan
    {op : BasicOp} {x : IeeeValue} {r : IeeeOperationResult} :
    ¬ ieeePrimitiveFiniteOverInfinityResult op x IeeeValue.nan r := by
  cases op <;>
    simp [ieeePrimitiveFiniteOverInfinityResult,
      ieeePrimitiveFiniteOverInfinityZeroValue,
      IeeeValue.isFinite, IeeeValue.isInfinite,
      IeeeValue.isNonnegativeSigned, IeeeValue.isNegativeSigned,
      IeeeValue.isPositiveNonzero, IeeeValue.isNegativeNonzero]
/-- Concrete default selector for the currently modeled `finite / infinity`
branch.  Only primitive division is covered here; `infinity / infinity`
remains in the invalid-operation branch, and ordinary finite division remains
the finite real-valued branch. -/
noncomputable def ieeePrimitiveFiniteOverInfinityResult?
    (op : BasicOp) (x y : IeeeValue) : Option IeeeOperationResult := by
  classical
  exact
    match op, x, y with
    | BasicOp.div, IeeeValue.posZero, IeeeValue.posInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero)
    | BasicOp.div, IeeeValue.posZero, IeeeValue.negInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero)
    | BasicOp.div, IeeeValue.negZero, IeeeValue.posInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero)
    | BasicOp.div, IeeeValue.negZero, IeeeValue.negInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero)
    | BasicOp.div, IeeeValue.finite x, IeeeValue.posInf =>
        if 0 ≤ x then
          some (IeeeOperationResult.valueNoFlags IeeeValue.posZero)
        else
          some (IeeeOperationResult.valueNoFlags IeeeValue.negZero)
    | BasicOp.div, IeeeValue.finite x, IeeeValue.negInf =>
        if 0 ≤ x then
          some (IeeeOperationResult.valueNoFlags IeeeValue.negZero)
        else
          some (IeeeOperationResult.valueNoFlags IeeeValue.posZero)
    | _, _, _ => none
theorem ieeePrimitiveFiniteOverInfinityResult?_posZero_posInf :
    ieeePrimitiveFiniteOverInfinityResult?
      BasicOp.div IeeeValue.posZero IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simp [ieeePrimitiveFiniteOverInfinityResult?]
theorem ieeePrimitiveFiniteOverInfinityResult?_negZero_of_posZero_negInf :
    ieeePrimitiveFiniteOverInfinityResult?
      BasicOp.div IeeeValue.posZero IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simp [ieeePrimitiveFiniteOverInfinityResult?]
theorem ieeePrimitiveFiniteOverInfinityResult?_negZero_posInf :
    ieeePrimitiveFiniteOverInfinityResult?
      BasicOp.div IeeeValue.negZero IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simp [ieeePrimitiveFiniteOverInfinityResult?]
theorem ieeePrimitiveFiniteOverInfinityResult?_posZero_of_negZero_negInf :
    ieeePrimitiveFiniteOverInfinityResult?
      BasicOp.div IeeeValue.negZero IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simp [ieeePrimitiveFiniteOverInfinityResult?]
theorem ieeePrimitiveFiniteOverInfinityResult?_finite_nonneg_posInf
    {x : ℝ} (hx : 0 ≤ x) :
    ieeePrimitiveFiniteOverInfinityResult?
      BasicOp.div (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simp [ieeePrimitiveFiniteOverInfinityResult?, hx]
theorem ieeePrimitiveFiniteOverInfinityResult?_negZero_of_finite_neg_posInf
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveFiniteOverInfinityResult?
      BasicOp.div (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simp [ieeePrimitiveFiniteOverInfinityResult?, not_le.mpr hx]
theorem ieeePrimitiveFiniteOverInfinityResult?_finite_nonneg_negInf
    {x : ℝ} (hx : 0 ≤ x) :
    ieeePrimitiveFiniteOverInfinityResult?
      BasicOp.div (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simp [ieeePrimitiveFiniteOverInfinityResult?, hx]
theorem ieeePrimitiveFiniteOverInfinityResult?_posZero_of_finite_neg_negInf
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveFiniteOverInfinityResult?
      BasicOp.div (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simp [ieeePrimitiveFiniteOverInfinityResult?, not_le.mpr hx]
theorem ieeePrimitiveFiniteOverInfinityResult?_finite_zero_posInf :
    ieeePrimitiveFiniteOverInfinityResult?
      BasicOp.div (IeeeValue.finite 0) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simpa using
    (ieeePrimitiveFiniteOverInfinityResult?_finite_nonneg_posInf
      (x := 0) (by norm_num))
theorem ieeePrimitiveFiniteOverInfinityResult?_finite_zero_negInf :
    ieeePrimitiveFiniteOverInfinityResult?
      BasicOp.div (IeeeValue.finite 0) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simpa using
    (ieeePrimitiveFiniteOverInfinityResult?_finite_nonneg_negInf
      (x := 0) (by norm_num))
theorem ieeePrimitiveFiniteOverInfinityResult?_sound
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveFiniteOverInfinityResult? op x y = some r) :
    ieeePrimitiveFiniteOverInfinityResult op x y r := by
  classical
  cases op <;> cases x <;> cases y <;>
    simp [ieeePrimitiveFiniteOverInfinityResult?,
      ieeePrimitiveFiniteOverInfinityResult,
      ieeePrimitiveFiniteOverInfinityZeroValue,
      IeeeValue.isFinite, IeeeValue.isInfinite,
      IeeeValue.isNonnegativeSigned, IeeeValue.isNegativeSigned,
      IeeeValue.isPositiveNonzero, IeeeValue.isNegativeNonzero] at h ⊢
  · rename_i x
    by_cases hx : 0 ≤ x
    · simp [hx] at h
      subst r
      exact ⟨IeeeValue.posZero, Or.inl ⟨hx, rfl⟩, rfl⟩
    · simp [hx] at h
      subst r
      exact ⟨IeeeValue.negZero, Or.inr ⟨not_le.mp hx, rfl⟩, rfl⟩
  · rename_i x
    by_cases hx : 0 ≤ x
    · simp [hx] at h
      subst r
      exact ⟨IeeeValue.negZero, Or.inr ⟨hx, rfl⟩, rfl⟩
    · simp [hx] at h
      subst r
      exact ⟨IeeeValue.posZero, Or.inl ⟨not_le.mp hx, rfl⟩, rfl⟩
  · exact h.symm
  · exact h.symm
  · exact h.symm
  · exact h.symm
/-- Sign-selected signed-zero value for non-invalid IEEE multiplication.
Only signed-zero operands trigger this special branch; ordinary finite payloads
continue to use the real-valued finite wrapper.  Zero-times-infinity remains an
invalid-operation branch, and NaNs remain quiet-propagation branches. -/
def ieeePrimitiveMulSignedZeroValue
    (x y value : IeeeValue) : Prop :=
  x.isFinite ∧ y.isFinite ∧ (x.isSignedZero ∨ y.isSignedZero) ∧
    ((((x.isNonnegativeSigned ∧ y.isNonnegativeSigned) ∨
          (x.isNegativeSigned ∧ y.isNegativeSigned)) ∧
        value = IeeeValue.posZero) ∨
      (((x.isNonnegativeSigned ∧ y.isNegativeSigned) ∨
          (x.isNegativeSigned ∧ y.isNonnegativeSigned)) ∧
        value = IeeeValue.negZero))
/-- No-flag result predicate for non-invalid IEEE multiplication cases whose
mathematical result is a signed zero. -/
def ieeePrimitiveMulSignedZeroResult
    (x y : IeeeValue) (r : IeeeOperationResult) : Prop :=
  ∃ value : IeeeValue,
    ieeePrimitiveMulSignedZeroValue x y value ∧
      r = IeeeOperationResult.valueNoFlags value
theorem ieeePrimitiveMulSignedZeroResult_posZero_of_nonnegative
    {x y : IeeeValue}
    (hxfinite : x.isFinite) (hyfinite : y.isFinite)
    (hsigned : x.isSignedZero ∨ y.isSignedZero)
    (hx : x.isNonnegativeSigned) (hy : y.isNonnegativeSigned) :
    ieeePrimitiveMulSignedZeroResult x y
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  refine ⟨IeeeValue.posZero, ?_, rfl⟩
  exact ⟨hxfinite, hyfinite, hsigned,
    Or.inl ⟨Or.inl ⟨hx, hy⟩, rfl⟩⟩
theorem ieeePrimitiveMulSignedZeroResult_posZero_of_negative_negative
    {x y : IeeeValue}
    (hxfinite : x.isFinite) (hyfinite : y.isFinite)
    (hsigned : x.isSignedZero ∨ y.isSignedZero)
    (hx : x.isNegativeSigned) (hy : y.isNegativeSigned) :
    ieeePrimitiveMulSignedZeroResult x y
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  refine ⟨IeeeValue.posZero, ?_, rfl⟩
  exact ⟨hxfinite, hyfinite, hsigned,
    Or.inl ⟨Or.inr ⟨hx, hy⟩, rfl⟩⟩
theorem ieeePrimitiveMulSignedZeroResult_negZero_of_nonnegative_negative
    {x y : IeeeValue}
    (hxfinite : x.isFinite) (hyfinite : y.isFinite)
    (hsigned : x.isSignedZero ∨ y.isSignedZero)
    (hx : x.isNonnegativeSigned) (hy : y.isNegativeSigned) :
    ieeePrimitiveMulSignedZeroResult x y
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  refine ⟨IeeeValue.negZero, ?_, rfl⟩
  exact ⟨hxfinite, hyfinite, hsigned,
    Or.inr ⟨Or.inl ⟨hx, hy⟩, rfl⟩⟩
theorem ieeePrimitiveMulSignedZeroResult_negZero_of_negative_nonnegative
    {x y : IeeeValue}
    (hxfinite : x.isFinite) (hyfinite : y.isFinite)
    (hsigned : x.isSignedZero ∨ y.isSignedZero)
    (hx : x.isNegativeSigned) (hy : y.isNonnegativeSigned) :
    ieeePrimitiveMulSignedZeroResult x y
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  refine ⟨IeeeValue.negZero, ?_, rfl⟩
  exact ⟨hxfinite, hyfinite, hsigned,
    Or.inr ⟨Or.inr ⟨hx, hy⟩, rfl⟩⟩
theorem ieeePrimitiveMulSignedZeroResult_posZero_posZero :
    ieeePrimitiveMulSignedZeroResult
      IeeeValue.posZero IeeeValue.posZero
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveMulSignedZeroResult_posZero_of_nonnegative
    IeeeValue.posZero_isFinite
    IeeeValue.posZero_isFinite
    (Or.inl IeeeValue.posZero_isSignedZero)
    IeeeValue.posZero_isNonnegativeSigned
    IeeeValue.posZero_isNonnegativeSigned
theorem ieeePrimitiveMulSignedZeroResult_posZero_negZero :
    ieeePrimitiveMulSignedZeroResult
      IeeeValue.posZero IeeeValue.negZero
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveMulSignedZeroResult_negZero_of_nonnegative_negative
    IeeeValue.posZero_isFinite
    IeeeValue.negZero_isFinite
    (Or.inl IeeeValue.posZero_isSignedZero)
    IeeeValue.posZero_isNonnegativeSigned
    IeeeValue.negZero_isNegativeSigned
theorem ieeePrimitiveMulSignedZeroResult_negZero_posZero :
    ieeePrimitiveMulSignedZeroResult
      IeeeValue.negZero IeeeValue.posZero
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveMulSignedZeroResult_negZero_of_negative_nonnegative
    IeeeValue.negZero_isFinite
    IeeeValue.posZero_isFinite
    (Or.inl IeeeValue.negZero_isSignedZero)
    IeeeValue.negZero_isNegativeSigned
    IeeeValue.posZero_isNonnegativeSigned
theorem ieeePrimitiveMulSignedZeroResult_negZero_negZero :
    ieeePrimitiveMulSignedZeroResult
      IeeeValue.negZero IeeeValue.negZero
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveMulSignedZeroResult_posZero_of_negative_negative
    IeeeValue.negZero_isFinite
    IeeeValue.negZero_isFinite
    (Or.inl IeeeValue.negZero_isSignedZero)
    IeeeValue.negZero_isNegativeSigned
    IeeeValue.negZero_isNegativeSigned
theorem ieeePrimitiveMulSignedZeroResult_posZero_of_posZero_finite_nonneg
    {y : ℝ} (hy : 0 ≤ y) :
    ieeePrimitiveMulSignedZeroResult
      IeeeValue.posZero (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveMulSignedZeroResult_posZero_of_nonnegative
    IeeeValue.posZero_isFinite
    (IeeeValue.finite_isFinite y)
    (Or.inl IeeeValue.posZero_isSignedZero)
    IeeeValue.posZero_isNonnegativeSigned
    (IeeeValue.finite_nonneg_isNonnegativeSigned hy)
theorem ieeePrimitiveMulSignedZeroResult_negZero_of_posZero_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveMulSignedZeroResult
      IeeeValue.posZero (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveMulSignedZeroResult_negZero_of_nonnegative_negative
    IeeeValue.posZero_isFinite
    (IeeeValue.finite_isFinite y)
    (Or.inl IeeeValue.posZero_isSignedZero)
    IeeeValue.posZero_isNonnegativeSigned
    (IeeeValue.finite_neg_isNegativeSigned hy)
theorem ieeePrimitiveMulSignedZeroResult_posZero_of_finite_nonneg_posZero
    {x : ℝ} (hx : 0 ≤ x) :
    ieeePrimitiveMulSignedZeroResult
      (IeeeValue.finite x) IeeeValue.posZero
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveMulSignedZeroResult_posZero_of_nonnegative
    (IeeeValue.finite_isFinite x)
    IeeeValue.posZero_isFinite
    (Or.inr IeeeValue.posZero_isSignedZero)
    (IeeeValue.finite_nonneg_isNonnegativeSigned hx)
    IeeeValue.posZero_isNonnegativeSigned
theorem ieeePrimitiveMulSignedZeroResult_negZero_of_finite_neg_posZero
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveMulSignedZeroResult
      (IeeeValue.finite x) IeeeValue.posZero
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveMulSignedZeroResult_negZero_of_negative_nonnegative
    (IeeeValue.finite_isFinite x)
    IeeeValue.posZero_isFinite
    (Or.inr IeeeValue.posZero_isSignedZero)
    (IeeeValue.finite_neg_isNegativeSigned hx)
    IeeeValue.posZero_isNonnegativeSigned
theorem ieeePrimitiveMulSignedZeroResult_negZero_of_negZero_finite_nonneg
    {y : ℝ} (hy : 0 ≤ y) :
    ieeePrimitiveMulSignedZeroResult
      IeeeValue.negZero (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveMulSignedZeroResult_negZero_of_negative_nonnegative
    IeeeValue.negZero_isFinite
    (IeeeValue.finite_isFinite y)
    (Or.inl IeeeValue.negZero_isSignedZero)
    IeeeValue.negZero_isNegativeSigned
    (IeeeValue.finite_nonneg_isNonnegativeSigned hy)
theorem ieeePrimitiveMulSignedZeroResult_posZero_of_negZero_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveMulSignedZeroResult
      IeeeValue.negZero (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveMulSignedZeroResult_posZero_of_negative_negative
    IeeeValue.negZero_isFinite
    (IeeeValue.finite_isFinite y)
    (Or.inl IeeeValue.negZero_isSignedZero)
    IeeeValue.negZero_isNegativeSigned
    (IeeeValue.finite_neg_isNegativeSigned hy)
theorem ieeePrimitiveMulSignedZeroResult_negZero_of_finite_nonneg_negZero
    {x : ℝ} (hx : 0 ≤ x) :
    ieeePrimitiveMulSignedZeroResult
      (IeeeValue.finite x) IeeeValue.negZero
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveMulSignedZeroResult_negZero_of_nonnegative_negative
    (IeeeValue.finite_isFinite x)
    IeeeValue.negZero_isFinite
    (Or.inr IeeeValue.negZero_isSignedZero)
    (IeeeValue.finite_nonneg_isNonnegativeSigned hx)
    IeeeValue.negZero_isNegativeSigned
theorem ieeePrimitiveMulSignedZeroResult_posZero_of_finite_neg_negZero
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveMulSignedZeroResult
      (IeeeValue.finite x) IeeeValue.negZero
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveMulSignedZeroResult_posZero_of_negative_negative
    (IeeeValue.finite_isFinite x)
    IeeeValue.negZero_isFinite
    (Or.inr IeeeValue.negZero_isSignedZero)
    (IeeeValue.finite_neg_isNegativeSigned hx)
    IeeeValue.negZero_isNegativeSigned
/-- Concrete default selector for the modeled signed-zero multiplication
branch.  This is intentionally only the no-flag branch in which at least one
operand is an actual signed zero and both operands are finite in the IEEE-value
sense; invalid cases such as zero times infinity are handled by the separate
invalid-operation branch. -/
noncomputable def ieeePrimitiveMulSignedZeroResult?
    (x y : IeeeValue) : Option IeeeOperationResult := by
  classical
  exact
    match x, y with
    | IeeeValue.posZero, IeeeValue.posZero =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero)
    | IeeeValue.posZero, IeeeValue.negZero =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero)
    | IeeeValue.negZero, IeeeValue.posZero =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero)
    | IeeeValue.negZero, IeeeValue.negZero =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero)
    | IeeeValue.posZero, IeeeValue.finite y =>
        if 0 ≤ y then
          some (IeeeOperationResult.valueNoFlags IeeeValue.posZero)
        else
          some (IeeeOperationResult.valueNoFlags IeeeValue.negZero)
    | IeeeValue.finite x, IeeeValue.posZero =>
        if 0 ≤ x then
          some (IeeeOperationResult.valueNoFlags IeeeValue.posZero)
        else
          some (IeeeOperationResult.valueNoFlags IeeeValue.negZero)
    | IeeeValue.negZero, IeeeValue.finite y =>
        if 0 ≤ y then
          some (IeeeOperationResult.valueNoFlags IeeeValue.negZero)
        else
          some (IeeeOperationResult.valueNoFlags IeeeValue.posZero)
    | IeeeValue.finite x, IeeeValue.negZero =>
        if 0 ≤ x then
          some (IeeeOperationResult.valueNoFlags IeeeValue.negZero)
        else
          some (IeeeOperationResult.valueNoFlags IeeeValue.posZero)
    | _, _ => none
theorem ieeePrimitiveMulSignedZeroResult?_posZero_posZero :
    ieeePrimitiveMulSignedZeroResult?
      IeeeValue.posZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simp [ieeePrimitiveMulSignedZeroResult?]
theorem ieeePrimitiveMulSignedZeroResult?_posZero_negZero :
    ieeePrimitiveMulSignedZeroResult?
      IeeeValue.posZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simp [ieeePrimitiveMulSignedZeroResult?]
theorem ieeePrimitiveMulSignedZeroResult?_negZero_posZero :
    ieeePrimitiveMulSignedZeroResult?
      IeeeValue.negZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simp [ieeePrimitiveMulSignedZeroResult?]
theorem ieeePrimitiveMulSignedZeroResult?_negZero_negZero :
    ieeePrimitiveMulSignedZeroResult?
      IeeeValue.negZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simp [ieeePrimitiveMulSignedZeroResult?]
theorem ieeePrimitiveMulSignedZeroResult?_posZero_finite_nonneg
    {y : ℝ} (hy : 0 ≤ y) :
    ieeePrimitiveMulSignedZeroResult?
      IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simp [ieeePrimitiveMulSignedZeroResult?, hy]
theorem ieeePrimitiveMulSignedZeroResult?_negZero_of_posZero_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveMulSignedZeroResult?
      IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simp [ieeePrimitiveMulSignedZeroResult?, not_le.mpr hy]
theorem ieeePrimitiveMulSignedZeroResult?_finite_nonneg_posZero
    {x : ℝ} (hx : 0 ≤ x) :
    ieeePrimitiveMulSignedZeroResult?
      (IeeeValue.finite x) IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simp [ieeePrimitiveMulSignedZeroResult?, hx]
theorem ieeePrimitiveMulSignedZeroResult?_negZero_of_finite_neg_posZero
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveMulSignedZeroResult?
      (IeeeValue.finite x) IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simp [ieeePrimitiveMulSignedZeroResult?, not_le.mpr hx]
theorem ieeePrimitiveMulSignedZeroResult?_negZero_finite_nonneg
    {y : ℝ} (hy : 0 ≤ y) :
    ieeePrimitiveMulSignedZeroResult?
      IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simp [ieeePrimitiveMulSignedZeroResult?, hy]
theorem ieeePrimitiveMulSignedZeroResult?_posZero_of_negZero_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveMulSignedZeroResult?
      IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simp [ieeePrimitiveMulSignedZeroResult?, not_le.mpr hy]
theorem ieeePrimitiveMulSignedZeroResult?_finite_nonneg_negZero
    {x : ℝ} (hx : 0 ≤ x) :
    ieeePrimitiveMulSignedZeroResult?
      (IeeeValue.finite x) IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simp [ieeePrimitiveMulSignedZeroResult?, hx]
theorem ieeePrimitiveMulSignedZeroResult?_posZero_of_finite_neg_negZero
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveMulSignedZeroResult?
      (IeeeValue.finite x) IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simp [ieeePrimitiveMulSignedZeroResult?, not_le.mpr hx]
theorem ieeePrimitiveMulSignedZeroResult?_sound
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveMulSignedZeroResult? x y = some r) :
    ieeePrimitiveMulSignedZeroResult x y r := by
  classical
  cases x <;> cases y <;> simp [ieeePrimitiveMulSignedZeroResult?,
      ieeePrimitiveMulSignedZeroResult, ieeePrimitiveMulSignedZeroValue,
      IeeeValue.isFinite, IeeeValue.isSignedZero,
      IeeeValue.isNonnegativeSigned, IeeeValue.isNegativeSigned] at h ⊢
  · rename_i x
    by_cases hx : 0 ≤ x
    · simp [hx] at h
      subst r
      exact ⟨IeeeValue.posZero, Or.inl ⟨hx, rfl⟩, rfl⟩
    · simp [hx] at h
      subst r
      exact ⟨IeeeValue.negZero, Or.inr ⟨not_le.mp hx, rfl⟩, rfl⟩
  · rename_i x
    by_cases hx : 0 ≤ x
    · simp [hx] at h
      subst r
      exact ⟨IeeeValue.negZero, Or.inr ⟨hx, rfl⟩, rfl⟩
    · simp [hx] at h
      subst r
      exact ⟨IeeeValue.posZero, Or.inl ⟨not_le.mp hx, rfl⟩, rfl⟩
  · rename_i y
    by_cases hy : 0 ≤ y
    · simp [hy] at h
      subst r
      exact ⟨IeeeValue.posZero, Or.inl ⟨hy, rfl⟩, rfl⟩
    · simp [hy] at h
      subst r
      exact ⟨IeeeValue.negZero, Or.inr ⟨not_le.mp hy, rfl⟩, rfl⟩
  · exact h.symm
  · exact h.symm
  · rename_i y
    by_cases hy : 0 ≤ y
    · simp [hy] at h
      subst r
      exact ⟨IeeeValue.negZero, Or.inr ⟨hy, rfl⟩, rfl⟩
    · simp [hy] at h
      subst r
      exact ⟨IeeeValue.posZero, Or.inl ⟨not_le.mp hy, rfl⟩, rfl⟩
  · exact h.symm
  · exact h.symm
theorem ieeePrimitiveMulSignedZeroResult_noFlags
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveMulSignedZeroResult x y r) :
    r.noFlags := by
  rcases h with ⟨value, _, hr⟩
  rw [hr]
  exact IeeeOperationResult.valueNoFlags_noFlags value
theorem ieeePrimitiveMulSignedZeroResult_left_nan
    {y : IeeeValue} {r : IeeeOperationResult} :
    ¬ ieeePrimitiveMulSignedZeroResult IeeeValue.nan y r := by
  intro h
  rcases h with ⟨value, hvalue, _⟩
  simp [ieeePrimitiveMulSignedZeroValue, IeeeValue.isFinite] at hvalue
theorem ieeePrimitiveMulSignedZeroResult_right_nan
    {x : IeeeValue} {r : IeeeOperationResult} :
    ¬ ieeePrimitiveMulSignedZeroResult x IeeeValue.nan r := by
  intro h
  rcases h with ⟨value, hvalue, _⟩
  simp [ieeePrimitiveMulSignedZeroValue, IeeeValue.isFinite] at hvalue
/-- Sign-selected signed-zero value for non-invalid IEEE division of signed
zero by a finite nonzero denominator.  The denominator sign is carried by the
positive/negative nonzero predicates, while `y.isFinite` excludes infinities so
this branch stays separate from finite-over-infinity division. -/
def ieeePrimitiveSignedZeroOverFiniteValue
    (x y value : IeeeValue) : Prop :=
  x.isSignedZero ∧ y.isFinite ∧
    ((y.isPositiveNonzero ∨ y.isNegativeNonzero) ∧
      ((((x.isNonnegativeSigned ∧ y.isPositiveNonzero) ∨
            (x.isNegativeSigned ∧ y.isNegativeNonzero)) ∧
          value = IeeeValue.posZero) ∨
        (((x.isNonnegativeSigned ∧ y.isNegativeNonzero) ∨
            (x.isNegativeSigned ∧ y.isPositiveNonzero)) ∧
          value = IeeeValue.negZero)))
/-- No-flag result predicate for IEEE division of signed zero by a finite
nonzero denominator. -/
def ieeePrimitiveSignedZeroOverFiniteResult
    (x y : IeeeValue) (r : IeeeOperationResult) : Prop :=
  ∃ value : IeeeValue,
    ieeePrimitiveSignedZeroOverFiniteValue x y value ∧
      r = IeeeOperationResult.valueNoFlags value
theorem ieeePrimitiveSignedZeroOverFiniteResult_posZero_of_nonnegative_positive
    {x y : IeeeValue}
    (hxsigned : x.isSignedZero) (hyfinite : y.isFinite)
    (hx : x.isNonnegativeSigned) (hy : y.isPositiveNonzero) :
    ieeePrimitiveSignedZeroOverFiniteResult x y
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  refine ⟨IeeeValue.posZero, ?_, rfl⟩
  exact ⟨hxsigned, hyfinite,
    ⟨Or.inl hy, Or.inl ⟨Or.inl ⟨hx, hy⟩, rfl⟩⟩⟩
theorem ieeePrimitiveSignedZeroOverFiniteResult_posZero_of_negative_negative
    {x y : IeeeValue}
    (hxsigned : x.isSignedZero) (hyfinite : y.isFinite)
    (hx : x.isNegativeSigned) (hy : y.isNegativeNonzero) :
    ieeePrimitiveSignedZeroOverFiniteResult x y
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  refine ⟨IeeeValue.posZero, ?_, rfl⟩
  exact ⟨hxsigned, hyfinite,
    ⟨Or.inr hy, Or.inl ⟨Or.inr ⟨hx, hy⟩, rfl⟩⟩⟩
theorem ieeePrimitiveSignedZeroOverFiniteResult_negZero_of_nonnegative_negative
    {x y : IeeeValue}
    (hxsigned : x.isSignedZero) (hyfinite : y.isFinite)
    (hx : x.isNonnegativeSigned) (hy : y.isNegativeNonzero) :
    ieeePrimitiveSignedZeroOverFiniteResult x y
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  refine ⟨IeeeValue.negZero, ?_, rfl⟩
  exact ⟨hxsigned, hyfinite,
    ⟨Or.inr hy, Or.inr ⟨Or.inl ⟨hx, hy⟩, rfl⟩⟩⟩
theorem ieeePrimitiveSignedZeroOverFiniteResult_negZero_of_negative_positive
    {x y : IeeeValue}
    (hxsigned : x.isSignedZero) (hyfinite : y.isFinite)
    (hx : x.isNegativeSigned) (hy : y.isPositiveNonzero) :
    ieeePrimitiveSignedZeroOverFiniteResult x y
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  refine ⟨IeeeValue.negZero, ?_, rfl⟩
  exact ⟨hxsigned, hyfinite,
    ⟨Or.inl hy, Or.inr ⟨Or.inr ⟨hx, hy⟩, rfl⟩⟩⟩
theorem ieeePrimitiveSignedZeroOverFiniteResult_posZero_of_posZero_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveSignedZeroOverFiniteResult
      IeeeValue.posZero (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveSignedZeroOverFiniteResult_posZero_of_nonnegative_positive
    IeeeValue.posZero_isSignedZero
    (IeeeValue.finite_isFinite y)
    IeeeValue.posZero_isNonnegativeSigned
    (IeeeValue.finite_pos_isPositiveNonzero hy)
theorem ieeePrimitiveSignedZeroOverFiniteResult_negZero_of_posZero_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveSignedZeroOverFiniteResult
      IeeeValue.posZero (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveSignedZeroOverFiniteResult_negZero_of_nonnegative_negative
    IeeeValue.posZero_isSignedZero
    (IeeeValue.finite_isFinite y)
    IeeeValue.posZero_isNonnegativeSigned
    (IeeeValue.finite_neg_isNegativeNonzero hy)
theorem ieeePrimitiveSignedZeroOverFiniteResult_negZero_of_negZero_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveSignedZeroOverFiniteResult
      IeeeValue.negZero (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveSignedZeroOverFiniteResult_negZero_of_negative_positive
    IeeeValue.negZero_isSignedZero
    (IeeeValue.finite_isFinite y)
    IeeeValue.negZero_isNegativeSigned
    (IeeeValue.finite_pos_isPositiveNonzero hy)
theorem ieeePrimitiveSignedZeroOverFiniteResult_posZero_of_negZero_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveSignedZeroOverFiniteResult
      IeeeValue.negZero (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveSignedZeroOverFiniteResult_posZero_of_negative_negative
    IeeeValue.negZero_isSignedZero
    (IeeeValue.finite_isFinite y)
    IeeeValue.negZero_isNegativeSigned
    (IeeeValue.finite_neg_isNegativeNonzero hy)
theorem ieeePrimitiveSignedZeroOverFiniteResult_noFlags
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveSignedZeroOverFiniteResult x y r) :
    r.noFlags := by
  rcases h with ⟨value, _, hr⟩
  rw [hr]
  exact IeeeOperationResult.valueNoFlags_noFlags value
theorem ieeePrimitiveSignedZeroOverFiniteResult_left_nan
    {y : IeeeValue} {r : IeeeOperationResult} :
    ¬ ieeePrimitiveSignedZeroOverFiniteResult IeeeValue.nan y r := by
  intro h
  rcases h with ⟨value, hvalue, _⟩
  simp [ieeePrimitiveSignedZeroOverFiniteValue, IeeeValue.isSignedZero] at hvalue
theorem ieeePrimitiveSignedZeroOverFiniteResult_right_nan
    {x : IeeeValue} {r : IeeeOperationResult} :
    ¬ ieeePrimitiveSignedZeroOverFiniteResult x IeeeValue.nan r := by
  intro h
  rcases h with ⟨value, hvalue, _⟩
  simp [ieeePrimitiveSignedZeroOverFiniteValue, IeeeValue.isFinite] at hvalue
/-- Concrete default selector for the quiet/default branch `signed zero / finite
nonzero = signed zero`.  Ordinary finite-zero denominators return `none` here
so they stay in the division-by-zero branch. -/
noncomputable def ieeePrimitiveSignedZeroOverFiniteResult?
    (x y : IeeeValue) : Option IeeeOperationResult := by
  classical
  exact
    match x, y with
    | IeeeValue.posZero, IeeeValue.finite y =>
        if 0 < y then
          some (IeeeOperationResult.valueNoFlags IeeeValue.posZero)
        else if y < 0 then
          some (IeeeOperationResult.valueNoFlags IeeeValue.negZero)
        else
          none
    | IeeeValue.negZero, IeeeValue.finite y =>
        if 0 < y then
          some (IeeeOperationResult.valueNoFlags IeeeValue.negZero)
        else if y < 0 then
          some (IeeeOperationResult.valueNoFlags IeeeValue.posZero)
        else
          none
    | _, _ => none
theorem ieeePrimitiveSignedZeroOverFiniteResult?_posZero_of_posZero_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveSignedZeroOverFiniteResult?
      IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simp [ieeePrimitiveSignedZeroOverFiniteResult?, hy]
theorem ieeePrimitiveSignedZeroOverFiniteResult?_negZero_of_posZero_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveSignedZeroOverFiniteResult?
      IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  have hnot : ¬ 0 < y := not_lt.mpr (le_of_lt hy)
  simp [ieeePrimitiveSignedZeroOverFiniteResult?, hnot, hy]
theorem ieeePrimitiveSignedZeroOverFiniteResult?_negZero_of_negZero_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveSignedZeroOverFiniteResult?
      IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simp [ieeePrimitiveSignedZeroOverFiniteResult?, hy]
theorem ieeePrimitiveSignedZeroOverFiniteResult?_posZero_of_negZero_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveSignedZeroOverFiniteResult?
      IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  have hnot : ¬ 0 < y := not_lt.mpr (le_of_lt hy)
  simp [ieeePrimitiveSignedZeroOverFiniteResult?, hnot, hy]
theorem ieeePrimitiveSignedZeroOverFiniteResult?_none_of_posZero_finite_zero :
    ieeePrimitiveSignedZeroOverFiniteResult?
      IeeeValue.posZero (IeeeValue.finite 0) = none := by
  simp [ieeePrimitiveSignedZeroOverFiniteResult?]
theorem ieeePrimitiveSignedZeroOverFiniteResult?_none_of_negZero_finite_zero :
    ieeePrimitiveSignedZeroOverFiniteResult?
      IeeeValue.negZero (IeeeValue.finite 0) = none := by
  simp [ieeePrimitiveSignedZeroOverFiniteResult?]
theorem ieeePrimitiveSignedZeroOverFiniteResult?_sound
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveSignedZeroOverFiniteResult? x y = some r) :
    ieeePrimitiveSignedZeroOverFiniteResult x y r := by
  cases x <;> cases y <;>
    simp [ieeePrimitiveSignedZeroOverFiniteResult?] at h ⊢
  · rename_i y
    by_cases hypos : 0 < y
    · simp [hypos] at h
      subst r
      exact
        ieeePrimitiveSignedZeroOverFiniteResult_posZero_of_posZero_finite_pos
          hypos
    · by_cases hyneg : y < 0
      · simp [hypos, hyneg] at h
        subst r
        exact
          ieeePrimitiveSignedZeroOverFiniteResult_negZero_of_posZero_finite_neg
            hyneg
      · simp [hypos, hyneg] at h
  · rename_i y
    by_cases hypos : 0 < y
    · simp [hypos] at h
      subst r
      exact
        ieeePrimitiveSignedZeroOverFiniteResult_negZero_of_negZero_finite_pos
          hypos
    · by_cases hyneg : y < 0
      · simp [hypos, hyneg] at h
        subst r
        exact
          ieeePrimitiveSignedZeroOverFiniteResult_posZero_of_negZero_finite_neg
            hyneg
      · simp [hypos, hyneg] at h
/-- Mode-independent signed-zero addition/subtraction branches.  These are the
signed-zero cases whose sign is forced without consulting the rounding mode:
same-signed zero addition and opposite-signed zero subtraction.  Opposite-signed
zero addition and same-signed zero subtraction remain outside this quiet branch
because their zero sign is rounding-mode sensitive. -/
def ieeePrimitiveAddSubSignedZeroResult
    (op : BasicOp) (x y : IeeeValue)
    (r : IeeeOperationResult) : Prop :=
  match op with
  | BasicOp.add =>
      (x = IeeeValue.posZero ∧ y = IeeeValue.posZero ∧
          r = IeeeOperationResult.valueNoFlags IeeeValue.posZero) ∨
        (x = IeeeValue.negZero ∧ y = IeeeValue.negZero ∧
          r = IeeeOperationResult.valueNoFlags IeeeValue.negZero)
  | BasicOp.sub =>
      (x = IeeeValue.posZero ∧ y = IeeeValue.negZero ∧
          r = IeeeOperationResult.valueNoFlags IeeeValue.posZero) ∨
        (x = IeeeValue.negZero ∧ y = IeeeValue.posZero ∧
          r = IeeeOperationResult.valueNoFlags IeeeValue.negZero)
  | BasicOp.mul => False
  | BasicOp.div => False
theorem ieeePrimitiveAddSubSignedZeroResult_add_posZero_posZero :
    ieeePrimitiveAddSubSignedZeroResult BasicOp.add
      IeeeValue.posZero IeeeValue.posZero
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  exact Or.inl ⟨rfl, rfl, rfl⟩
theorem ieeePrimitiveAddSubSignedZeroResult_add_negZero_negZero :
    ieeePrimitiveAddSubSignedZeroResult BasicOp.add
      IeeeValue.negZero IeeeValue.negZero
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  exact Or.inr ⟨rfl, rfl, rfl⟩
theorem ieeePrimitiveAddSubSignedZeroResult_sub_posZero_negZero :
    ieeePrimitiveAddSubSignedZeroResult BasicOp.sub
      IeeeValue.posZero IeeeValue.negZero
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  exact Or.inl ⟨rfl, rfl, rfl⟩
theorem ieeePrimitiveAddSubSignedZeroResult_sub_negZero_posZero :
    ieeePrimitiveAddSubSignedZeroResult BasicOp.sub
      IeeeValue.negZero IeeeValue.posZero
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  exact Or.inr ⟨rfl, rfl, rfl⟩
theorem ieeePrimitiveAddSubSignedZeroResult_noFlags
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubSignedZeroResult op x y r) :
    r.noFlags := by
  cases op with
  | add =>
    rcases h with h | h <;>
      rcases h with ⟨_, _, hr⟩ <;>
      subst r <;>
      exact IeeeOperationResult.valueNoFlags_noFlags _
  | sub =>
    rcases h with h | h <;>
      rcases h with ⟨_, _, hr⟩ <;>
      subst r <;>
      exact IeeeOperationResult.valueNoFlags_noFlags _
  | mul => cases h
  | div => cases h
theorem ieeePrimitiveAddSubSignedZeroResult_left_nan
    {op : BasicOp} {y : IeeeValue} {r : IeeeOperationResult} :
    ¬ ieeePrimitiveAddSubSignedZeroResult op IeeeValue.nan y r := by
  cases op <;> simp [ieeePrimitiveAddSubSignedZeroResult]
theorem ieeePrimitiveAddSubSignedZeroResult_right_nan
    {op : BasicOp} {x : IeeeValue} {r : IeeeOperationResult} :
    ¬ ieeePrimitiveAddSubSignedZeroResult op x IeeeValue.nan r := by
  cases op <;> simp [ieeePrimitiveAddSubSignedZeroResult]
/-- Concrete default selector for the mode-independent signed-zero add/sub
branches.  Opposite-signed zero addition and same-signed zero subtraction return
`none` here because their result sign depends on the rounding mode. -/
noncomputable def ieeePrimitiveAddSubSignedZeroResult?
    (op : BasicOp) (x y : IeeeValue) : Option IeeeOperationResult := by
  classical
  exact
    match op, x, y with
    | BasicOp.add, IeeeValue.posZero, IeeeValue.posZero =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero)
    | BasicOp.add, IeeeValue.negZero, IeeeValue.negZero =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero)
    | BasicOp.sub, IeeeValue.posZero, IeeeValue.negZero =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero)
    | BasicOp.sub, IeeeValue.negZero, IeeeValue.posZero =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero)
    | _, _, _ => none
theorem ieeePrimitiveAddSubSignedZeroResult?_add_posZero_posZero :
    ieeePrimitiveAddSubSignedZeroResult?
      BasicOp.add IeeeValue.posZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simp [ieeePrimitiveAddSubSignedZeroResult?]
theorem ieeePrimitiveAddSubSignedZeroResult?_add_negZero_negZero :
    ieeePrimitiveAddSubSignedZeroResult?
      BasicOp.add IeeeValue.negZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simp [ieeePrimitiveAddSubSignedZeroResult?]
theorem ieeePrimitiveAddSubSignedZeroResult?_sub_posZero_negZero :
    ieeePrimitiveAddSubSignedZeroResult?
      BasicOp.sub IeeeValue.posZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simp [ieeePrimitiveAddSubSignedZeroResult?]
theorem ieeePrimitiveAddSubSignedZeroResult?_sub_negZero_posZero :
    ieeePrimitiveAddSubSignedZeroResult?
      BasicOp.sub IeeeValue.negZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simp [ieeePrimitiveAddSubSignedZeroResult?]
theorem ieeePrimitiveAddSubSignedZeroResult?_none_add_posZero_negZero :
    ieeePrimitiveAddSubSignedZeroResult?
      BasicOp.add IeeeValue.posZero IeeeValue.negZero = none := by
  simp [ieeePrimitiveAddSubSignedZeroResult?]
theorem ieeePrimitiveAddSubSignedZeroResult?_none_add_negZero_posZero :
    ieeePrimitiveAddSubSignedZeroResult?
      BasicOp.add IeeeValue.negZero IeeeValue.posZero = none := by
  simp [ieeePrimitiveAddSubSignedZeroResult?]
theorem ieeePrimitiveAddSubSignedZeroResult?_none_sub_posZero_posZero :
    ieeePrimitiveAddSubSignedZeroResult?
      BasicOp.sub IeeeValue.posZero IeeeValue.posZero = none := by
  simp [ieeePrimitiveAddSubSignedZeroResult?]
theorem ieeePrimitiveAddSubSignedZeroResult?_none_sub_negZero_negZero :
    ieeePrimitiveAddSubSignedZeroResult?
      BasicOp.sub IeeeValue.negZero IeeeValue.negZero = none := by
  simp [ieeePrimitiveAddSubSignedZeroResult?]
theorem ieeePrimitiveAddSubSignedZeroResult?_sound
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubSignedZeroResult? op x y = some r) :
    ieeePrimitiveAddSubSignedZeroResult op x y r := by
  cases op <;> cases x <;> cases y <;>
    simp [ieeePrimitiveAddSubSignedZeroResult?,
      ieeePrimitiveAddSubSignedZeroResult] at h ⊢
  all_goals exact h.symm
/-- Rounding-mode-sensitive signed-zero add/sub branches for exact zero sums.
Opposite-signed zero addition and same-signed zero subtraction produce `-0`
only under round toward negative infinity, and `+0` under the other modeled
rounding modes. -/
def ieeePrimitiveAddSubZeroSumResult
    (mode : IeeeRoundingMode) (op : BasicOp) (x y : IeeeValue)
    (r : IeeeOperationResult) : Prop :=
  match op with
  | BasicOp.add =>
      (x = IeeeValue.posZero ∧ y = IeeeValue.negZero ∧
          r = IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) ∨
        (x = IeeeValue.negZero ∧ y = IeeeValue.posZero ∧
          r = IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue)
  | BasicOp.sub =>
      (x = IeeeValue.posZero ∧ y = IeeeValue.posZero ∧
          r = IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) ∨
        (x = IeeeValue.negZero ∧ y = IeeeValue.negZero ∧
          r = IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue)
  | BasicOp.mul => False
  | BasicOp.div => False
theorem ieeePrimitiveAddSubZeroSumResult_add_posZero_negZero
    (mode : IeeeRoundingMode) :
    ieeePrimitiveAddSubZeroSumResult mode BasicOp.add
      IeeeValue.posZero IeeeValue.negZero
      (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) := by
  exact Or.inl ⟨rfl, rfl, rfl⟩
theorem ieeePrimitiveAddSubZeroSumResult_add_negZero_posZero
    (mode : IeeeRoundingMode) :
    ieeePrimitiveAddSubZeroSumResult mode BasicOp.add
      IeeeValue.negZero IeeeValue.posZero
      (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) := by
  exact Or.inr ⟨rfl, rfl, rfl⟩
theorem ieeePrimitiveAddSubZeroSumResult_sub_posZero_posZero
    (mode : IeeeRoundingMode) :
    ieeePrimitiveAddSubZeroSumResult mode BasicOp.sub
      IeeeValue.posZero IeeeValue.posZero
      (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) := by
  exact Or.inl ⟨rfl, rfl, rfl⟩
theorem ieeePrimitiveAddSubZeroSumResult_sub_negZero_negZero
    (mode : IeeeRoundingMode) :
    ieeePrimitiveAddSubZeroSumResult mode BasicOp.sub
      IeeeValue.negZero IeeeValue.negZero
      (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) := by
  exact Or.inr ⟨rfl, rfl, rfl⟩
theorem ieeePrimitiveAddSubZeroSumResult_noFlags
    {mode : IeeeRoundingMode} {op : BasicOp}
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubZeroSumResult mode op x y r) :
    r.noFlags := by
  cases op with
  | add =>
    rcases h with h | h <;>
      rcases h with ⟨_, _, hr⟩ <;>
      subst r <;>
      exact IeeeOperationResult.valueNoFlags_noFlags _
  | sub =>
    rcases h with h | h <;>
      rcases h with ⟨_, _, hr⟩ <;>
      subst r <;>
      exact IeeeOperationResult.valueNoFlags_noFlags _
  | mul => cases h
  | div => cases h
theorem ieeePrimitiveAddSubZeroSumResult_left_nan
    {mode : IeeeRoundingMode} {op : BasicOp} {y : IeeeValue}
    {r : IeeeOperationResult} :
    ¬ ieeePrimitiveAddSubZeroSumResult mode op IeeeValue.nan y r := by
  cases op <;> simp [ieeePrimitiveAddSubZeroSumResult]
theorem ieeePrimitiveAddSubZeroSumResult_right_nan
    {mode : IeeeRoundingMode} {op : BasicOp} {x : IeeeValue}
    {r : IeeeOperationResult} :
    ¬ ieeePrimitiveAddSubZeroSumResult mode op x IeeeValue.nan r := by
  cases op <;> simp [ieeePrimitiveAddSubZeroSumResult]
theorem ieeePrimitiveAddSubZeroSumResult_finite_absurd
    (mode : IeeeRoundingMode) (op : BasicOp) (x y : ℝ) :
    ¬ ∃ r, ieeePrimitiveAddSubZeroSumResult mode op
      (IeeeValue.finite x) (IeeeValue.finite y) r := by
  intro h
  rcases h with ⟨r, h⟩
  cases op <;> simp [ieeePrimitiveAddSubZeroSumResult] at h
/-- Concrete selector for the rounding-mode-sensitive signed-zero add/sub
zero-sum branches.  Same-signed zero addition and opposite-signed zero
subtraction return `none` here because their sign is already mode-independent
and handled by `ieeePrimitiveAddSubSignedZeroResult?`. -/
def ieeePrimitiveAddSubZeroSumResult?
    (mode : IeeeRoundingMode) (op : BasicOp) (x y : IeeeValue) :
    Option IeeeOperationResult :=
  match op, x, y with
  | BasicOp.add, IeeeValue.posZero, IeeeValue.negZero =>
      some (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue)
  | BasicOp.add, IeeeValue.negZero, IeeeValue.posZero =>
      some (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue)
  | BasicOp.sub, IeeeValue.posZero, IeeeValue.posZero =>
      some (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue)
  | BasicOp.sub, IeeeValue.negZero, IeeeValue.negZero =>
      some (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue)
  | _, _, _ => none
theorem ieeePrimitiveAddSubZeroSumResult?_add_posZero_negZero
    (mode : IeeeRoundingMode) :
    ieeePrimitiveAddSubZeroSumResult?
      mode BasicOp.add IeeeValue.posZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) := by
  simp [ieeePrimitiveAddSubZeroSumResult?]
theorem ieeePrimitiveAddSubZeroSumResult?_add_negZero_posZero
    (mode : IeeeRoundingMode) :
    ieeePrimitiveAddSubZeroSumResult?
      mode BasicOp.add IeeeValue.negZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) := by
  simp [ieeePrimitiveAddSubZeroSumResult?]
theorem ieeePrimitiveAddSubZeroSumResult?_sub_posZero_posZero
    (mode : IeeeRoundingMode) :
    ieeePrimitiveAddSubZeroSumResult?
      mode BasicOp.sub IeeeValue.posZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) := by
  simp [ieeePrimitiveAddSubZeroSumResult?]
theorem ieeePrimitiveAddSubZeroSumResult?_sub_negZero_negZero
    (mode : IeeeRoundingMode) :
    ieeePrimitiveAddSubZeroSumResult?
      mode BasicOp.sub IeeeValue.negZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags mode.zeroSumSignedZeroValue) := by
  simp [ieeePrimitiveAddSubZeroSumResult?]
theorem ieeePrimitiveAddSubZeroSumResult?_none_add_posZero_posZero
    (mode : IeeeRoundingMode) :
    ieeePrimitiveAddSubZeroSumResult?
      mode BasicOp.add IeeeValue.posZero IeeeValue.posZero = none := by
  simp [ieeePrimitiveAddSubZeroSumResult?]
theorem ieeePrimitiveAddSubZeroSumResult?_none_add_negZero_negZero
    (mode : IeeeRoundingMode) :
    ieeePrimitiveAddSubZeroSumResult?
      mode BasicOp.add IeeeValue.negZero IeeeValue.negZero = none := by
  simp [ieeePrimitiveAddSubZeroSumResult?]
theorem ieeePrimitiveAddSubZeroSumResult?_none_sub_posZero_negZero
    (mode : IeeeRoundingMode) :
    ieeePrimitiveAddSubZeroSumResult?
      mode BasicOp.sub IeeeValue.posZero IeeeValue.negZero = none := by
  simp [ieeePrimitiveAddSubZeroSumResult?]
theorem ieeePrimitiveAddSubZeroSumResult?_none_sub_negZero_posZero
    (mode : IeeeRoundingMode) :
    ieeePrimitiveAddSubZeroSumResult?
      mode BasicOp.sub IeeeValue.negZero IeeeValue.posZero = none := by
  simp [ieeePrimitiveAddSubZeroSumResult?]
theorem ieeePrimitiveAddSubZeroSumResult?_sound
    {mode : IeeeRoundingMode} {op : BasicOp} {x y : IeeeValue}
    {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubZeroSumResult? mode op x y = some r) :
    ieeePrimitiveAddSubZeroSumResult mode op x y r := by
  cases op <;> cases x <;> cases y <;>
    simp [ieeePrimitiveAddSubZeroSumResult?,
      ieeePrimitiveAddSubZeroSumResult] at h ⊢
  all_goals exact h.symm
/-- Mixed finite-nonzero/signed-zero addition and subtraction branches.  These
cases are independent of the rounding mode: adding or subtracting a signed zero
from a nonzero finite payload leaves that payload unchanged, while a signed
zero minus a nonzero finite payload returns the negated finite payload. -/
def ieeePrimitiveAddSubFiniteSignedZeroResult
    (op : BasicOp) (x y : IeeeValue)
    (r : IeeeOperationResult) : Prop :=
  match op with
  | BasicOp.add =>
      (∃ xr : ℝ, x = IeeeValue.finite xr ∧ xr ≠ 0 ∧
          y.isSignedZero ∧
          r = IeeeOperationResult.valueNoFlags (IeeeValue.finite xr)) ∨
        (∃ yr : ℝ, x.isSignedZero ∧ y = IeeeValue.finite yr ∧ yr ≠ 0 ∧
          r = IeeeOperationResult.valueNoFlags (IeeeValue.finite yr))
  | BasicOp.sub =>
      (∃ xr : ℝ, x = IeeeValue.finite xr ∧ xr ≠ 0 ∧
          y.isSignedZero ∧
          r = IeeeOperationResult.valueNoFlags (IeeeValue.finite xr)) ∨
        (∃ yr : ℝ, x.isSignedZero ∧ y = IeeeValue.finite yr ∧ yr ≠ 0 ∧
          r = IeeeOperationResult.valueNoFlags (IeeeValue.finite (-yr)))
  | BasicOp.mul => False
  | BasicOp.div => False
theorem ieeePrimitiveAddSubFiniteSignedZeroResult_add_finite_signedZero
    {x : ℝ} (hx : x ≠ 0) {z : IeeeValue} (hz : z.isSignedZero) :
    ieeePrimitiveAddSubFiniteSignedZeroResult BasicOp.add
      (IeeeValue.finite x) z
      (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) := by
  exact Or.inl ⟨x, rfl, hx, hz, rfl⟩
theorem ieeePrimitiveAddSubFiniteSignedZeroResult_add_signedZero_finite
    {z : IeeeValue} (hz : z.isSignedZero) {y : ℝ} (hy : y ≠ 0) :
    ieeePrimitiveAddSubFiniteSignedZeroResult BasicOp.add
      z (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags (IeeeValue.finite y)) := by
  exact Or.inr ⟨y, hz, rfl, hy, rfl⟩
theorem ieeePrimitiveAddSubFiniteSignedZeroResult_sub_finite_signedZero
    {x : ℝ} (hx : x ≠ 0) {z : IeeeValue} (hz : z.isSignedZero) :
    ieeePrimitiveAddSubFiniteSignedZeroResult BasicOp.sub
      (IeeeValue.finite x) z
      (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) := by
  exact Or.inl ⟨x, rfl, hx, hz, rfl⟩
theorem ieeePrimitiveAddSubFiniteSignedZeroResult_sub_signedZero_finite
    {z : IeeeValue} (hz : z.isSignedZero) {y : ℝ} (hy : y ≠ 0) :
    ieeePrimitiveAddSubFiniteSignedZeroResult BasicOp.sub
      z (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags (IeeeValue.finite (-y))) := by
  exact Or.inr ⟨y, hz, rfl, hy, rfl⟩
theorem ieeePrimitiveAddSubFiniteSignedZeroResult_add_finite_posZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeePrimitiveAddSubFiniteSignedZeroResult BasicOp.add
      (IeeeValue.finite x) IeeeValue.posZero
      (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) :=
  ieeePrimitiveAddSubFiniteSignedZeroResult_add_finite_signedZero
    hx IeeeValue.posZero_isSignedZero
theorem ieeePrimitiveAddSubFiniteSignedZeroResult_add_finite_negZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeePrimitiveAddSubFiniteSignedZeroResult BasicOp.add
      (IeeeValue.finite x) IeeeValue.negZero
      (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) :=
  ieeePrimitiveAddSubFiniteSignedZeroResult_add_finite_signedZero
    hx IeeeValue.negZero_isSignedZero
theorem ieeePrimitiveAddSubFiniteSignedZeroResult_add_posZero_finite
    {y : ℝ} (hy : y ≠ 0) :
    ieeePrimitiveAddSubFiniteSignedZeroResult BasicOp.add
      IeeeValue.posZero (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags (IeeeValue.finite y)) :=
  ieeePrimitiveAddSubFiniteSignedZeroResult_add_signedZero_finite
    IeeeValue.posZero_isSignedZero hy
theorem ieeePrimitiveAddSubFiniteSignedZeroResult_add_negZero_finite
    {y : ℝ} (hy : y ≠ 0) :
    ieeePrimitiveAddSubFiniteSignedZeroResult BasicOp.add
      IeeeValue.negZero (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags (IeeeValue.finite y)) :=
  ieeePrimitiveAddSubFiniteSignedZeroResult_add_signedZero_finite
    IeeeValue.negZero_isSignedZero hy
theorem ieeePrimitiveAddSubFiniteSignedZeroResult_sub_finite_posZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeePrimitiveAddSubFiniteSignedZeroResult BasicOp.sub
      (IeeeValue.finite x) IeeeValue.posZero
      (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) :=
  ieeePrimitiveAddSubFiniteSignedZeroResult_sub_finite_signedZero
    hx IeeeValue.posZero_isSignedZero
theorem ieeePrimitiveAddSubFiniteSignedZeroResult_sub_finite_negZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeePrimitiveAddSubFiniteSignedZeroResult BasicOp.sub
      (IeeeValue.finite x) IeeeValue.negZero
      (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) :=
  ieeePrimitiveAddSubFiniteSignedZeroResult_sub_finite_signedZero
    hx IeeeValue.negZero_isSignedZero
theorem ieeePrimitiveAddSubFiniteSignedZeroResult_sub_posZero_finite
    {y : ℝ} (hy : y ≠ 0) :
    ieeePrimitiveAddSubFiniteSignedZeroResult BasicOp.sub
      IeeeValue.posZero (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags (IeeeValue.finite (-y))) :=
  ieeePrimitiveAddSubFiniteSignedZeroResult_sub_signedZero_finite
    IeeeValue.posZero_isSignedZero hy
theorem ieeePrimitiveAddSubFiniteSignedZeroResult_sub_negZero_finite
    {y : ℝ} (hy : y ≠ 0) :
    ieeePrimitiveAddSubFiniteSignedZeroResult BasicOp.sub
      IeeeValue.negZero (IeeeValue.finite y)
      (IeeeOperationResult.valueNoFlags (IeeeValue.finite (-y))) :=
  ieeePrimitiveAddSubFiniteSignedZeroResult_sub_signedZero_finite
    IeeeValue.negZero_isSignedZero hy
/-- Concrete selector for the mixed finite-nonzero/signed-zero add/sub branches.
It leaves ordinary `finite 0` payloads to the exact-zero branch instead of
silently turning them into signed zeros. -/
noncomputable def ieeePrimitiveAddSubFiniteSignedZeroResult?
    (op : BasicOp) (x y : IeeeValue) : Option IeeeOperationResult := by
  classical
  exact
    match op, x, y with
    | BasicOp.add, IeeeValue.finite xr, IeeeValue.posZero =>
        if xr = 0 then none
        else some (IeeeOperationResult.valueNoFlags (IeeeValue.finite xr))
    | BasicOp.add, IeeeValue.finite xr, IeeeValue.negZero =>
        if xr = 0 then none
        else some (IeeeOperationResult.valueNoFlags (IeeeValue.finite xr))
    | BasicOp.add, IeeeValue.posZero, IeeeValue.finite yr =>
        if yr = 0 then none
        else some (IeeeOperationResult.valueNoFlags (IeeeValue.finite yr))
    | BasicOp.add, IeeeValue.negZero, IeeeValue.finite yr =>
        if yr = 0 then none
        else some (IeeeOperationResult.valueNoFlags (IeeeValue.finite yr))
    | BasicOp.sub, IeeeValue.finite xr, IeeeValue.posZero =>
        if xr = 0 then none
        else some (IeeeOperationResult.valueNoFlags (IeeeValue.finite xr))
    | BasicOp.sub, IeeeValue.finite xr, IeeeValue.negZero =>
        if xr = 0 then none
        else some (IeeeOperationResult.valueNoFlags (IeeeValue.finite xr))
    | BasicOp.sub, IeeeValue.posZero, IeeeValue.finite yr =>
        if yr = 0 then none
        else some (IeeeOperationResult.valueNoFlags (IeeeValue.finite (-yr)))
    | BasicOp.sub, IeeeValue.negZero, IeeeValue.finite yr =>
        if yr = 0 then none
        else some (IeeeOperationResult.valueNoFlags (IeeeValue.finite (-yr)))
    | _, _, _ => none
theorem ieeePrimitiveAddSubFiniteSignedZeroResult?_add_finite_posZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeePrimitiveAddSubFiniteSignedZeroResult?
        BasicOp.add (IeeeValue.finite x) IeeeValue.posZero =
      some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) := by
  simp [ieeePrimitiveAddSubFiniteSignedZeroResult?, hx]
theorem ieeePrimitiveAddSubFiniteSignedZeroResult?_add_finite_negZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeePrimitiveAddSubFiniteSignedZeroResult?
        BasicOp.add (IeeeValue.finite x) IeeeValue.negZero =
      some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) := by
  simp [ieeePrimitiveAddSubFiniteSignedZeroResult?, hx]
theorem ieeePrimitiveAddSubFiniteSignedZeroResult?_add_posZero_finite
    {y : ℝ} (hy : y ≠ 0) :
    ieeePrimitiveAddSubFiniteSignedZeroResult?
        BasicOp.add IeeeValue.posZero (IeeeValue.finite y) =
      some (IeeeOperationResult.valueNoFlags (IeeeValue.finite y)) := by
  simp [ieeePrimitiveAddSubFiniteSignedZeroResult?, hy]
theorem ieeePrimitiveAddSubFiniteSignedZeroResult?_add_negZero_finite
    {y : ℝ} (hy : y ≠ 0) :
    ieeePrimitiveAddSubFiniteSignedZeroResult?
        BasicOp.add IeeeValue.negZero (IeeeValue.finite y) =
      some (IeeeOperationResult.valueNoFlags (IeeeValue.finite y)) := by
  simp [ieeePrimitiveAddSubFiniteSignedZeroResult?, hy]
theorem ieeePrimitiveAddSubFiniteSignedZeroResult?_sub_finite_posZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeePrimitiveAddSubFiniteSignedZeroResult?
        BasicOp.sub (IeeeValue.finite x) IeeeValue.posZero =
      some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) := by
  simp [ieeePrimitiveAddSubFiniteSignedZeroResult?, hx]
theorem ieeePrimitiveAddSubFiniteSignedZeroResult?_sub_finite_negZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeePrimitiveAddSubFiniteSignedZeroResult?
        BasicOp.sub (IeeeValue.finite x) IeeeValue.negZero =
      some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) := by
  simp [ieeePrimitiveAddSubFiniteSignedZeroResult?, hx]
theorem ieeePrimitiveAddSubFiniteSignedZeroResult?_sub_posZero_finite
    {y : ℝ} (hy : y ≠ 0) :
    ieeePrimitiveAddSubFiniteSignedZeroResult?
        BasicOp.sub IeeeValue.posZero (IeeeValue.finite y) =
      some (IeeeOperationResult.valueNoFlags (IeeeValue.finite (-y))) := by
  simp [ieeePrimitiveAddSubFiniteSignedZeroResult?, hy]
theorem ieeePrimitiveAddSubFiniteSignedZeroResult?_sub_negZero_finite
    {y : ℝ} (hy : y ≠ 0) :
    ieeePrimitiveAddSubFiniteSignedZeroResult?
        BasicOp.sub IeeeValue.negZero (IeeeValue.finite y) =
      some (IeeeOperationResult.valueNoFlags (IeeeValue.finite (-y))) := by
  simp [ieeePrimitiveAddSubFiniteSignedZeroResult?, hy]
theorem ieeePrimitiveAddSubFiniteSignedZeroResult?_sound
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubFiniteSignedZeroResult? op x y = some r) :
    ieeePrimitiveAddSubFiniteSignedZeroResult op x y r := by
  classical
  cases op <;> cases x <;> cases y <;>
    simp [ieeePrimitiveAddSubFiniteSignedZeroResult?,
      ieeePrimitiveAddSubFiniteSignedZeroResult, IeeeValue.isSignedZero] at h ⊢
  all_goals exact ⟨h.1, h.2.symm⟩
theorem ieeePrimitiveAddSubFiniteSignedZeroResult_noFlags
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubFiniteSignedZeroResult op x y r) :
    r.noFlags := by
  cases op with
  | add =>
    rcases h with h | h <;>
      rcases h with ⟨_, _, _, _, hr⟩ <;>
      subst r <;>
      exact IeeeOperationResult.valueNoFlags_noFlags _
  | sub =>
    rcases h with h | h <;>
      rcases h with ⟨_, _, _, _, hr⟩ <;>
      subst r <;>
      exact IeeeOperationResult.valueNoFlags_noFlags _
  | mul => cases h
  | div => cases h
theorem ieeePrimitiveAddSubFiniteSignedZeroResult_left_nan
    {op : BasicOp} {y : IeeeValue} {r : IeeeOperationResult} :
    ¬ ieeePrimitiveAddSubFiniteSignedZeroResult op IeeeValue.nan y r := by
  cases op <;> simp [ieeePrimitiveAddSubFiniteSignedZeroResult,
    IeeeValue.isSignedZero]
theorem ieeePrimitiveAddSubFiniteSignedZeroResult_right_nan
    {op : BasicOp} {x : IeeeValue} {r : IeeeOperationResult} :
    ¬ ieeePrimitiveAddSubFiniteSignedZeroResult op x IeeeValue.nan r := by
  cases op <;> simp [ieeePrimitiveAddSubFiniteSignedZeroResult,
    IeeeValue.isSignedZero]
theorem ieeePrimitiveAddSubFiniteSignedZeroResult_finite_absurd
    (op : BasicOp) (x y : ℝ) :
    ¬ ∃ r, ieeePrimitiveAddSubFiniteSignedZeroResult op
      (IeeeValue.finite x) (IeeeValue.finite y) r := by
  intro h
  rcases h with ⟨r, h⟩
  cases op <;> simp [ieeePrimitiveAddSubFiniteSignedZeroResult,
    IeeeValue.isSignedZero] at h
/-- IEEE primitive add/sub infinity propagation for modeled non-invalid
infinity cases.  The predicate records no-flag propagation of infinities through
addition and subtraction when the other operand is finite, a signed zero, or
the compatible infinity; multiplication when at least one operand is an infinity
and the other is signed nonzero; and division of an infinity by a signed finite
nonzero denominator.  NaNs are intentionally excluded here so the quiet-NaN
propagation branch remains disjoint from these constructors.  Invalid
indeterminate cases, payloads, signaling NaNs, and traps are handled by other
predicates or remain outside this quiet/default layer. -/
def ieeePrimitiveInfinityPropagationResult
    (op : BasicOp) (x y : IeeeValue)
    (r : IeeeOperationResult) : Prop :=
  match op with
  | BasicOp.add =>
      (x = IeeeValue.posInf ∧ (y.isFinite ∨ y = IeeeValue.posInf) ∧
          r = IeeeOperationResult.valueNoFlags IeeeValue.posInf) ∨
        (y = IeeeValue.posInf ∧ (x.isFinite ∨ x = IeeeValue.posInf) ∧
          r = IeeeOperationResult.valueNoFlags IeeeValue.posInf) ∨
        (x = IeeeValue.negInf ∧ (y.isFinite ∨ y = IeeeValue.negInf) ∧
          r = IeeeOperationResult.valueNoFlags IeeeValue.negInf) ∨
        (y = IeeeValue.negInf ∧ (x.isFinite ∨ x = IeeeValue.negInf) ∧
          r = IeeeOperationResult.valueNoFlags IeeeValue.negInf)
  | BasicOp.sub =>
      (x = IeeeValue.posInf ∧ (y.isFinite ∨ y = IeeeValue.negInf) ∧
          r = IeeeOperationResult.valueNoFlags IeeeValue.posInf) ∨
        (y = IeeeValue.negInf ∧ (x.isFinite ∨ x = IeeeValue.posInf) ∧
          r = IeeeOperationResult.valueNoFlags IeeeValue.posInf) ∨
        (x = IeeeValue.negInf ∧ (y.isFinite ∨ y = IeeeValue.posInf) ∧
          r = IeeeOperationResult.valueNoFlags IeeeValue.negInf) ∨
        (y = IeeeValue.posInf ∧ (x.isFinite ∨ x = IeeeValue.negInf) ∧
          r = IeeeOperationResult.valueNoFlags IeeeValue.negInf)
  | BasicOp.mul => ieeePrimitiveMulInfinityPropagationResult x y r
  | BasicOp.div => ieeePrimitiveDivInfinityPropagationResult x y r
theorem ieeePrimitiveInfinityPropagationResult_add_posInf_posInf :
    ieeePrimitiveInfinityPropagationResult BasicOp.add
      IeeeValue.posInf IeeeValue.posInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  change
    (IeeeValue.posInf = IeeeValue.posInf ∧
        (IeeeValue.posInf.isFinite ∨ IeeeValue.posInf = IeeeValue.posInf) ∧
        IeeeOperationResult.valueNoFlags IeeeValue.posInf =
          IeeeOperationResult.valueNoFlags IeeeValue.posInf) ∨
      _
  exact Or.inl (And.intro rfl (And.intro (Or.inr rfl) rfl))
theorem ieeePrimitiveInfinityPropagationResult_add_negInf_negInf :
    ieeePrimitiveInfinityPropagationResult BasicOp.add
      IeeeValue.negInf IeeeValue.negInf
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  change _ ∨ _ ∨
    (IeeeValue.negInf = IeeeValue.negInf ∧
        (IeeeValue.negInf.isFinite ∨ IeeeValue.negInf = IeeeValue.negInf) ∧
        IeeeOperationResult.valueNoFlags IeeeValue.negInf =
          IeeeOperationResult.valueNoFlags IeeeValue.negInf) ∨
      _
  exact Or.inr
    (Or.inr (Or.inl (And.intro rfl (And.intro (Or.inr rfl) rfl))))
theorem ieeePrimitiveInfinityPropagationResult_sub_posInf_negInf :
    ieeePrimitiveInfinityPropagationResult BasicOp.sub
      IeeeValue.posInf IeeeValue.negInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  change
    (IeeeValue.posInf = IeeeValue.posInf ∧
        (IeeeValue.negInf.isFinite ∨ IeeeValue.negInf = IeeeValue.negInf) ∧
        IeeeOperationResult.valueNoFlags IeeeValue.posInf =
          IeeeOperationResult.valueNoFlags IeeeValue.posInf) ∨
      _
  exact Or.inl (And.intro rfl (And.intro (Or.inr rfl) rfl))
theorem ieeePrimitiveInfinityPropagationResult_sub_negInf_posInf :
    ieeePrimitiveInfinityPropagationResult BasicOp.sub
      IeeeValue.negInf IeeeValue.posInf
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  change _ ∨ _ ∨
    (IeeeValue.negInf = IeeeValue.negInf ∧
        (IeeeValue.posInf.isFinite ∨ IeeeValue.posInf = IeeeValue.posInf) ∧
        IeeeOperationResult.valueNoFlags IeeeValue.negInf =
          IeeeOperationResult.valueNoFlags IeeeValue.negInf) ∨
      _
  exact Or.inr
    (Or.inr (Or.inl (And.intro rfl (And.intro (Or.inr rfl) rfl))))
theorem ieeePrimitiveInfinityPropagationResult_add_posInf_of_isFinite
    {y : IeeeValue} (hy : y.isFinite) :
    ieeePrimitiveInfinityPropagationResult BasicOp.add
      IeeeValue.posInf y
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  change
    (IeeeValue.posInf = IeeeValue.posInf ∧
        (y.isFinite ∨ y = IeeeValue.posInf) ∧
        IeeeOperationResult.valueNoFlags IeeeValue.posInf =
          IeeeOperationResult.valueNoFlags IeeeValue.posInf) ∨
      _
  exact Or.inl (And.intro rfl (And.intro (Or.inl hy) rfl))
theorem ieeePrimitiveInfinityPropagationResult_add_isFinite_posInf
    {x : IeeeValue} (hx : x.isFinite) :
    ieeePrimitiveInfinityPropagationResult BasicOp.add
      x IeeeValue.posInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  change _ ∨
    (IeeeValue.posInf = IeeeValue.posInf ∧
        (x.isFinite ∨ x = IeeeValue.posInf) ∧
        IeeeOperationResult.valueNoFlags IeeeValue.posInf =
          IeeeOperationResult.valueNoFlags IeeeValue.posInf) ∨
      _
  exact Or.inr (Or.inl (And.intro rfl (And.intro (Or.inl hx) rfl)))
theorem ieeePrimitiveInfinityPropagationResult_add_negInf_of_isFinite
    {y : IeeeValue} (hy : y.isFinite) :
    ieeePrimitiveInfinityPropagationResult BasicOp.add
      IeeeValue.negInf y
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  change _ ∨ _ ∨
    (IeeeValue.negInf = IeeeValue.negInf ∧
        (y.isFinite ∨ y = IeeeValue.negInf) ∧
        IeeeOperationResult.valueNoFlags IeeeValue.negInf =
          IeeeOperationResult.valueNoFlags IeeeValue.negInf) ∨
      _
  exact Or.inr (Or.inr (Or.inl (And.intro rfl (And.intro (Or.inl hy) rfl))))
theorem ieeePrimitiveInfinityPropagationResult_add_isFinite_negInf
    {x : IeeeValue} (hx : x.isFinite) :
    ieeePrimitiveInfinityPropagationResult BasicOp.add
      x IeeeValue.negInf
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  change _ ∨ _ ∨ _ ∨
    (IeeeValue.negInf = IeeeValue.negInf ∧
        (x.isFinite ∨ x = IeeeValue.negInf) ∧
        IeeeOperationResult.valueNoFlags IeeeValue.negInf =
          IeeeOperationResult.valueNoFlags IeeeValue.negInf)
  exact Or.inr
    (Or.inr (Or.inr (And.intro rfl (And.intro (Or.inl hx) rfl))))
theorem ieeePrimitiveInfinityPropagationResult_sub_posInf_of_isFinite
    {y : IeeeValue} (hy : y.isFinite) :
    ieeePrimitiveInfinityPropagationResult BasicOp.sub
      IeeeValue.posInf y
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  change
    (IeeeValue.posInf = IeeeValue.posInf ∧
        (y.isFinite ∨ y = IeeeValue.negInf) ∧
        IeeeOperationResult.valueNoFlags IeeeValue.posInf =
          IeeeOperationResult.valueNoFlags IeeeValue.posInf) ∨
      _
  exact Or.inl (And.intro rfl (And.intro (Or.inl hy) rfl))
theorem ieeePrimitiveInfinityPropagationResult_sub_isFinite_negInf
    {x : IeeeValue} (hx : x.isFinite) :
    ieeePrimitiveInfinityPropagationResult BasicOp.sub
      x IeeeValue.negInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  change _ ∨
    (IeeeValue.negInf = IeeeValue.negInf ∧
        (x.isFinite ∨ x = IeeeValue.posInf) ∧
        IeeeOperationResult.valueNoFlags IeeeValue.posInf =
          IeeeOperationResult.valueNoFlags IeeeValue.posInf) ∨
      _
  exact Or.inr (Or.inl (And.intro rfl (And.intro (Or.inl hx) rfl)))
theorem ieeePrimitiveInfinityPropagationResult_sub_negInf_of_isFinite
    {y : IeeeValue} (hy : y.isFinite) :
    ieeePrimitiveInfinityPropagationResult BasicOp.sub
      IeeeValue.negInf y
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  change _ ∨ _ ∨
    (IeeeValue.negInf = IeeeValue.negInf ∧
        (y.isFinite ∨ y = IeeeValue.posInf) ∧
        IeeeOperationResult.valueNoFlags IeeeValue.negInf =
          IeeeOperationResult.valueNoFlags IeeeValue.negInf) ∨
      _
  exact Or.inr (Or.inr (Or.inl (And.intro rfl (And.intro (Or.inl hy) rfl))))
theorem ieeePrimitiveInfinityPropagationResult_sub_isFinite_posInf
    {x : IeeeValue} (hx : x.isFinite) :
    ieeePrimitiveInfinityPropagationResult BasicOp.sub
      x IeeeValue.posInf
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  change _ ∨ _ ∨ _ ∨
    (IeeeValue.posInf = IeeeValue.posInf ∧
        (x.isFinite ∨ x = IeeeValue.negInf) ∧
        IeeeOperationResult.valueNoFlags IeeeValue.negInf =
          IeeeOperationResult.valueNoFlags IeeeValue.negInf)
  exact Or.inr
    (Or.inr (Or.inr (And.intro rfl (And.intro (Or.inl hx) rfl))))
theorem ieeePrimitiveInfinityPropagationResult_mul
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveMulInfinityPropagationResult x y r) :
    ieeePrimitiveInfinityPropagationResult BasicOp.mul x y r :=
  h
theorem ieeePrimitiveInfinityPropagationResult_div
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveDivInfinityPropagationResult x y r) :
    ieeePrimitiveInfinityPropagationResult BasicOp.div x y r :=
  h
theorem ieeePrimitiveInfinityPropagationResult_mul_posInf_posInf :
    ieeePrimitiveInfinityPropagationResult BasicOp.mul
      IeeeValue.posInf IeeeValue.posInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveInfinityPropagationResult_mul
    ieeePrimitiveMulInfinityPropagationResult_posInf_posInf
theorem ieeePrimitiveInfinityPropagationResult_mul_posInf_negInf :
    ieeePrimitiveInfinityPropagationResult BasicOp.mul
      IeeeValue.posInf IeeeValue.negInf
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveInfinityPropagationResult_mul
    ieeePrimitiveMulInfinityPropagationResult_posInf_negInf
theorem ieeePrimitiveInfinityPropagationResult_mul_negInf_posInf :
    ieeePrimitiveInfinityPropagationResult BasicOp.mul
      IeeeValue.negInf IeeeValue.posInf
      (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveInfinityPropagationResult_mul
    ieeePrimitiveMulInfinityPropagationResult_negInf_posInf
theorem ieeePrimitiveInfinityPropagationResult_mul_negInf_negInf :
    ieeePrimitiveInfinityPropagationResult BasicOp.mul
      IeeeValue.negInf IeeeValue.negInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveInfinityPropagationResult_mul
    ieeePrimitiveMulInfinityPropagationResult_negInf_negInf
theorem ieeePrimitiveInfinityPropagationResult_left_nan
    {op : BasicOp} {y : IeeeValue} {r : IeeeOperationResult} :
    ¬ ieeePrimitiveInfinityPropagationResult op IeeeValue.nan y r := by
  cases op <;>
    simp [ieeePrimitiveInfinityPropagationResult,
      ieeePrimitiveMulInfinityPropagationResult,
      ieeePrimitiveMulInfinityValue,
      ieeePrimitiveDivInfinityPropagationResult,
      ieeePrimitiveDivInfinityValue,
      IeeeValue.isFinite, IeeeValue.isInfinite,
      IeeeValue.isPositiveNonzero, IeeeValue.isNegativeNonzero]
theorem ieeePrimitiveInfinityPropagationResult_right_nan
    {op : BasicOp} {x : IeeeValue} {r : IeeeOperationResult} :
    ¬ ieeePrimitiveInfinityPropagationResult op x IeeeValue.nan r := by
  cases op <;>
    simp [ieeePrimitiveInfinityPropagationResult,
      ieeePrimitiveMulInfinityPropagationResult,
      ieeePrimitiveMulInfinityValue,
      ieeePrimitiveDivInfinityPropagationResult,
      ieeePrimitiveDivInfinityValue,
      IeeeValue.isFinite, IeeeValue.isInfinite,
      IeeeValue.isPositiveNonzero, IeeeValue.isNegativeNonzero]
theorem ieeePrimitiveInfinityPropagationResult_noFlags
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInfinityPropagationResult op x y r) :
    r.noFlags := by
  cases op with
  | add =>
    simp [ieeePrimitiveInfinityPropagationResult] at h
    rcases h with h | h | h | h <;>
      rcases h with ⟨_, _, hr⟩ <;>
      subst r <;>
      exact IeeeOperationResult.valueNoFlags_noFlags _
  | sub =>
    simp [ieeePrimitiveInfinityPropagationResult] at h
    rcases h with h | h | h | h <;>
      rcases h with ⟨_, _, hr⟩ <;>
      subst r <;>
      exact IeeeOperationResult.valueNoFlags_noFlags _
  | mul =>
    exact ieeePrimitiveMulInfinityPropagationResult_noFlags h
  | div =>
    exact ieeePrimitiveDivInfinityPropagationResult_noFlags h
/-- Concrete default selector for the quiet/default non-invalid infinity
propagation branches.  Invalid cases such as opposite-signed infinity addition,
same-signed infinity subtraction, zero times infinity, and infinity divided by
zero or infinity return `none` here so they remain in their flagged/default
branches. -/
noncomputable def ieeePrimitiveInfinityPropagationResult?
    (op : BasicOp) (x y : IeeeValue) : Option IeeeOperationResult := by
  classical
  exact
    match op, x, y with
    | BasicOp.add, IeeeValue.posInf, IeeeValue.finite _ =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
    | BasicOp.add, IeeeValue.posInf, IeeeValue.posZero =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
    | BasicOp.add, IeeeValue.posInf, IeeeValue.negZero =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
    | BasicOp.add, IeeeValue.posInf, IeeeValue.posInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
    | BasicOp.add, IeeeValue.finite _, IeeeValue.posInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
    | BasicOp.add, IeeeValue.posZero, IeeeValue.posInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
    | BasicOp.add, IeeeValue.negZero, IeeeValue.posInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
    | BasicOp.add, IeeeValue.negInf, IeeeValue.finite _ =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
    | BasicOp.add, IeeeValue.negInf, IeeeValue.posZero =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
    | BasicOp.add, IeeeValue.negInf, IeeeValue.negZero =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
    | BasicOp.add, IeeeValue.negInf, IeeeValue.negInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
    | BasicOp.add, IeeeValue.finite _, IeeeValue.negInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
    | BasicOp.add, IeeeValue.posZero, IeeeValue.negInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
    | BasicOp.add, IeeeValue.negZero, IeeeValue.negInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
    | BasicOp.sub, IeeeValue.posInf, IeeeValue.finite _ =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
    | BasicOp.sub, IeeeValue.posInf, IeeeValue.posZero =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
    | BasicOp.sub, IeeeValue.posInf, IeeeValue.negZero =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
    | BasicOp.sub, IeeeValue.posInf, IeeeValue.negInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
    | BasicOp.sub, IeeeValue.finite _, IeeeValue.negInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
    | BasicOp.sub, IeeeValue.posZero, IeeeValue.negInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
    | BasicOp.sub, IeeeValue.negZero, IeeeValue.negInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
    | BasicOp.sub, IeeeValue.negInf, IeeeValue.finite _ =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
    | BasicOp.sub, IeeeValue.negInf, IeeeValue.posZero =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
    | BasicOp.sub, IeeeValue.negInf, IeeeValue.negZero =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
    | BasicOp.sub, IeeeValue.negInf, IeeeValue.posInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
    | BasicOp.sub, IeeeValue.finite _, IeeeValue.posInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
    | BasicOp.sub, IeeeValue.posZero, IeeeValue.posInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
    | BasicOp.sub, IeeeValue.negZero, IeeeValue.posInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
    | BasicOp.mul, IeeeValue.posInf, IeeeValue.posInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
    | BasicOp.mul, IeeeValue.posInf, IeeeValue.negInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
    | BasicOp.mul, IeeeValue.negInf, IeeeValue.posInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
    | BasicOp.mul, IeeeValue.negInf, IeeeValue.negInf =>
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
    | BasicOp.mul, IeeeValue.posInf, IeeeValue.finite y =>
        if 0 < y then
          some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
        else if y < 0 then
          some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
        else
          none
    | BasicOp.mul, IeeeValue.negInf, IeeeValue.finite y =>
        if 0 < y then
          some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
        else if y < 0 then
          some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
        else
          none
    | BasicOp.mul, IeeeValue.finite x, IeeeValue.posInf =>
        if 0 < x then
          some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
        else if x < 0 then
          some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
        else
          none
    | BasicOp.mul, IeeeValue.finite x, IeeeValue.negInf =>
        if 0 < x then
          some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
        else if x < 0 then
          some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
        else
          none
    | BasicOp.div, IeeeValue.posInf, IeeeValue.finite y =>
        if 0 < y then
          some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
        else if y < 0 then
          some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
        else
          none
    | BasicOp.div, IeeeValue.negInf, IeeeValue.finite y =>
        if 0 < y then
          some (IeeeOperationResult.valueNoFlags IeeeValue.negInf)
        else if y < 0 then
          some (IeeeOperationResult.valueNoFlags IeeeValue.posInf)
        else
          none
    | _, _, _ => none
theorem ieeePrimitiveInfinityPropagationResult?_add_posInf_posInf :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.add IeeeValue.posInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_add_negInf_negInf :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.add IeeeValue.negInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_add_posInf_finite
    (x : ℝ) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.add IeeeValue.posInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_add_finite_posInf
    (x : ℝ) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.add (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_add_negInf_finite
    (x : ℝ) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.add IeeeValue.negInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_add_finite_negInf
    (x : ℝ) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.add (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_sub_posInf_negInf :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.sub IeeeValue.posInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_sub_negInf_posInf :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.sub IeeeValue.negInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_sub_posInf_finite
    (x : ℝ) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.sub IeeeValue.posInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_sub_finite_posInf
    (x : ℝ) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.sub (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_sub_negInf_finite
    (x : ℝ) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.sub IeeeValue.negInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_sub_finite_negInf
    (x : ℝ) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.sub (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_mul_posInf_posInf :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.mul IeeeValue.posInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_mul_posInf_negInf :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.mul IeeeValue.posInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_mul_negInf_posInf :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.mul IeeeValue.negInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_mul_negInf_negInf :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.mul IeeeValue.negInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_mul_posInf_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.mul IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?, hy]
theorem ieeePrimitiveInfinityPropagationResult?_mul_negInf_of_posInf_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.mul IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  have hnot : ¬ 0 < y := not_lt.mpr (le_of_lt hy)
  simp [ieeePrimitiveInfinityPropagationResult?, hnot, hy]
theorem ieeePrimitiveInfinityPropagationResult?_mul_negInf_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.mul IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?, hy]
theorem ieeePrimitiveInfinityPropagationResult?_mul_posInf_of_negInf_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.mul IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  have hnot : ¬ 0 < y := not_lt.mpr (le_of_lt hy)
  simp [ieeePrimitiveInfinityPropagationResult?, hnot, hy]
theorem ieeePrimitiveInfinityPropagationResult?_mul_finite_pos_posInf
    {x : ℝ} (hx : 0 < x) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?, hx]
theorem ieeePrimitiveInfinityPropagationResult?_mul_negInf_of_finite_neg_posInf
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  have hnot : ¬ 0 < x := not_lt.mpr (le_of_lt hx)
  simp [ieeePrimitiveInfinityPropagationResult?, hnot, hx]
theorem ieeePrimitiveInfinityPropagationResult?_mul_finite_pos_negInf
    {x : ℝ} (hx : 0 < x) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?, hx]
theorem ieeePrimitiveInfinityPropagationResult?_mul_posInf_of_finite_neg_negInf
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  have hnot : ¬ 0 < x := not_lt.mpr (le_of_lt hx)
  simp [ieeePrimitiveInfinityPropagationResult?, hnot, hx]
theorem ieeePrimitiveInfinityPropagationResult?_mul_posInf_finite_zero :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.mul IeeeValue.posInf (IeeeValue.finite 0) = none := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_mul_negInf_finite_zero :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.mul IeeeValue.negInf (IeeeValue.finite 0) = none := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_mul_finite_zero_posInf :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.mul (IeeeValue.finite 0) IeeeValue.posInf = none := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_mul_finite_zero_negInf :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.mul (IeeeValue.finite 0) IeeeValue.negInf = none := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_div_posInf_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.div IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?, hy]
theorem ieeePrimitiveInfinityPropagationResult?_div_negInf_of_posInf_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.div IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  have hnot : ¬ 0 < y := not_lt.mpr (le_of_lt hy)
  simp [ieeePrimitiveInfinityPropagationResult?, hnot, hy]
theorem ieeePrimitiveInfinityPropagationResult?_div_negInf_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.div IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  simp [ieeePrimitiveInfinityPropagationResult?, hy]
theorem ieeePrimitiveInfinityPropagationResult?_div_posInf_of_negInf_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.div IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  have hnot : ¬ 0 < y := not_lt.mpr (le_of_lt hy)
  simp [ieeePrimitiveInfinityPropagationResult?, hnot, hy]
theorem ieeePrimitiveInfinityPropagationResult?_div_posInf_finite_zero :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.div IeeeValue.posInf (IeeeValue.finite 0) = none := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_div_negInf_finite_zero :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.div IeeeValue.negInf (IeeeValue.finite 0) = none := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_add_posInf_negInf :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.add IeeeValue.posInf IeeeValue.negInf = none := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_add_negInf_posInf :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.add IeeeValue.negInf IeeeValue.posInf = none := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_sub_posInf_posInf :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.sub IeeeValue.posInf IeeeValue.posInf = none := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_sub_negInf_negInf :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.sub IeeeValue.negInf IeeeValue.negInf = none := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_div_posInf_posInf :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.div IeeeValue.posInf IeeeValue.posInf = none := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_mul_posInf_posZero :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.mul IeeeValue.posInf IeeeValue.posZero = none := by
  simp [ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveInfinityPropagationResult?_mul_posZero_posInf :
    ieeePrimitiveInfinityPropagationResult?
      BasicOp.mul IeeeValue.posZero IeeeValue.posInf = none := by
  simp [ieeePrimitiveInfinityPropagationResult?]
/-- Combined primitive-operation special-value result predicate for the first
IEEE branches modeled here: quiet NaN propagation, invalid-operation
special-value inputs, non-invalid infinity propagation, signed-zero
multiplication, signed-zero-over-finite division, finite-over-infinity
signed-zero division, mode-independent signed-zero add/sub cases, and mixed
finite-nonzero/signed-zero add/sub cases. -/
def ieeePrimitiveSpecialValueResult
    (op : BasicOp) (x y : IeeeValue)
    (r : IeeeOperationResult) : Prop :=
  ieeeQuietNaNPropagationResult x y r ∨
    ieeePrimitiveInvalidOperationResult op x y r ∨
      ieeePrimitiveInfinityPropagationResult op x y r ∨
        (op = BasicOp.mul ∧ ieeePrimitiveMulSignedZeroResult x y r) ∨
          (op = BasicOp.div ∧
              ieeePrimitiveSignedZeroOverFiniteResult x y r) ∨
            ieeePrimitiveFiniteOverInfinityResult op x y r ∨
              ieeePrimitiveAddSubSignedZeroResult op x y r ∨
                ieeePrimitiveAddSubFiniteSignedZeroResult op x y r
theorem ieeePrimitiveSpecialValueResult_left_nan
    (op : BasicOp) (y : IeeeValue) :
    ieeePrimitiveSpecialValueResult op IeeeValue.nan y
      (IeeeOperationResult.valueNoFlags IeeeValue.nan) := by
  exact Or.inl (ieeeQuietNaNPropagationResult_left_nan y)
theorem ieeePrimitiveSpecialValueResult_right_nan
    (op : BasicOp) (x : IeeeValue) :
    ieeePrimitiveSpecialValueResult op x IeeeValue.nan
      (IeeeOperationResult.valueNoFlags IeeeValue.nan) := by
  exact Or.inl (ieeeQuietNaNPropagationResult_right_nan x)
theorem ieeePrimitiveSpecialValueResult_quietNaNDefault?
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeQuietNaNPropagationResult? x y = some r) :
    ieeePrimitiveSpecialValueResult op x y r := by
  exact Or.inl (ieeeQuietNaNPropagationResult?_sound h)
theorem ieeePrimitiveSpecialValueResult_invalid_default
    {op : BasicOp} {x y : IeeeValue}
    (hinput : ieeePrimitiveInvalidOperationInput op x y) :
    ieeePrimitiveSpecialValueResult op x y
      ieeeInvalidOperationDefaultResult := by
  exact Or.inr (Or.inl
    (ieeePrimitiveInvalidOperationDefaultResult_ieeePrimitiveInvalidOperationResult
      hinput))
theorem ieeePrimitiveSpecialValueResult_invalidOperationDefault?
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInvalidOperationResult? op x y = some r) :
    ieeePrimitiveSpecialValueResult op x y r := by
  exact Or.inr (Or.inl (ieeePrimitiveInvalidOperationResult?_sound h))
theorem ieeePrimitiveSpecialValueResult_infinity
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInfinityPropagationResult op x y r) :
    ieeePrimitiveSpecialValueResult op x y r := by
  exact Or.inr (Or.inr (Or.inl h))
theorem ieeePrimitiveSpecialValueResult_finiteOverInfinity
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveFiniteOverInfinityResult op x y r) :
    ieeePrimitiveSpecialValueResult op x y r := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
theorem ieeePrimitiveSpecialValueResult_finiteOverInfinityDefault?
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveFiniteOverInfinityResult? op x y = some r) :
    ieeePrimitiveSpecialValueResult op x y r :=
  ieeePrimitiveSpecialValueResult_finiteOverInfinity
    (ieeePrimitiveFiniteOverInfinityResult?_sound h)
theorem ieeePrimitiveSpecialValueResult_mulSignedZero
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveMulSignedZeroResult x y r) :
    ieeePrimitiveSpecialValueResult BasicOp.mul x y r := by
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h⟩)))
theorem ieeePrimitiveSpecialValueResult_mulSignedZeroDefault?
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveMulSignedZeroResult? x y = some r) :
    ieeePrimitiveSpecialValueResult BasicOp.mul x y r :=
  ieeePrimitiveSpecialValueResult_mulSignedZero
    (ieeePrimitiveMulSignedZeroResult?_sound h)
theorem ieeePrimitiveSpecialValueResult_signedZeroOverFinite
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveSignedZeroOverFiniteResult x y r) :
    ieeePrimitiveSpecialValueResult BasicOp.div x y r := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))))
theorem ieeePrimitiveSpecialValueResult_signedZeroOverFiniteDefault?
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveSignedZeroOverFiniteResult? x y = some r) :
    ieeePrimitiveSpecialValueResult BasicOp.div x y r :=
  ieeePrimitiveSpecialValueResult_signedZeroOverFinite
    (ieeePrimitiveSignedZeroOverFiniteResult?_sound h)
theorem ieeePrimitiveSpecialValueResult_addSubSignedZero
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubSignedZeroResult op x y r) :
    ieeePrimitiveSpecialValueResult op x y r := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
theorem ieeePrimitiveSpecialValueResult_addSubSignedZeroDefault?
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubSignedZeroResult? op x y = some r) :
    ieeePrimitiveSpecialValueResult op x y r :=
  ieeePrimitiveSpecialValueResult_addSubSignedZero
    (ieeePrimitiveAddSubSignedZeroResult?_sound h)
theorem ieeePrimitiveSpecialValueResult_addSubFiniteSignedZero
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubFiniteSignedZeroResult op x y r) :
    ieeePrimitiveSpecialValueResult op x y r := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
theorem ieeePrimitiveSpecialValueResult_addSubFiniteSignedZeroDefault?
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubFiniteSignedZeroResult? op x y = some r) :
    ieeePrimitiveSpecialValueResult op x y r :=
  ieeePrimitiveSpecialValueResult_addSubFiniteSignedZero
    (ieeePrimitiveAddSubFiniteSignedZeroResult?_sound h)
/-- Concrete ordered selector for the currently modeled primitive
special-value branches.  It tries quiet NaN propagation, invalid operation,
non-invalid infinity propagation, finite-over-infinity division, signed-zero
multiplication, signed-zero-over-finite division, mode-independent signed-zero
add/sub, and mixed finite-nonzero/signed-zero add/sub in that order.  Branches
outside this modeled quiet/default layer return `none`. -/
noncomputable def ieeePrimitiveSpecialValueResult?
    (op : BasicOp) (x y : IeeeValue) : Option IeeeOperationResult := by
  classical
  exact
    match ieeeQuietNaNPropagationResult? x y with
    | some r => some r
    | none =>
        match ieeePrimitiveInvalidOperationResult? op x y with
        | some r => some r
        | none =>
            match ieeePrimitiveInfinityPropagationResult? op x y with
            | some r => some r
            | none =>
                match ieeePrimitiveFiniteOverInfinityResult? op x y with
                | some r => some r
                | none =>
                    match op with
                    | BasicOp.mul => ieeePrimitiveMulSignedZeroResult? x y
                    | BasicOp.div =>
                        ieeePrimitiveSignedZeroOverFiniteResult? x y
                    | BasicOp.add =>
                        match ieeePrimitiveAddSubSignedZeroResult? op x y with
                        | some r => some r
                        | none =>
                            ieeePrimitiveAddSubFiniteSignedZeroResult? op x y
                    | BasicOp.sub =>
                        match ieeePrimitiveAddSubSignedZeroResult? op x y with
                        | some r => some r
                        | none =>
                            ieeePrimitiveAddSubFiniteSignedZeroResult? op x y
theorem ieeePrimitiveSpecialValueResult?_quietNaNDefault?
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeQuietNaNPropagationResult? x y = some r) :
    ieeePrimitiveSpecialValueResult? op x y = some r := by
  simp [ieeePrimitiveSpecialValueResult?, h]
theorem ieeePrimitiveSpecialValueResult?_left_nan
    (op : BasicOp) (y : IeeeValue) :
    ieeePrimitiveSpecialValueResult? op IeeeValue.nan y =
      some (IeeeOperationResult.valueNoFlags IeeeValue.nan) :=
  ieeePrimitiveSpecialValueResult?_quietNaNDefault?
    (ieeeQuietNaNPropagationResult?_left_nan y)
theorem ieeePrimitiveSpecialValueResult?_right_nan
    (op : BasicOp) (x : IeeeValue) :
    ieeePrimitiveSpecialValueResult? op x IeeeValue.nan =
      some (IeeeOperationResult.valueNoFlags IeeeValue.nan) :=
  ieeePrimitiveSpecialValueResult?_quietNaNDefault?
    (ieeeQuietNaNPropagationResult?_right_nan x)
theorem ieeePrimitiveSpecialValueResult?_add_posInf_posInf :
  ieeePrimitiveSpecialValueResult?
      BasicOp.add IeeeValue.posInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  simp [ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.oppositeSignedInfinities,
    ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveSpecialValueResult?_sub_posInf_negInf :
  ieeePrimitiveSpecialValueResult?
      BasicOp.sub IeeeValue.posInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  simp [ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.sameSignedInfinities,
    ieeePrimitiveInfinityPropagationResult?]
theorem ieeePrimitiveSpecialValueResult?_mul_negInf_of_posInf_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  have hnot : ¬ 0 < y := not_lt.mpr (le_of_lt hy)
  have hyne : y ≠ 0 := ne_of_lt hy
  simp [ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.isZero,
    IeeeValue.isInfinite, ieeePrimitiveInfinityPropagationResult?,
    hnot, hy, hyne]
theorem ieeePrimitiveSpecialValueResult?_div_posInf_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  simp [ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.isZero,
    IeeeValue.isInfinite, ieeePrimitiveInfinityPropagationResult?, hy]
theorem ieeePrimitiveSpecialValueResult?_infinityDefault?
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInfinityPropagationResult? op x y = some r) :
    ieeePrimitiveSpecialValueResult? op x y = some r := by
  classical
  cases op <;> cases x <;> cases y <;>
    simp [ieeePrimitiveSpecialValueResult?, ieeeQuietNaNPropagationResult?,
      ieeePrimitiveInvalidOperationResult?, ieeePrimitiveInvalidOperationInput,
      ieeePrimitiveInfinityPropagationResult?, IeeeValue.isZero,
      IeeeValue.isInfinite, IeeeValue.oppositeSignedInfinities,
      IeeeValue.sameSignedInfinities] at h ⊢
  all_goals try simp [h]
  all_goals
    rename_i x
    by_cases hx : x = 0
    · subst x
      simp at h
    · simp [hx]
theorem ieeePrimitiveSpecialValueResult?_add_negInf_negInf :
    ieeePrimitiveSpecialValueResult?
      BasicOp.add IeeeValue.negInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    ieeePrimitiveInfinityPropagationResult?_add_negInf_negInf
theorem ieeePrimitiveSpecialValueResult?_add_posInf_finite
    (x : ℝ) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.add IeeeValue.posInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_add_posInf_finite x)
theorem ieeePrimitiveSpecialValueResult?_add_finite_posInf
    (x : ℝ) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.add (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_add_finite_posInf x)
theorem ieeePrimitiveSpecialValueResult?_add_negInf_finite
    (x : ℝ) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.add IeeeValue.negInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_add_negInf_finite x)
theorem ieeePrimitiveSpecialValueResult?_add_finite_negInf
    (x : ℝ) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.add (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_add_finite_negInf x)
theorem ieeePrimitiveSpecialValueResult?_sub_negInf_posInf :
    ieeePrimitiveSpecialValueResult?
      BasicOp.sub IeeeValue.negInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    ieeePrimitiveInfinityPropagationResult?_sub_negInf_posInf
theorem ieeePrimitiveSpecialValueResult?_sub_posInf_finite
    (x : ℝ) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.sub IeeeValue.posInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_sub_posInf_finite x)
theorem ieeePrimitiveSpecialValueResult?_sub_finite_posInf
    (x : ℝ) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.sub (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_sub_finite_posInf x)
theorem ieeePrimitiveSpecialValueResult?_sub_negInf_finite
    (x : ℝ) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.sub IeeeValue.negInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_sub_negInf_finite x)
theorem ieeePrimitiveSpecialValueResult?_sub_finite_negInf
    (x : ℝ) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.sub (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_sub_finite_negInf x)
theorem ieeePrimitiveSpecialValueResult?_mul_posInf_posInf :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul IeeeValue.posInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    ieeePrimitiveInfinityPropagationResult?_mul_posInf_posInf
theorem ieeePrimitiveSpecialValueResult?_mul_posInf_negInf :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul IeeeValue.posInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    ieeePrimitiveInfinityPropagationResult?_mul_posInf_negInf
theorem ieeePrimitiveSpecialValueResult?_mul_negInf_posInf :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul IeeeValue.negInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    ieeePrimitiveInfinityPropagationResult?_mul_negInf_posInf
theorem ieeePrimitiveSpecialValueResult?_mul_negInf_negInf :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul IeeeValue.negInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    ieeePrimitiveInfinityPropagationResult?_mul_negInf_negInf
theorem ieeePrimitiveSpecialValueResult?_mul_posInf_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_mul_posInf_finite_pos hy)
theorem ieeePrimitiveSpecialValueResult?_mul_negInf_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_mul_negInf_finite_pos hy)
theorem ieeePrimitiveSpecialValueResult?_mul_posInf_of_negInf_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_mul_posInf_of_negInf_finite_neg hy)
theorem ieeePrimitiveSpecialValueResult?_mul_finite_pos_posInf
    {x : ℝ} (hx : 0 < x) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_mul_finite_pos_posInf hx)
theorem ieeePrimitiveSpecialValueResult?_mul_negInf_of_finite_neg_posInf
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_mul_negInf_of_finite_neg_posInf hx)
theorem ieeePrimitiveSpecialValueResult?_mul_finite_pos_negInf
    {x : ℝ} (hx : 0 < x) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_mul_finite_pos_negInf hx)
theorem ieeePrimitiveSpecialValueResult?_mul_posInf_of_finite_neg_negInf
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_mul_posInf_of_finite_neg_negInf hx)
theorem ieeePrimitiveSpecialValueResult?_div_negInf_of_posInf_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_div_negInf_of_posInf_finite_neg hy)
theorem ieeePrimitiveSpecialValueResult?_div_negInf_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_div_negInf_finite_pos hy)
theorem ieeePrimitiveSpecialValueResult?_div_posInf_of_negInf_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveSpecialValueResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_div_posInf_of_negInf_finite_neg hy)
theorem ieeePrimitiveSpecialValueResult?_add_posInf_negInf :
    ieeePrimitiveSpecialValueResult?
      BasicOp.add IeeeValue.posInf IeeeValue.negInf =
        some ieeeInvalidOperationDefaultResult := by
  simp [ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.oppositeSignedInfinities]
theorem ieeePrimitiveSpecialValueResult?_of_invalidOperationInput
    {op : BasicOp} {x y : IeeeValue}
    (hinput : ieeePrimitiveInvalidOperationInput op x y) :
    ieeePrimitiveSpecialValueResult? op x y =
      some ieeeInvalidOperationDefaultResult := by
  classical
  have hnan : ieeeQuietNaNPropagationResult? x y = none := by
    cases op <;> cases x <;> cases y <;>
      simp [ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationInput,
        IeeeValue.isZero, IeeeValue.isInfinite,
        IeeeValue.oppositeSignedInfinities, IeeeValue.sameSignedInfinities] at hinput ⊢
  have hinvalid : ieeePrimitiveInvalidOperationResult? op x y =
      some ieeeInvalidOperationDefaultResult :=
    ieeePrimitiveInvalidOperationResult?_of_input hinput
  unfold ieeePrimitiveSpecialValueResult?
  rw [hnan, hinvalid]
theorem ieeePrimitiveSpecialValueResult?_add_negInf_posInf :
    ieeePrimitiveSpecialValueResult?
      BasicOp.add IeeeValue.negInf IeeeValue.posInf =
        some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveSpecialValueResult?_of_invalidOperationInput
    ieeePrimitiveInvalidOperationInput_add_negInf_posInf
theorem ieeePrimitiveSpecialValueResult?_sub_posInf_posInf :
    ieeePrimitiveSpecialValueResult?
      BasicOp.sub IeeeValue.posInf IeeeValue.posInf =
        some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveSpecialValueResult?_of_invalidOperationInput
    ieeePrimitiveInvalidOperationInput_sub_posInf_posInf
theorem ieeePrimitiveSpecialValueResult?_sub_negInf_negInf :
    ieeePrimitiveSpecialValueResult?
      BasicOp.sub IeeeValue.negInf IeeeValue.negInf =
        some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveSpecialValueResult?_of_invalidOperationInput
    ieeePrimitiveInvalidOperationInput_sub_negInf_negInf
theorem ieeePrimitiveSpecialValueResult?_mul_zero_inf
    {x y : IeeeValue} (hx : x.isZero) (hy : y.isInfinite) :
    ieeePrimitiveSpecialValueResult? BasicOp.mul x y =
      some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveSpecialValueResult?_of_invalidOperationInput
    (ieeePrimitiveInvalidOperationInput_mul_zero_inf hx hy)
theorem ieeePrimitiveSpecialValueResult?_mul_inf_zero
    {x y : IeeeValue} (hx : x.isInfinite) (hy : y.isZero) :
    ieeePrimitiveSpecialValueResult? BasicOp.mul x y =
      some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveSpecialValueResult?_of_invalidOperationInput
    (ieeePrimitiveInvalidOperationInput_mul_inf_zero hx hy)
theorem ieeePrimitiveSpecialValueResult?_div_zero_zero
    {x y : IeeeValue} (hx : x.isZero) (hy : y.isZero) :
    ieeePrimitiveSpecialValueResult? BasicOp.div x y =
      some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveSpecialValueResult?_of_invalidOperationInput
    (ieeePrimitiveInvalidOperationInput_div_zero_zero hx hy)
theorem ieeePrimitiveSpecialValueResult?_div_inf_inf
    {x y : IeeeValue} (hx : x.isInfinite) (hy : y.isInfinite) :
    ieeePrimitiveSpecialValueResult? BasicOp.div x y =
      some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveSpecialValueResult?_of_invalidOperationInput
    (ieeePrimitiveInvalidOperationInput_div_inf_inf hx hy)
theorem ieeePrimitiveSpecialValueResult?_div_posInf_posInf :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div IeeeValue.posInf IeeeValue.posInf =
        some ieeeInvalidOperationDefaultResult := by
  simp [ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.isZero, IeeeValue.isInfinite]
theorem ieeePrimitiveSpecialValueResult?_div_finite_zero_posZero :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div (IeeeValue.finite 0) IeeeValue.posZero =
        some ieeeInvalidOperationDefaultResult := by
  simp [ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.isZero, IeeeValue.isInfinite]
theorem ieeePrimitiveSpecialValueResult?_div_finite_zero_negZero :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div (IeeeValue.finite 0) IeeeValue.negZero =
        some ieeeInvalidOperationDefaultResult := by
  simp [ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.isZero, IeeeValue.isInfinite]
theorem ieeePrimitiveSpecialValueResult?_div_finite_zero_finite_zero :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div (IeeeValue.finite 0) (IeeeValue.finite 0) =
        some ieeeInvalidOperationDefaultResult := by
  simp [ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.isZero, IeeeValue.isInfinite]
theorem ieeePrimitiveSpecialValueResult?_div_posZero_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simp [ieeePrimitiveSpecialValueResult?, ieeeQuietNaNPropagationResult?,
    ieeePrimitiveInvalidOperationResult?, ieeePrimitiveInvalidOperationInput,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveSignedZeroOverFiniteResult?, IeeeValue.isZero,
    IeeeValue.isInfinite, hy, ne_of_gt hy]
theorem ieeePrimitiveSpecialValueResult?_div_posZero_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simp [ieeePrimitiveSpecialValueResult?, ieeeQuietNaNPropagationResult?,
    ieeePrimitiveInvalidOperationResult?, ieeePrimitiveInvalidOperationInput,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveSignedZeroOverFiniteResult?, IeeeValue.isZero,
    IeeeValue.isInfinite, not_lt_of_gt hy, hy, ne_of_lt hy]
theorem ieeePrimitiveSpecialValueResult?_div_negZero_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simp [ieeePrimitiveSpecialValueResult?, ieeeQuietNaNPropagationResult?,
    ieeePrimitiveInvalidOperationResult?, ieeePrimitiveInvalidOperationInput,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveSignedZeroOverFiniteResult?, IeeeValue.isZero,
    IeeeValue.isInfinite, hy, ne_of_gt hy]
theorem ieeePrimitiveSpecialValueResult?_div_negZero_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simp [ieeePrimitiveSpecialValueResult?, ieeeQuietNaNPropagationResult?,
    ieeePrimitiveInvalidOperationResult?, ieeePrimitiveInvalidOperationInput,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveSignedZeroOverFiniteResult?, IeeeValue.isZero,
    IeeeValue.isInfinite, not_lt_of_gt hy, hy, ne_of_lt hy]
theorem ieeePrimitiveSpecialValueResult?_finiteOverInfinityDefault?
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveFiniteOverInfinityResult? op x y = some r) :
    ieeePrimitiveSpecialValueResult? op x y = some r := by
  classical
  cases op <;> cases x <;> cases y <;>
    simp [ieeePrimitiveSpecialValueResult?, ieeeQuietNaNPropagationResult?,
      ieeePrimitiveInvalidOperationResult?, ieeePrimitiveInvalidOperationInput,
      ieeePrimitiveInfinityPropagationResult?,
      ieeePrimitiveFiniteOverInfinityResult?, IeeeValue.isZero,
      IeeeValue.isInfinite] at h ⊢
  all_goals simp [h]
theorem ieeePrimitiveSpecialValueResult?_div_posZero_posInf :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div IeeeValue.posZero IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveSpecialValueResult?_finiteOverInfinityDefault?
    ieeePrimitiveFiniteOverInfinityResult?_posZero_posInf
theorem ieeePrimitiveSpecialValueResult?_div_negZero_of_posZero_negInf :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div IeeeValue.posZero IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveSpecialValueResult?_finiteOverInfinityDefault?
    ieeePrimitiveFiniteOverInfinityResult?_negZero_of_posZero_negInf
theorem ieeePrimitiveSpecialValueResult?_div_negZero_posInf :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div IeeeValue.negZero IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveSpecialValueResult?_finiteOverInfinityDefault?
    ieeePrimitiveFiniteOverInfinityResult?_negZero_posInf
theorem ieeePrimitiveSpecialValueResult?_div_posZero_of_negZero_negInf :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div IeeeValue.negZero IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveSpecialValueResult?_finiteOverInfinityDefault?
    ieeePrimitiveFiniteOverInfinityResult?_posZero_of_negZero_negInf
theorem ieeePrimitiveSpecialValueResult?_div_finite_nonneg_posInf
    {x : ℝ} (hx : 0 ≤ x) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveSpecialValueResult?_finiteOverInfinityDefault?
    (ieeePrimitiveFiniteOverInfinityResult?_finite_nonneg_posInf hx)
theorem ieeePrimitiveSpecialValueResult?_div_negZero_of_finite_neg_posInf
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveSpecialValueResult?_finiteOverInfinityDefault?
    (ieeePrimitiveFiniteOverInfinityResult?_negZero_of_finite_neg_posInf hx)
theorem ieeePrimitiveSpecialValueResult?_div_finite_nonneg_negInf
    {x : ℝ} (hx : 0 ≤ x) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveSpecialValueResult?_finiteOverInfinityDefault?
    (ieeePrimitiveFiniteOverInfinityResult?_finite_nonneg_negInf hx)
theorem ieeePrimitiveSpecialValueResult?_div_posZero_of_finite_neg_negInf
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveSpecialValueResult?_finiteOverInfinityDefault?
    (ieeePrimitiveFiniteOverInfinityResult?_posZero_of_finite_neg_negInf hx)
theorem ieeePrimitiveSpecialValueResult?_div_finite_zero_posInf :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div (IeeeValue.finite 0) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveSpecialValueResult?_finiteOverInfinityDefault?
    ieeePrimitiveFiniteOverInfinityResult?_finite_zero_posInf
theorem ieeePrimitiveSpecialValueResult?_div_finite_zero_negInf :
    ieeePrimitiveSpecialValueResult?
      BasicOp.div (IeeeValue.finite 0) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveSpecialValueResult?_finiteOverInfinityDefault?
    ieeePrimitiveFiniteOverInfinityResult?_finite_zero_negInf
theorem ieeePrimitiveSpecialValueResult?_mulSignedZeroDefault?
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveMulSignedZeroResult? x y = some r) :
    ieeePrimitiveSpecialValueResult? BasicOp.mul x y = some r := by
  classical
  cases x <;> cases y <;>
    simp [ieeePrimitiveSpecialValueResult?, ieeeQuietNaNPropagationResult?,
      ieeePrimitiveInvalidOperationResult?, ieeePrimitiveInvalidOperationInput,
      ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
      ieeePrimitiveMulSignedZeroResult?, IeeeValue.isZero, IeeeValue.isInfinite] at h ⊢
  all_goals exact h
theorem ieeePrimitiveSpecialValueResult?_mul_posZero_posZero :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul IeeeValue.posZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveSpecialValueResult?_mulSignedZeroDefault?
    ieeePrimitiveMulSignedZeroResult?_posZero_posZero
theorem ieeePrimitiveSpecialValueResult?_mul_posZero_negZero :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul IeeeValue.posZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveSpecialValueResult?_mulSignedZeroDefault?
    ieeePrimitiveMulSignedZeroResult?_posZero_negZero
theorem ieeePrimitiveSpecialValueResult?_mul_negZero_posZero :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul IeeeValue.negZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveSpecialValueResult?_mulSignedZeroDefault?
    ieeePrimitiveMulSignedZeroResult?_negZero_posZero
theorem ieeePrimitiveSpecialValueResult?_mul_negZero_negZero :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul IeeeValue.negZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveSpecialValueResult?_mulSignedZeroDefault?
    ieeePrimitiveMulSignedZeroResult?_negZero_negZero
theorem ieeePrimitiveSpecialValueResult?_mul_posZero_finite_nonneg
    {y : ℝ} (hy : 0 ≤ y) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveSpecialValueResult?_mulSignedZeroDefault?
    (ieeePrimitiveMulSignedZeroResult?_posZero_finite_nonneg hy)
theorem ieeePrimitiveSpecialValueResult?_mul_negZero_of_posZero_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveSpecialValueResult?_mulSignedZeroDefault?
    (ieeePrimitiveMulSignedZeroResult?_negZero_of_posZero_finite_neg hy)
theorem ieeePrimitiveSpecialValueResult?_mul_finite_nonneg_posZero
    {x : ℝ} (hx : 0 ≤ x) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveSpecialValueResult?_mulSignedZeroDefault?
    (ieeePrimitiveMulSignedZeroResult?_finite_nonneg_posZero hx)
theorem ieeePrimitiveSpecialValueResult?_mul_negZero_of_finite_neg_posZero
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveSpecialValueResult?_mulSignedZeroDefault?
    (ieeePrimitiveMulSignedZeroResult?_negZero_of_finite_neg_posZero hx)
theorem ieeePrimitiveSpecialValueResult?_mul_negZero_finite_nonneg
    {y : ℝ} (hy : 0 ≤ y) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveSpecialValueResult?_mulSignedZeroDefault?
    (ieeePrimitiveMulSignedZeroResult?_negZero_finite_nonneg hy)
theorem ieeePrimitiveSpecialValueResult?_mul_posZero_of_negZero_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveSpecialValueResult?_mulSignedZeroDefault?
    (ieeePrimitiveMulSignedZeroResult?_posZero_of_negZero_finite_neg hy)
theorem ieeePrimitiveSpecialValueResult?_mul_finite_nonneg_negZero
    {x : ℝ} (hx : 0 ≤ x) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveSpecialValueResult?_mulSignedZeroDefault?
    (ieeePrimitiveMulSignedZeroResult?_finite_nonneg_negZero hx)
theorem ieeePrimitiveSpecialValueResult?_mul_posZero_of_finite_neg_negZero
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveSpecialValueResult?_mulSignedZeroDefault?
    (ieeePrimitiveMulSignedZeroResult?_posZero_of_finite_neg_negZero hx)
theorem ieeePrimitiveSpecialValueResult?_add_finite_posZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.add (IeeeValue.finite x) IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) := by
  simp [ieeePrimitiveSpecialValueResult?, ieeeQuietNaNPropagationResult?,
    ieeePrimitiveInvalidOperationResult?, ieeePrimitiveInvalidOperationInput,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveAddSubSignedZeroResult?, ieeePrimitiveAddSubFiniteSignedZeroResult?,
    IeeeValue.oppositeSignedInfinities, hx]
theorem ieeePrimitiveSpecialValueResult?_add_finite_negZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.add (IeeeValue.finite x) IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) := by
  simp [ieeePrimitiveSpecialValueResult?, ieeeQuietNaNPropagationResult?,
    ieeePrimitiveInvalidOperationResult?, ieeePrimitiveInvalidOperationInput,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveAddSubSignedZeroResult?, ieeePrimitiveAddSubFiniteSignedZeroResult?,
    IeeeValue.oppositeSignedInfinities, hx]
theorem ieeePrimitiveSpecialValueResult?_add_posZero_finite
    {y : ℝ} (hy : y ≠ 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.add IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite y)) := by
  simp [ieeePrimitiveSpecialValueResult?, ieeeQuietNaNPropagationResult?,
    ieeePrimitiveInvalidOperationResult?, ieeePrimitiveInvalidOperationInput,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveAddSubSignedZeroResult?, ieeePrimitiveAddSubFiniteSignedZeroResult?,
    IeeeValue.oppositeSignedInfinities, hy]
theorem ieeePrimitiveSpecialValueResult?_add_negZero_finite
    {y : ℝ} (hy : y ≠ 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.add IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite y)) := by
  simp [ieeePrimitiveSpecialValueResult?, ieeeQuietNaNPropagationResult?,
    ieeePrimitiveInvalidOperationResult?, ieeePrimitiveInvalidOperationInput,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveAddSubSignedZeroResult?, ieeePrimitiveAddSubFiniteSignedZeroResult?,
    IeeeValue.oppositeSignedInfinities, hy]
theorem ieeePrimitiveSpecialValueResult?_sub_finite_posZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.sub (IeeeValue.finite x) IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) := by
  simp [ieeePrimitiveSpecialValueResult?, ieeeQuietNaNPropagationResult?,
    ieeePrimitiveInvalidOperationResult?, ieeePrimitiveInvalidOperationInput,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveAddSubSignedZeroResult?, ieeePrimitiveAddSubFiniteSignedZeroResult?,
    IeeeValue.sameSignedInfinities, hx]
theorem ieeePrimitiveSpecialValueResult?_sub_finite_negZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.sub (IeeeValue.finite x) IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) := by
  simp [ieeePrimitiveSpecialValueResult?, ieeeQuietNaNPropagationResult?,
    ieeePrimitiveInvalidOperationResult?, ieeePrimitiveInvalidOperationInput,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveAddSubSignedZeroResult?, ieeePrimitiveAddSubFiniteSignedZeroResult?,
    IeeeValue.sameSignedInfinities, hx]
theorem ieeePrimitiveSpecialValueResult?_sub_posZero_finite
    {y : ℝ} (hy : y ≠ 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.sub IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite (-y))) := by
  simp [ieeePrimitiveSpecialValueResult?, ieeeQuietNaNPropagationResult?,
    ieeePrimitiveInvalidOperationResult?, ieeePrimitiveInvalidOperationInput,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveAddSubSignedZeroResult?, ieeePrimitiveAddSubFiniteSignedZeroResult?,
    IeeeValue.sameSignedInfinities, hy]
theorem ieeePrimitiveSpecialValueResult?_sub_negZero_finite
    {y : ℝ} (hy : y ≠ 0) :
    ieeePrimitiveSpecialValueResult?
      BasicOp.sub IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite (-y))) := by
  simp [ieeePrimitiveSpecialValueResult?, ieeeQuietNaNPropagationResult?,
    ieeePrimitiveInvalidOperationResult?, ieeePrimitiveInvalidOperationInput,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveAddSubSignedZeroResult?, ieeePrimitiveAddSubFiniteSignedZeroResult?,
    IeeeValue.sameSignedInfinities, hy]
/-- Primitive IEEE value-level branch predicate before ordinary finite
rounding.  This combines the quiet/default special-value branches with the
finite-nonzero-over-zero division-by-zero branch.  It is still a predicate
layer: traps, signaling NaNs, payload propagation, and an executable hardware
instruction are intentionally outside this definition. -/
def ieeePrimitiveValueBranchResult
    (op : BasicOp) (x y : IeeeValue)
    (r : IeeeOperationResult) : Prop :=
  ieeePrimitiveSpecialValueResult op x y r ∨
    (op = BasicOp.div ∧ ieeeDivisionByZeroResult x y r)
theorem ieeePrimitiveValueBranchResult_special
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveSpecialValueResult op x y r) :
    ieeePrimitiveValueBranchResult op x y r :=
  Or.inl h
theorem ieeePrimitiveValueBranchResult_divisionByZero
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeDivisionByZeroResult x y r) :
    ieeePrimitiveValueBranchResult BasicOp.div x y r :=
  Or.inr ⟨rfl, h⟩
theorem ieeePrimitiveValueBranchResult_divisionByZeroDefault?
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeDivisionByZeroDefaultResult? x y = some r) :
    ieeePrimitiveValueBranchResult BasicOp.div x y r :=
  ieeePrimitiveValueBranchResult_divisionByZero
    (ieeeDivisionByZeroDefaultResult?_sound h)
theorem ieeePrimitiveValueBranchResult_left_nan
    (op : BasicOp) (y : IeeeValue) :
    ieeePrimitiveValueBranchResult op IeeeValue.nan y
      (IeeeOperationResult.valueNoFlags IeeeValue.nan) :=
  ieeePrimitiveValueBranchResult_special
    (ieeePrimitiveSpecialValueResult_left_nan op y)
theorem ieeePrimitiveValueBranchResult_right_nan
    (op : BasicOp) (x : IeeeValue) :
    ieeePrimitiveValueBranchResult op x IeeeValue.nan
      (IeeeOperationResult.valueNoFlags IeeeValue.nan) :=
  ieeePrimitiveValueBranchResult_special
    (ieeePrimitiveSpecialValueResult_right_nan op x)
theorem ieeePrimitiveValueBranchResult_quietNaNDefault?
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeQuietNaNPropagationResult? x y = some r) :
    ieeePrimitiveValueBranchResult op x y r :=
  ieeePrimitiveValueBranchResult_special
    (ieeePrimitiveSpecialValueResult_quietNaNDefault? h)
theorem ieeePrimitiveValueBranchResult_invalid_default
    {op : BasicOp} {x y : IeeeValue}
    (hinput : ieeePrimitiveInvalidOperationInput op x y) :
    ieeePrimitiveValueBranchResult op x y
      ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveValueBranchResult_special
    (ieeePrimitiveSpecialValueResult_invalid_default hinput)
theorem ieeePrimitiveValueBranchResult_invalidOperationDefault?
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInvalidOperationResult? op x y = some r) :
    ieeePrimitiveValueBranchResult op x y r :=
  ieeePrimitiveValueBranchResult_special
    (ieeePrimitiveSpecialValueResult_invalidOperationDefault? h)
theorem ieeePrimitiveValueBranchResult_infinity
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInfinityPropagationResult op x y r) :
    ieeePrimitiveValueBranchResult op x y r :=
  ieeePrimitiveValueBranchResult_special
    (ieeePrimitiveSpecialValueResult_infinity h)
theorem ieeePrimitiveValueBranchResult_finiteOverInfinity
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveFiniteOverInfinityResult op x y r) :
    ieeePrimitiveValueBranchResult op x y r :=
  ieeePrimitiveValueBranchResult_special
    (ieeePrimitiveSpecialValueResult_finiteOverInfinity h)
theorem ieeePrimitiveValueBranchResult_finiteOverInfinityDefault?
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveFiniteOverInfinityResult? op x y = some r) :
    ieeePrimitiveValueBranchResult op x y r :=
  ieeePrimitiveValueBranchResult_special
    (ieeePrimitiveSpecialValueResult_finiteOverInfinityDefault? h)
theorem ieeePrimitiveValueBranchResult_mulSignedZero
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveMulSignedZeroResult x y r) :
    ieeePrimitiveValueBranchResult BasicOp.mul x y r :=
  ieeePrimitiveValueBranchResult_special
    (ieeePrimitiveSpecialValueResult_mulSignedZero h)
theorem ieeePrimitiveValueBranchResult_mulSignedZeroDefault?
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveMulSignedZeroResult? x y = some r) :
    ieeePrimitiveValueBranchResult BasicOp.mul x y r :=
  ieeePrimitiveValueBranchResult_special
    (ieeePrimitiveSpecialValueResult_mulSignedZeroDefault? h)
theorem ieeePrimitiveValueBranchResult_signedZeroOverFinite
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveSignedZeroOverFiniteResult x y r) :
    ieeePrimitiveValueBranchResult BasicOp.div x y r :=
  ieeePrimitiveValueBranchResult_special
    (ieeePrimitiveSpecialValueResult_signedZeroOverFinite h)
theorem ieeePrimitiveValueBranchResult_signedZeroOverFiniteDefault?
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveSignedZeroOverFiniteResult? x y = some r) :
    ieeePrimitiveValueBranchResult BasicOp.div x y r :=
  ieeePrimitiveValueBranchResult_special
    (ieeePrimitiveSpecialValueResult_signedZeroOverFiniteDefault? h)
theorem ieeePrimitiveValueBranchResult_addSubSignedZero
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubSignedZeroResult op x y r) :
    ieeePrimitiveValueBranchResult op x y r :=
  ieeePrimitiveValueBranchResult_special
    (ieeePrimitiveSpecialValueResult_addSubSignedZero h)
theorem ieeePrimitiveValueBranchResult_addSubSignedZeroDefault?
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubSignedZeroResult? op x y = some r) :
    ieeePrimitiveValueBranchResult op x y r :=
  ieeePrimitiveValueBranchResult_special
    (ieeePrimitiveSpecialValueResult_addSubSignedZeroDefault? h)
theorem ieeePrimitiveValueBranchResult_addSubFiniteSignedZero
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubFiniteSignedZeroResult op x y r) :
    ieeePrimitiveValueBranchResult op x y r :=
  ieeePrimitiveValueBranchResult_special
    (ieeePrimitiveSpecialValueResult_addSubFiniteSignedZero h)
theorem ieeePrimitiveValueBranchResult_addSubFiniteSignedZeroDefault?
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveAddSubFiniteSignedZeroResult? op x y = some r) :
    ieeePrimitiveValueBranchResult op x y r :=
  ieeePrimitiveValueBranchResult_special
    (ieeePrimitiveSpecialValueResult_addSubFiniteSignedZeroDefault? h)
/-- Concrete ordered selector for the currently modeled primitive
value-branch layer.  It selects an already modeled special-value branch first,
then the finite-nonzero-over-zero division-by-zero branch.  Ordinary finite
rounding and mode-aware exact-zero-sum signed-zero results remain in the
`FloatingPointFormat` value-dispatch layer. -/
noncomputable def ieeePrimitiveValueBranchResult?
    (op : BasicOp) (x y : IeeeValue) : Option IeeeOperationResult := by
  classical
  exact
    match ieeePrimitiveSpecialValueResult? op x y with
    | some r => some r
    | none =>
        match op with
        | BasicOp.div => ieeeDivisionByZeroDefaultResult? x y
        | _ => none
theorem ieeePrimitiveValueBranchResult?_quietNaNDefault?
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeQuietNaNPropagationResult? x y = some r) :
    ieeePrimitiveValueBranchResult? op x y = some r := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_quietNaNDefault? h]
theorem ieeePrimitiveValueBranchResult?_left_nan
    (op : BasicOp) (y : IeeeValue) :
    ieeePrimitiveValueBranchResult? op IeeeValue.nan y =
      some (IeeeOperationResult.valueNoFlags IeeeValue.nan) :=
  ieeePrimitiveValueBranchResult?_quietNaNDefault?
    (ieeeQuietNaNPropagationResult?_left_nan y)
theorem ieeePrimitiveValueBranchResult?_right_nan
    (op : BasicOp) (x : IeeeValue) :
    ieeePrimitiveValueBranchResult? op x IeeeValue.nan =
      some (IeeeOperationResult.valueNoFlags IeeeValue.nan) :=
  ieeePrimitiveValueBranchResult?_quietNaNDefault?
    (ieeeQuietNaNPropagationResult?_right_nan x)
theorem ieeePrimitiveValueBranchResult?_add_posInf_posInf :
    ieeePrimitiveValueBranchResult?
      BasicOp.add IeeeValue.posInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_add_posInf_posInf]
theorem ieeePrimitiveValueBranchResult?_sub_posInf_negInf :
    ieeePrimitiveValueBranchResult?
      BasicOp.sub IeeeValue.posInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_sub_posInf_negInf]
theorem ieeePrimitiveValueBranchResult?_mul_negInf_of_posInf_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_mul_negInf_of_posInf_finite_neg hy]
theorem ieeePrimitiveValueBranchResult?_div_posInf_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveValueBranchResult?
      BasicOp.div IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_div_posInf_finite_pos hy]
theorem ieeePrimitiveValueBranchResult?_infinityDefault?
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInfinityPropagationResult? op x y = some r) :
    ieeePrimitiveValueBranchResult? op x y = some r := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_infinityDefault? h]
theorem ieeePrimitiveValueBranchResult?_add_negInf_negInf :
    ieeePrimitiveValueBranchResult?
      BasicOp.add IeeeValue.negInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    ieeePrimitiveInfinityPropagationResult?_add_negInf_negInf
theorem ieeePrimitiveValueBranchResult?_add_posInf_finite
    (x : ℝ) :
    ieeePrimitiveValueBranchResult?
      BasicOp.add IeeeValue.posInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_add_posInf_finite x)
theorem ieeePrimitiveValueBranchResult?_add_finite_posInf
    (x : ℝ) :
    ieeePrimitiveValueBranchResult?
      BasicOp.add (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_add_finite_posInf x)
theorem ieeePrimitiveValueBranchResult?_add_negInf_finite
    (x : ℝ) :
    ieeePrimitiveValueBranchResult?
      BasicOp.add IeeeValue.negInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_add_negInf_finite x)
theorem ieeePrimitiveValueBranchResult?_add_finite_negInf
    (x : ℝ) :
    ieeePrimitiveValueBranchResult?
      BasicOp.add (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_add_finite_negInf x)
theorem ieeePrimitiveValueBranchResult?_sub_negInf_posInf :
    ieeePrimitiveValueBranchResult?
      BasicOp.sub IeeeValue.negInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    ieeePrimitiveInfinityPropagationResult?_sub_negInf_posInf
theorem ieeePrimitiveValueBranchResult?_sub_posInf_finite
    (x : ℝ) :
    ieeePrimitiveValueBranchResult?
      BasicOp.sub IeeeValue.posInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_sub_posInf_finite x)
theorem ieeePrimitiveValueBranchResult?_sub_finite_posInf
    (x : ℝ) :
    ieeePrimitiveValueBranchResult?
      BasicOp.sub (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_sub_finite_posInf x)
theorem ieeePrimitiveValueBranchResult?_sub_negInf_finite
    (x : ℝ) :
    ieeePrimitiveValueBranchResult?
      BasicOp.sub IeeeValue.negInf (IeeeValue.finite x) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_sub_negInf_finite x)
theorem ieeePrimitiveValueBranchResult?_sub_finite_negInf
    (x : ℝ) :
    ieeePrimitiveValueBranchResult?
      BasicOp.sub (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_sub_finite_negInf x)
theorem ieeePrimitiveValueBranchResult?_mul_posInf_posInf :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul IeeeValue.posInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    ieeePrimitiveInfinityPropagationResult?_mul_posInf_posInf
theorem ieeePrimitiveValueBranchResult?_mul_posInf_negInf :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul IeeeValue.posInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    ieeePrimitiveInfinityPropagationResult?_mul_posInf_negInf
theorem ieeePrimitiveValueBranchResult?_mul_negInf_posInf :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul IeeeValue.negInf IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    ieeePrimitiveInfinityPropagationResult?_mul_negInf_posInf
theorem ieeePrimitiveValueBranchResult?_mul_negInf_negInf :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul IeeeValue.negInf IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    ieeePrimitiveInfinityPropagationResult?_mul_negInf_negInf
theorem ieeePrimitiveValueBranchResult?_mul_posInf_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_mul_posInf_finite_pos hy)
theorem ieeePrimitiveValueBranchResult?_mul_negInf_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_mul_negInf_finite_pos hy)
theorem ieeePrimitiveValueBranchResult?_mul_posInf_of_negInf_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_mul_posInf_of_negInf_finite_neg hy)
theorem ieeePrimitiveValueBranchResult?_mul_finite_pos_posInf
    {x : ℝ} (hx : 0 < x) :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_mul_finite_pos_posInf hx)
theorem ieeePrimitiveValueBranchResult?_mul_negInf_of_finite_neg_posInf
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_mul_negInf_of_finite_neg_posInf hx)
theorem ieeePrimitiveValueBranchResult?_mul_finite_pos_negInf
    {x : ℝ} (hx : 0 < x) :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_mul_finite_pos_negInf hx)
theorem ieeePrimitiveValueBranchResult?_mul_posInf_of_finite_neg_negInf
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_mul_posInf_of_finite_neg_negInf hx)
theorem ieeePrimitiveValueBranchResult?_div_negInf_of_posInf_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.div IeeeValue.posInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_div_negInf_of_posInf_finite_neg hy)
theorem ieeePrimitiveValueBranchResult?_div_negInf_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveValueBranchResult?
      BasicOp.div IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_div_negInf_finite_pos hy)
theorem ieeePrimitiveValueBranchResult?_div_posInf_of_negInf_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.div IeeeValue.negInf (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posInf) :=
  ieeePrimitiveValueBranchResult?_infinityDefault?
    (ieeePrimitiveInfinityPropagationResult?_div_posInf_of_negInf_finite_neg hy)
theorem ieeePrimitiveValueBranchResult?_add_posInf_negInf :
    ieeePrimitiveValueBranchResult?
      BasicOp.add IeeeValue.posInf IeeeValue.negInf =
        some ieeeInvalidOperationDefaultResult := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_add_posInf_negInf]
theorem ieeePrimitiveValueBranchResult?_of_invalidOperationInput
    {op : BasicOp} {x y : IeeeValue}
    (hinput : ieeePrimitiveInvalidOperationInput op x y) :
    ieeePrimitiveValueBranchResult? op x y =
      some ieeeInvalidOperationDefaultResult := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_of_invalidOperationInput hinput]
theorem ieeePrimitiveValueBranchResult?_add_negInf_posInf :
    ieeePrimitiveValueBranchResult?
      BasicOp.add IeeeValue.negInf IeeeValue.posInf =
        some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveValueBranchResult?_of_invalidOperationInput
    ieeePrimitiveInvalidOperationInput_add_negInf_posInf
theorem ieeePrimitiveValueBranchResult?_sub_posInf_posInf :
    ieeePrimitiveValueBranchResult?
      BasicOp.sub IeeeValue.posInf IeeeValue.posInf =
        some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveValueBranchResult?_of_invalidOperationInput
    ieeePrimitiveInvalidOperationInput_sub_posInf_posInf
theorem ieeePrimitiveValueBranchResult?_sub_negInf_negInf :
    ieeePrimitiveValueBranchResult?
      BasicOp.sub IeeeValue.negInf IeeeValue.negInf =
        some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveValueBranchResult?_of_invalidOperationInput
    ieeePrimitiveInvalidOperationInput_sub_negInf_negInf
theorem ieeePrimitiveValueBranchResult?_mul_zero_inf
    {x y : IeeeValue} (hx : x.isZero) (hy : y.isInfinite) :
    ieeePrimitiveValueBranchResult? BasicOp.mul x y =
      some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveValueBranchResult?_of_invalidOperationInput
    (ieeePrimitiveInvalidOperationInput_mul_zero_inf hx hy)
theorem ieeePrimitiveValueBranchResult?_mul_inf_zero
    {x y : IeeeValue} (hx : x.isInfinite) (hy : y.isZero) :
    ieeePrimitiveValueBranchResult? BasicOp.mul x y =
      some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveValueBranchResult?_of_invalidOperationInput
    (ieeePrimitiveInvalidOperationInput_mul_inf_zero hx hy)
theorem ieeePrimitiveValueBranchResult?_div_zero_zero
    {x y : IeeeValue} (hx : x.isZero) (hy : y.isZero) :
    ieeePrimitiveValueBranchResult? BasicOp.div x y =
      some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveValueBranchResult?_of_invalidOperationInput
    (ieeePrimitiveInvalidOperationInput_div_zero_zero hx hy)
theorem ieeePrimitiveValueBranchResult?_div_inf_inf
    {x y : IeeeValue} (hx : x.isInfinite) (hy : y.isInfinite) :
    ieeePrimitiveValueBranchResult? BasicOp.div x y =
      some ieeeInvalidOperationDefaultResult :=
  ieeePrimitiveValueBranchResult?_of_invalidOperationInput
    (ieeePrimitiveInvalidOperationInput_div_inf_inf hx hy)
theorem ieeePrimitiveValueBranchResult?_div_posInf_posInf :
    ieeePrimitiveValueBranchResult?
      BasicOp.div IeeeValue.posInf IeeeValue.posInf =
        some ieeeInvalidOperationDefaultResult := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_div_posInf_posInf]
theorem ieeePrimitiveValueBranchResult?_div_finite_pos_posZero
    {x : ℝ} (hx : 0 < x) :
    ieeePrimitiveValueBranchResult?
      BasicOp.div (IeeeValue.finite x) IeeeValue.posZero =
        some (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) := by
  have hxne : x ≠ 0 := ne_of_gt hx
  simp [ieeePrimitiveValueBranchResult?, ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.isZero, IeeeValue.isInfinite,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveSignedZeroOverFiniteResult?, ieeeDivisionByZeroDefaultResult?,
    hx, hxne]
theorem ieeePrimitiveValueBranchResult?_div_finite_neg_posZero
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.div (IeeeValue.finite x) IeeeValue.posZero =
        some (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) := by
  have hxnot : ¬ 0 < x := not_lt.mpr (le_of_lt hx)
  have hxne : x ≠ 0 := ne_of_lt hx
  simp [ieeePrimitiveValueBranchResult?, ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.isZero, IeeeValue.isInfinite,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveSignedZeroOverFiniteResult?, ieeeDivisionByZeroDefaultResult?,
    hxnot, hx, hxne]
theorem ieeePrimitiveValueBranchResult?_div_finite_pos_negZero
    {x : ℝ} (hx : 0 < x) :
    ieeePrimitiveValueBranchResult?
      BasicOp.div (IeeeValue.finite x) IeeeValue.negZero =
        some (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) := by
  have hxne : x ≠ 0 := ne_of_gt hx
  simp [ieeePrimitiveValueBranchResult?, ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.isZero, IeeeValue.isInfinite,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveSignedZeroOverFiniteResult?, ieeeDivisionByZeroDefaultResult?,
    hx, hxne]
theorem ieeePrimitiveValueBranchResult?_div_finite_neg_negZero
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.div (IeeeValue.finite x) IeeeValue.negZero =
        some (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) := by
  have hxnot : ¬ 0 < x := not_lt.mpr (le_of_lt hx)
  have hxne : x ≠ 0 := ne_of_lt hx
  simp [ieeePrimitiveValueBranchResult?, ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.isZero, IeeeValue.isInfinite,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveSignedZeroOverFiniteResult?, ieeeDivisionByZeroDefaultResult?,
    hxnot, hx, hxne]
theorem ieeePrimitiveValueBranchResult?_div_finite_pos_finite_zero
    {x : ℝ} (hx : 0 < x) :
    ieeePrimitiveValueBranchResult?
      BasicOp.div (IeeeValue.finite x) (IeeeValue.finite 0) =
        some (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) := by
  have hxne : x ≠ 0 := ne_of_gt hx
  simp [ieeePrimitiveValueBranchResult?, ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.isZero, IeeeValue.isInfinite,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveSignedZeroOverFiniteResult?, ieeeDivisionByZeroDefaultResult?,
    hx, hxne]
theorem ieeePrimitiveValueBranchResult?_div_finite_neg_finite_zero
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.div (IeeeValue.finite x) (IeeeValue.finite 0) =
        some (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) := by
  have hxnot : ¬ 0 < x := not_lt.mpr (le_of_lt hx)
  have hxne : x ≠ 0 := ne_of_lt hx
  simp [ieeePrimitiveValueBranchResult?, ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.isZero, IeeeValue.isInfinite,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveSignedZeroOverFiniteResult?, ieeeDivisionByZeroDefaultResult?,
    hxnot, hx, hxne]
theorem ieeePrimitiveValueBranchResult?_div_finite_zero_posZero :
    ieeePrimitiveValueBranchResult?
      BasicOp.div (IeeeValue.finite 0) IeeeValue.posZero =
        some ieeeInvalidOperationDefaultResult := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_div_finite_zero_posZero]
theorem ieeePrimitiveValueBranchResult?_div_finite_zero_negZero :
    ieeePrimitiveValueBranchResult?
      BasicOp.div (IeeeValue.finite 0) IeeeValue.negZero =
        some ieeeInvalidOperationDefaultResult := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_div_finite_zero_negZero]
theorem ieeePrimitiveValueBranchResult?_div_finite_zero_finite_zero :
    ieeePrimitiveValueBranchResult?
      BasicOp.div (IeeeValue.finite 0) (IeeeValue.finite 0) =
        some ieeeInvalidOperationDefaultResult := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_div_finite_zero_finite_zero]
theorem ieeePrimitiveValueBranchResult?_div_posZero_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveValueBranchResult?
      BasicOp.div IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_div_posZero_finite_pos hy]
theorem ieeePrimitiveValueBranchResult?_div_posZero_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.div IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_div_posZero_finite_neg hy]
theorem ieeePrimitiveValueBranchResult?_div_negZero_finite_pos
    {y : ℝ} (hy : 0 < y) :
    ieeePrimitiveValueBranchResult?
      BasicOp.div IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_div_negZero_finite_pos hy]
theorem ieeePrimitiveValueBranchResult?_div_negZero_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.div IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_div_negZero_finite_neg hy]
theorem ieeePrimitiveValueBranchResult?_finiteOverInfinityDefault?
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveFiniteOverInfinityResult? op x y = some r) :
    ieeePrimitiveValueBranchResult? op x y = some r := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_finiteOverInfinityDefault? h]
theorem ieeePrimitiveValueBranchResult?_div_posZero_posInf :
    ieeePrimitiveValueBranchResult?
      BasicOp.div IeeeValue.posZero IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveValueBranchResult?_finiteOverInfinityDefault?
    ieeePrimitiveFiniteOverInfinityResult?_posZero_posInf
theorem ieeePrimitiveValueBranchResult?_div_negZero_of_posZero_negInf :
    ieeePrimitiveValueBranchResult?
      BasicOp.div IeeeValue.posZero IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveValueBranchResult?_finiteOverInfinityDefault?
    ieeePrimitiveFiniteOverInfinityResult?_negZero_of_posZero_negInf
theorem ieeePrimitiveValueBranchResult?_div_negZero_posInf :
    ieeePrimitiveValueBranchResult?
      BasicOp.div IeeeValue.negZero IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveValueBranchResult?_finiteOverInfinityDefault?
    ieeePrimitiveFiniteOverInfinityResult?_negZero_posInf
theorem ieeePrimitiveValueBranchResult?_div_posZero_of_negZero_negInf :
    ieeePrimitiveValueBranchResult?
      BasicOp.div IeeeValue.negZero IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveValueBranchResult?_finiteOverInfinityDefault?
    ieeePrimitiveFiniteOverInfinityResult?_posZero_of_negZero_negInf
theorem ieeePrimitiveValueBranchResult?_div_finite_nonneg_posInf
    {x : ℝ} (hx : 0 ≤ x) :
    ieeePrimitiveValueBranchResult?
      BasicOp.div (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveValueBranchResult?_finiteOverInfinityDefault?
    (ieeePrimitiveFiniteOverInfinityResult?_finite_nonneg_posInf hx)
theorem ieeePrimitiveValueBranchResult?_div_negZero_of_finite_neg_posInf
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.div (IeeeValue.finite x) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveValueBranchResult?_finiteOverInfinityDefault?
    (ieeePrimitiveFiniteOverInfinityResult?_negZero_of_finite_neg_posInf hx)
theorem ieeePrimitiveValueBranchResult?_div_finite_nonneg_negInf
    {x : ℝ} (hx : 0 ≤ x) :
    ieeePrimitiveValueBranchResult?
      BasicOp.div (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveValueBranchResult?_finiteOverInfinityDefault?
    (ieeePrimitiveFiniteOverInfinityResult?_finite_nonneg_negInf hx)
theorem ieeePrimitiveValueBranchResult?_div_posZero_of_finite_neg_negInf
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.div (IeeeValue.finite x) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveValueBranchResult?_finiteOverInfinityDefault?
    (ieeePrimitiveFiniteOverInfinityResult?_posZero_of_finite_neg_negInf hx)
theorem ieeePrimitiveValueBranchResult?_div_finite_zero_posInf :
    ieeePrimitiveValueBranchResult?
      BasicOp.div (IeeeValue.finite 0) IeeeValue.posInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveValueBranchResult?_finiteOverInfinityDefault?
    ieeePrimitiveFiniteOverInfinityResult?_finite_zero_posInf
theorem ieeePrimitiveValueBranchResult?_div_finite_zero_negInf :
    ieeePrimitiveValueBranchResult?
      BasicOp.div (IeeeValue.finite 0) IeeeValue.negInf =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveValueBranchResult?_finiteOverInfinityDefault?
    ieeePrimitiveFiniteOverInfinityResult?_finite_zero_negInf
theorem ieeePrimitiveValueBranchResult?_mulSignedZeroDefault?
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveMulSignedZeroResult? x y = some r) :
    ieeePrimitiveValueBranchResult? BasicOp.mul x y = some r := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_mulSignedZeroDefault? h]
theorem ieeePrimitiveValueBranchResult?_mul_posZero_posZero :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul IeeeValue.posZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveValueBranchResult?_mulSignedZeroDefault?
    ieeePrimitiveMulSignedZeroResult?_posZero_posZero
theorem ieeePrimitiveValueBranchResult?_mul_posZero_negZero :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul IeeeValue.posZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveValueBranchResult?_mulSignedZeroDefault?
    ieeePrimitiveMulSignedZeroResult?_posZero_negZero
theorem ieeePrimitiveValueBranchResult?_mul_negZero_posZero :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul IeeeValue.negZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveValueBranchResult?_mulSignedZeroDefault?
    ieeePrimitiveMulSignedZeroResult?_negZero_posZero
theorem ieeePrimitiveValueBranchResult?_mul_negZero_negZero :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul IeeeValue.negZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveValueBranchResult?_mulSignedZeroDefault?
    ieeePrimitiveMulSignedZeroResult?_negZero_negZero
theorem ieeePrimitiveValueBranchResult?_mul_posZero_finite_nonneg
    {y : ℝ} (hy : 0 ≤ y) :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveValueBranchResult?_mulSignedZeroDefault?
    (ieeePrimitiveMulSignedZeroResult?_posZero_finite_nonneg hy)
theorem ieeePrimitiveValueBranchResult?_mul_negZero_of_posZero_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveValueBranchResult?_mulSignedZeroDefault?
    (ieeePrimitiveMulSignedZeroResult?_negZero_of_posZero_finite_neg hy)
theorem ieeePrimitiveValueBranchResult?_mul_finite_nonneg_posZero
    {x : ℝ} (hx : 0 ≤ x) :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveValueBranchResult?_mulSignedZeroDefault?
    (ieeePrimitiveMulSignedZeroResult?_finite_nonneg_posZero hx)
theorem ieeePrimitiveValueBranchResult?_mul_negZero_of_finite_neg_posZero
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveValueBranchResult?_mulSignedZeroDefault?
    (ieeePrimitiveMulSignedZeroResult?_negZero_of_finite_neg_posZero hx)
theorem ieeePrimitiveValueBranchResult?_mul_negZero_finite_nonneg
    {y : ℝ} (hy : 0 ≤ y) :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveValueBranchResult?_mulSignedZeroDefault?
    (ieeePrimitiveMulSignedZeroResult?_negZero_finite_nonneg hy)
theorem ieeePrimitiveValueBranchResult?_mul_posZero_of_negZero_finite_neg
    {y : ℝ} (hy : y < 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveValueBranchResult?_mulSignedZeroDefault?
    (ieeePrimitiveMulSignedZeroResult?_posZero_of_negZero_finite_neg hy)
theorem ieeePrimitiveValueBranchResult?_mul_finite_nonneg_negZero
    {x : ℝ} (hx : 0 ≤ x) :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) :=
  ieeePrimitiveValueBranchResult?_mulSignedZeroDefault?
    (ieeePrimitiveMulSignedZeroResult?_finite_nonneg_negZero hx)
theorem ieeePrimitiveValueBranchResult?_mul_posZero_of_finite_neg_negZero
    {x : ℝ} (hx : x < 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.mul (IeeeValue.finite x) IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) :=
  ieeePrimitiveValueBranchResult?_mulSignedZeroDefault?
    (ieeePrimitiveMulSignedZeroResult?_posZero_of_finite_neg_negZero hx)
theorem ieeePrimitiveValueBranchResult?_add_posZero_posZero :
    ieeePrimitiveValueBranchResult?
      BasicOp.add IeeeValue.posZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simp [ieeePrimitiveValueBranchResult?, ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.oppositeSignedInfinities,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveAddSubSignedZeroResult?]
theorem ieeePrimitiveValueBranchResult?_add_negZero_negZero :
    ieeePrimitiveValueBranchResult?
      BasicOp.add IeeeValue.negZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simp [ieeePrimitiveValueBranchResult?, ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.oppositeSignedInfinities,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveAddSubSignedZeroResult?]
theorem ieeePrimitiveValueBranchResult?_sub_posZero_negZero :
    ieeePrimitiveValueBranchResult?
      BasicOp.sub IeeeValue.posZero IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  simp [ieeePrimitiveValueBranchResult?, ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.sameSignedInfinities,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveAddSubSignedZeroResult?]
theorem ieeePrimitiveValueBranchResult?_sub_negZero_posZero :
    ieeePrimitiveValueBranchResult?
      BasicOp.sub IeeeValue.negZero IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  simp [ieeePrimitiveValueBranchResult?, ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.sameSignedInfinities,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveAddSubSignedZeroResult?]
theorem ieeePrimitiveValueBranchResult?_add_finite_posZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.add (IeeeValue.finite x) IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_add_finite_posZero hx]
theorem ieeePrimitiveValueBranchResult?_add_finite_negZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.add (IeeeValue.finite x) IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_add_finite_negZero hx]
theorem ieeePrimitiveValueBranchResult?_add_posZero_finite
    {y : ℝ} (hy : y ≠ 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.add IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite y)) := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_add_posZero_finite hy]
theorem ieeePrimitiveValueBranchResult?_add_negZero_finite
    {y : ℝ} (hy : y ≠ 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.add IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite y)) := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_add_negZero_finite hy]
theorem ieeePrimitiveValueBranchResult?_sub_finite_posZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.sub (IeeeValue.finite x) IeeeValue.posZero =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_sub_finite_posZero hx]
theorem ieeePrimitiveValueBranchResult?_sub_finite_negZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.sub (IeeeValue.finite x) IeeeValue.negZero =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite x)) := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_sub_finite_negZero hx]
theorem ieeePrimitiveValueBranchResult?_sub_posZero_finite
    {y : ℝ} (hy : y ≠ 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.sub IeeeValue.posZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite (-y))) := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_sub_posZero_finite hy]
theorem ieeePrimitiveValueBranchResult?_sub_negZero_finite
    {y : ℝ} (hy : y ≠ 0) :
    ieeePrimitiveValueBranchResult?
      BasicOp.sub IeeeValue.negZero (IeeeValue.finite y) =
        some (IeeeOperationResult.valueNoFlags (IeeeValue.finite (-y))) := by
  simp [ieeePrimitiveValueBranchResult?,
    ieeePrimitiveSpecialValueResult?_sub_negZero_finite hy]
theorem ieeePrimitiveValueBranchResult?_none_add_posZero_negZero :
    ieeePrimitiveValueBranchResult?
      BasicOp.add IeeeValue.posZero IeeeValue.negZero = none := by
  simp [ieeePrimitiveValueBranchResult?, ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.oppositeSignedInfinities,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveAddSubSignedZeroResult?, ieeePrimitiveAddSubFiniteSignedZeroResult?]
theorem ieeePrimitiveValueBranchResult?_none_add_negZero_posZero :
    ieeePrimitiveValueBranchResult?
      BasicOp.add IeeeValue.negZero IeeeValue.posZero = none := by
  simp [ieeePrimitiveValueBranchResult?, ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.oppositeSignedInfinities,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveAddSubSignedZeroResult?, ieeePrimitiveAddSubFiniteSignedZeroResult?]
theorem ieeePrimitiveValueBranchResult?_none_sub_posZero_posZero :
    ieeePrimitiveValueBranchResult?
      BasicOp.sub IeeeValue.posZero IeeeValue.posZero = none := by
  simp [ieeePrimitiveValueBranchResult?, ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.sameSignedInfinities,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveAddSubSignedZeroResult?, ieeePrimitiveAddSubFiniteSignedZeroResult?]
theorem ieeePrimitiveValueBranchResult?_none_sub_negZero_negZero :
    ieeePrimitiveValueBranchResult?
      BasicOp.sub IeeeValue.negZero IeeeValue.negZero = none := by
  simp [ieeePrimitiveValueBranchResult?, ieeePrimitiveSpecialValueResult?,
    ieeeQuietNaNPropagationResult?, ieeePrimitiveInvalidOperationResult?,
    ieeePrimitiveInvalidOperationInput, IeeeValue.sameSignedInfinities,
    ieeePrimitiveInfinityPropagationResult?, ieeePrimitiveFiniteOverInfinityResult?,
    ieeePrimitiveAddSubSignedZeroResult?, ieeePrimitiveAddSubFiniteSignedZeroResult?]

end

end NumStability
