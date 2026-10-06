import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic.IeeeValue

namespace NumStability

/-!
# Format

Extracted without change from FloatingPointArithmetic.
-/

noncomputable section

/-- Higham Chapter 2 finite floating-point format parameters.  We use inclusive
exponent endpoints, matching the displayed source line `emin <= e <= emax`. -/
structure FloatingPointFormat where
  /-- Base, or radix. -/
  beta : ℕ
  /-- Precision, in base-`beta` digits. -/
  t : ℕ
  /-- Minimum normalized exponent. -/
  emin : ℤ
  /-- Maximum normalized exponent. -/
  emax : ℤ
  beta_ge_two : 2 ≤ beta
  t_pos : 0 < t
  emin_le_emax : emin ≤ emax
namespace FloatingPointFormat

/-- The base as a real number. -/
def betaR (fmt : FloatingPointFormat) : ℝ :=
  (fmt.beta : ℝ)
/-- Higham's machine epsilon: the gap from `1.0` to the next larger normalized
number, `beta^(1-t)`. -/
def machineEpsilon (fmt : FloatingPointFormat) : ℝ :=
  fmt.betaR ^ (1 - (fmt.t : ℤ))
/-- Higham's unit roundoff `u = (1/2) beta^(1-t)`. -/
def unitRoundoff (fmt : FloatingPointFormat) : ℝ :=
  (1 / 2 : ℝ) * fmt.machineEpsilon
/-- Higham's unit in the last place for a normalized value with exponent `e`:
`ulp(+- beta^e * .d_1...d_t) = beta^(e-t)`. -/
def ulpAtExponent (fmt : FloatingPointFormat) (e : ℤ) : ℝ :=
  fmt.betaR ^ (e - (fmt.t : ℤ))
/-- Higham's IEEE single-precision parameter tuple: `beta = 2`, `t = 24`,
`emin = -125`, `emax = 128`.  This records the finite-format parameters only;
it is not a full IEEE semantics with signed zeros, infinities, NaNs, exception
flags, or a concrete tie rule. -/
def ieeeSingleFormat : FloatingPointFormat where
  beta := 2
  t := 24
  emin := -125
  emax := 128
  beta_ge_two := by norm_num
  t_pos := by norm_num
  emin_le_emax := by norm_num
/-- Higham's IEEE double-precision parameter tuple: `beta = 2`, `t = 53`,
`emin = -1021`, `emax = 1024`.  This records the finite-format parameters only;
it is not a full IEEE semantics with signed zeros, infinities, NaNs, exception
flags, or a concrete tie rule. -/
def ieeeDoubleFormat : FloatingPointFormat where
  beta := 2
  t := 53
  emin := -1021
  emax := 1024
  beta_ge_two := by norm_num
  t_pos := by norm_num
  emin_le_emax := by norm_num
theorem ieeeSingleFormat_params :
    ieeeSingleFormat.beta = 2 ∧ ieeeSingleFormat.t = 24 ∧
      ieeeSingleFormat.emin = -125 ∧ ieeeSingleFormat.emax = 128 := by
  norm_num [ieeeSingleFormat]
theorem ieeeDoubleFormat_params :
    ieeeDoubleFormat.beta = 2 ∧ ieeeDoubleFormat.t = 53 ∧
      ieeeDoubleFormat.emin = -1021 ∧ ieeeDoubleFormat.emax = 1024 := by
  norm_num [ieeeDoubleFormat]
theorem ieeeSingleFormat_machineEpsilon :
    ieeeSingleFormat.machineEpsilon = (2 : ℝ) ^ (-23 : ℤ) := by
  norm_num [ieeeSingleFormat, machineEpsilon, betaR]
theorem ieeeSingleFormat_unitRoundoff :
    ieeeSingleFormat.unitRoundoff = (2 : ℝ) ^ (-24 : ℤ) := by
  rw [unitRoundoff, ieeeSingleFormat_machineEpsilon]
  norm_num [zpow_neg]
theorem ieeeDoubleFormat_machineEpsilon :
    ieeeDoubleFormat.machineEpsilon = (2 : ℝ) ^ (-52 : ℤ) := by
  norm_num [ieeeDoubleFormat, machineEpsilon, betaR]
theorem ieeeDoubleFormat_unitRoundoff :
    ieeeDoubleFormat.unitRoundoff = (2 : ℝ) ^ (-53 : ℤ) := by
  rw [unitRoundoff, ieeeDoubleFormat_machineEpsilon]
  norm_num [zpow_neg]
theorem ieeeSingleFormat_ulpAtExponent (e : ℤ) :
    ieeeSingleFormat.ulpAtExponent e = (2 : ℝ) ^ (e - 24) := by
  norm_num [ulpAtExponent, ieeeSingleFormat, betaR]
theorem ieeeDoubleFormat_ulpAtExponent (e : ℤ) :
    ieeeDoubleFormat.ulpAtExponent e = (2 : ℝ) ^ (e - 53) := by
  norm_num [ulpAtExponent, ieeeDoubleFormat, betaR]
/-- The smallest positive normalized magnitude, `beta^(emin-1)`. -/
def minNormalMagnitude (fmt : FloatingPointFormat) : ℝ :=
  fmt.betaR ^ (fmt.emin - 1)
/-- The smallest positive subnormal magnitude, `beta^(emin-t)`. -/
def minSubnormalMagnitude (fmt : FloatingPointFormat) : ℝ :=
  fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))
/-- The largest finite normalized magnitude,
`beta^emax * (1 - beta^(-t))`. -/
def maxFiniteMagnitude (fmt : FloatingPointFormat) : ℝ :=
  fmt.betaR ^ fmt.emax * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))
/-- Source-facing finite normal range, excluding the subnormal/zero region but
including both finite normalized endpoints by magnitude. -/
def finiteNormalRange (fmt : FloatingPointFormat) (x : ℝ) : Prop :=
  fmt.minNormalMagnitude ≤ |x| ∧ |x| ≤ fmt.maxFiniteMagnitude
/-- Source-facing underflow range: magnitudes below the smallest positive
normalized value.  This includes zero and subnormal magnitudes; arithmetic
semantics and exception behavior are modeled separately. -/
def finiteUnderflowRange (fmt : FloatingPointFormat) (x : ℝ) : Prop :=
  |x| < fmt.minNormalMagnitude
/-- Source-facing overflow range: magnitudes above the largest finite normalized
value.  This is a range predicate, not yet an operational overflow semantics. -/
def finiteOverflowRange (fmt : FloatingPointFormat) (x : ℝ) : Prop :=
  fmt.maxFiniteMagnitude < |x|
theorem finiteNormalRange_neg_iff (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteNormalRange (-x) ↔ fmt.finiteNormalRange x := by
  simp [finiteNormalRange]
theorem finiteUnderflowRange_neg_iff (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteUnderflowRange (-x) ↔ fmt.finiteUnderflowRange x := by
  simp [finiteUnderflowRange]
theorem finiteOverflowRange_neg_iff (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteOverflowRange (-x) ↔ fmt.finiteOverflowRange x := by
  simp [finiteOverflowRange]
/-- A finite-normal value is not in the source-facing underflow range. -/
theorem finiteNormalRange_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ} (hx : fmt.finiteNormalRange x) :
    ¬ fmt.finiteUnderflowRange x :=
  not_lt_of_ge hx.1
/-- A finite-normal value is not in the source-facing overflow range. -/
theorem finiteNormalRange_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ} (hx : fmt.finiteNormalRange x) :
    ¬ fmt.finiteOverflowRange x :=
  not_lt_of_ge hx.2
/-- IEEE-facing default overflow value for a finite exact real result that is
outside the finite range.  Nearest/even overflows to the signed infinity; the
directed modes choose either the signed infinity or the signed largest finite
endpoint according to the direction.  This is only the value component of the
overflow semantics; flags are recorded by `ieeeOverflowResult`. -/
def ieeeOverflowValue
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    IeeeValue :=
  if x < 0 then
    match mode with
    | IeeeRoundingMode.nearestEven => IeeeValue.negInf
    | IeeeRoundingMode.towardZero => IeeeValue.finite (-fmt.maxFiniteMagnitude)
    | IeeeRoundingMode.towardPositive =>
        IeeeValue.finite (-fmt.maxFiniteMagnitude)
    | IeeeRoundingMode.towardNegative => IeeeValue.negInf
  else
    match mode with
    | IeeeRoundingMode.nearestEven => IeeeValue.posInf
    | IeeeRoundingMode.towardZero => IeeeValue.finite fmt.maxFiniteMagnitude
    | IeeeRoundingMode.towardPositive => IeeeValue.posInf
    | IeeeRoundingMode.towardNegative =>
        IeeeValue.finite fmt.maxFiniteMagnitude
/-- First IEEE-facing overflow-result predicate for Chapter 2: the exact real
input is in the source-facing overflow range, the value is the mode-dependent
overflow value, and the overflow and inexact flags are set.  This is a semantic
predicate, not yet a full arithmetic operation. -/
def ieeeOverflowResult
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ)
    (r : IeeeOperationResult) : Prop :=
  fmt.finiteOverflowRange x ∧
    r.value = fmt.ieeeOverflowValue mode x ∧
    r.hasFlag IeeeExceptionFlag.overflow ∧
    r.hasFlag IeeeExceptionFlag.inexact
/-- Default IEEE-facing overflow result for an exact finite real result outside
the finite range.  It records the mode-dependent overflow value and sets
exactly the overflow and inexact flags. -/
def ieeeOverflowDefaultResult
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    IeeeOperationResult where
  value := fmt.ieeeOverflowValue mode x
  flag := fun flag =>
    flag = IeeeExceptionFlag.overflow ∨ flag = IeeeExceptionFlag.inexact
theorem ieeeOverflowDefaultResult_value
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    (fmt.ieeeOverflowDefaultResult mode x).value =
      fmt.ieeeOverflowValue mode x := rfl
theorem ieeeOverflowDefaultResult_hasFlag_iff
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ)
    (flag : IeeeExceptionFlag) :
    (fmt.ieeeOverflowDefaultResult mode x).hasFlag flag ↔
      flag = IeeeExceptionFlag.overflow ∨
        flag = IeeeExceptionFlag.inexact := by
  rfl
theorem ieeeOverflowDefaultResult_hasOverflowFlag
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    (fmt.ieeeOverflowDefaultResult mode x).hasFlag
      IeeeExceptionFlag.overflow := by
  simp [ieeeOverflowDefaultResult, IeeeOperationResult.hasFlag]
theorem ieeeOverflowDefaultResult_hasInexactFlag
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    (fmt.ieeeOverflowDefaultResult mode x).hasFlag
      IeeeExceptionFlag.inexact := by
  simp [ieeeOverflowDefaultResult, IeeeOperationResult.hasFlag]
theorem ieeeOverflowDefaultResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx : fmt.finiteOverflowRange x) :
    fmt.ieeeOverflowResult mode x
      (fmt.ieeeOverflowDefaultResult mode x) := by
  exact ⟨hx, rfl,
    fmt.ieeeOverflowDefaultResult_hasOverflowFlag mode x,
    fmt.ieeeOverflowDefaultResult_hasInexactFlag mode x⟩
theorem ieeeOverflowValue_nearestEven_of_neg
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    fmt.ieeeOverflowValue IeeeRoundingMode.nearestEven x =
      IeeeValue.negInf := by
  simp [ieeeOverflowValue, hx]
theorem ieeeOverflowValue_nearestEven_of_nonneg
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 ≤ x) :
    fmt.ieeeOverflowValue IeeeRoundingMode.nearestEven x =
      IeeeValue.posInf := by
  have hnot : ¬ x < 0 := not_lt.mpr hx
  simp [ieeeOverflowValue, hnot]
theorem ieeeOverflowValue_towardZero_of_neg
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    fmt.ieeeOverflowValue IeeeRoundingMode.towardZero x =
      IeeeValue.finite (-fmt.maxFiniteMagnitude) := by
  simp [ieeeOverflowValue, hx]
theorem ieeeOverflowValue_towardZero_of_nonneg
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 ≤ x) :
    fmt.ieeeOverflowValue IeeeRoundingMode.towardZero x =
      IeeeValue.finite fmt.maxFiniteMagnitude := by
  have hnot : ¬ x < 0 := not_lt.mpr hx
  simp [ieeeOverflowValue, hnot]
theorem ieeeOverflowValue_towardPositive_of_neg
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    fmt.ieeeOverflowValue IeeeRoundingMode.towardPositive x =
      IeeeValue.finite (-fmt.maxFiniteMagnitude) := by
  simp [ieeeOverflowValue, hx]
theorem ieeeOverflowValue_towardPositive_of_nonneg
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 ≤ x) :
    fmt.ieeeOverflowValue IeeeRoundingMode.towardPositive x =
      IeeeValue.posInf := by
  have hnot : ¬ x < 0 := not_lt.mpr hx
  simp [ieeeOverflowValue, hnot]
theorem ieeeOverflowValue_towardNegative_of_neg
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    fmt.ieeeOverflowValue IeeeRoundingMode.towardNegative x =
      IeeeValue.negInf := by
  simp [ieeeOverflowValue, hx]
theorem ieeeOverflowValue_towardNegative_of_nonneg
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 ≤ x) :
    fmt.ieeeOverflowValue IeeeRoundingMode.towardNegative x =
      IeeeValue.finite fmt.maxFiniteMagnitude := by
  have hnot : ¬ x < 0 := not_lt.mpr hx
  simp [ieeeOverflowValue, hnot]
theorem ieeeOverflowResult_finiteOverflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    {r : IeeeOperationResult} (h : fmt.ieeeOverflowResult mode x r) :
    fmt.finiteOverflowRange x :=
  h.1
theorem ieeeOverflowResult_value
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    {r : IeeeOperationResult} (h : fmt.ieeeOverflowResult mode x r) :
    r.value = fmt.ieeeOverflowValue mode x :=
  h.2.1
theorem ieeeOverflowResult_hasOverflowFlag
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    {r : IeeeOperationResult} (h : fmt.ieeeOverflowResult mode x r) :
    r.hasFlag IeeeExceptionFlag.overflow :=
  h.2.2.1
theorem ieeeOverflowResult_hasInexactFlag
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    {r : IeeeOperationResult} (h : fmt.ieeeOverflowResult mode x r) :
    r.hasFlag IeeeExceptionFlag.inexact :=
  h.2.2.2
theorem ieeeOverflowResult_not_noFlags
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    {r : IeeeOperationResult} (h : fmt.ieeeOverflowResult mode x r) :
    ¬ r.noFlags := by
  intro hno
  exact hno IeeeExceptionFlag.overflow
    (fmt.ieeeOverflowResult_hasOverflowFlag h)
theorem ieeeOverflowResult_not_finiteNoFlags
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x y : ℝ} :
    ¬ fmt.ieeeOverflowResult mode x (IeeeOperationResult.finiteNoFlags y) := by
  intro h
  exact IeeeOperationResult.finiteNoFlags_not_hasFlag y
    IeeeExceptionFlag.overflow (fmt.ieeeOverflowResult_hasOverflowFlag h)
/-- Mantissas in the finite `t`-digit range `0 <= m <= beta^t - 1`, represented
over natural numbers as `m < beta^t`. -/
def mantissaInRange (fmt : FloatingPointFormat) (m : ℕ) : Prop :=
  m < fmt.beta ^ fmt.t
/-- The smallest normalized mantissa, `beta^(t-1)`. -/
def minNormalMantissa (fmt : FloatingPointFormat) : ℕ :=
  fmt.beta ^ (fmt.t - 1)
/-- The largest normalized mantissa, `beta^t - 1`. -/
def maxNormalMantissa (fmt : FloatingPointFormat) : ℕ :=
  fmt.beta ^ fmt.t - 1
/-- Higham's normalized nonzero mantissa condition:
`beta^(t-1) <= m <= beta^t - 1`. -/
def normalizedMantissa (fmt : FloatingPointFormat) (m : ℕ) : Prop :=
  fmt.minNormalMantissa ≤ m ∧ fmt.mantissaInRange m
/-- Higham's subnormal nonzero mantissa condition:
`0 < m < beta^(t-1)`. -/
def subnormalMantissa (fmt : FloatingPointFormat) (m : ℕ) : Prop :=
  0 < m ∧ m < fmt.minNormalMantissa
/-- Inclusive exponent range for normalized numbers. -/
def exponentInRange (fmt : FloatingPointFormat) (e : ℤ) : Prop :=
  fmt.emin ≤ e ∧ e ≤ fmt.emax
/-- Sign choice in the `+- m beta^(e-t)` representation. -/
def signValue (_fmt : FloatingPointFormat) (negative : Bool) : ℝ :=
  if negative then -1 else 1
/-- Higham equation (2.1), `+- m * beta^(e-t)`.  The mantissa and exponent
predicates are kept separate so the same value expression can be used for the
bounded system `F` and the unbounded-exponent system `G`. -/
def normalizedValue (fmt : FloatingPointFormat) (negative : Bool) (m : ℕ)
    (e : ℤ) : ℝ :=
  fmt.signValue negative * (m : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))
/-- Integer coefficient carrying the sign of a normalized mantissa.  This is
the common-lattice form used to reconstruct exact subtraction results from
their operand representations, without assuming a representation of the
result itself. -/
def signedMantissaCoeff
    (_fmt : FloatingPointFormat) (negative : Bool) (m : ℕ) : ℤ :=
  if negative then -(m : ℤ) else (m : ℤ)
theorem normalizedValue_eq_signedMantissaCoeff
    (fmt : FloatingPointFormat) (negative : Bool) (m : ℕ) (e : ℤ) :
    fmt.normalizedValue negative m e =
      (fmt.signedMantissaCoeff negative m : ℝ) *
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  cases negative <;>
    simp [normalizedValue, signValue, signedMantissaCoeff]
/-- Subnormal value form `+- m * beta^(emin-t)`. -/
def subnormalValue (fmt : FloatingPointFormat) (negative : Bool) (m : ℕ) : ℝ :=
  fmt.signValue negative * (m : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))
/-- The normalized finite system `F`, excluding zero and subnormals. -/
def normalizedSystem (fmt : FloatingPointFormat) (y : ℝ) : Prop :=
  ∃ negative m e,
    fmt.normalizedMantissa m ∧
    fmt.exponentInRange e ∧
    y = fmt.normalizedValue negative m e
/-- A normalized finite representation of a value with an explicit exponent.
This is the local version of Higham's `e(x)` surface used in the guard-digit
theorems: the exponent is carried as data rather than chosen by a function. -/
def normalizedExponentRepresentation
    (fmt : FloatingPointFormat) (y : ℝ) (e : ℤ) : Prop :=
  ∃ negative m,
    fmt.normalizedMantissa m ∧
    fmt.exponentInRange e ∧
    y = fmt.normalizedValue negative m e
theorem normalizedExponentRepresentation_normalizedSystem
    {fmt : FloatingPointFormat} {y : ℝ} {e : ℤ}
    (h : fmt.normalizedExponentRepresentation y e) :
    fmt.normalizedSystem y := by
  rcases h with ⟨negative, m, hm, he, hy⟩
  exact ⟨negative, m, e, hm, he, hy⟩
theorem normalizedSystem_exists_normalizedExponentRepresentation
    {fmt : FloatingPointFormat} {y : ℝ}
    (h : fmt.normalizedSystem y) :
    ∃ e : ℤ, fmt.normalizedExponentRepresentation y e := by
  rcases h with ⟨negative, m, e, hm, he, hy⟩
  exact ⟨e, negative, m, hm, he, hy⟩
theorem normalizedSystem_iff_exists_normalizedExponentRepresentation
    {fmt : FloatingPointFormat} {y : ℝ} :
    fmt.normalizedSystem y ↔
      ∃ e : ℤ, fmt.normalizedExponentRepresentation y e := by
  constructor
  · exact normalizedSystem_exists_normalizedExponentRepresentation
  · intro h
    rcases h with ⟨e, he⟩
    exact fmt.normalizedExponentRepresentation_normalizedSystem he
/-- Higham's unbounded-exponent set `G`, with the same normalized mantissas but
without the finite exponent-range restriction. -/
def unboundedNormalizedSystem (fmt : FloatingPointFormat) (y : ℝ) : Prop :=
  ∃ negative m e,
    fmt.normalizedMantissa m ∧
    y = fmt.normalizedValue negative m e
/-- The subnormal part of the finite system. -/
def subnormalSystem (fmt : FloatingPointFormat) (y : ℝ) : Prop :=
  ∃ negative m,
    fmt.subnormalMantissa m ∧
    y = fmt.subnormalValue negative m
/-- The finite floating-point values: zero, normalized numbers, and subnormals. -/
def finiteSystem (fmt : FloatingPointFormat) (y : ℝ) : Prop :=
  y = 0 ∨ fmt.normalizedSystem y ∨ fmt.subnormalSystem y
/-- A finite floating-point value whose nonzero representation has a supplied
sign bit.  Zero is allowed independently of sign. -/
def finiteSystemWithSign (fmt : FloatingPointFormat) (negative : Bool)
    (y : ℝ) : Prop :=
  y = 0 ∨
    (∃ (m : ℕ) (e : ℤ),
      fmt.normalizedMantissa m ∧
      fmt.exponentInRange e ∧
      y = fmt.normalizedValue negative m e) ∨
    (∃ m : ℕ, fmt.subnormalMantissa m ∧
      y = fmt.subnormalValue negative m)
/-- A finite value with a supplied nonzero sign is, in particular, finite. -/
theorem finiteSystem_of_finiteSystemWithSign
    {fmt : FloatingPointFormat} {negative : Bool} {y : ℝ}
    (hy : fmt.finiteSystemWithSign negative y) :
    fmt.finiteSystem y := by
  rcases hy with hy0 | hynz
  · exact Or.inl hy0
  · rcases hynz with hynorm | hysub
    · rcases hynorm with ⟨m, e, hm, he, rfl⟩
      exact Or.inr (Or.inl ⟨negative, m, e, hm, he, rfl⟩)
    · rcases hysub with ⟨m, hm, rfl⟩
      exact Or.inr (Or.inr ⟨negative, m, hm, rfl⟩)
/-- Every bounded normalized finite value is also a member of Higham's
unbounded normalized system `G`. -/
theorem normalizedSystem_unboundedNormalizedSystem
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.normalizedSystem y) :
    fmt.unboundedNormalizedSystem y := by
  rcases hy with ⟨negative, m, e, hm, _he, hy⟩
  exact ⟨negative, m, e, hm, hy⟩
/-- A base-`beta`, length-`t` digit string, written in Higham's big-endian
order `d_1, ..., d_t`. -/
def digitStringInRange (fmt : FloatingPointFormat) (digits : List ℕ) : Prop :=
  digits.length = fmt.t ∧ ∀ d ∈ digits, d < fmt.beta
/-- A normalized base-`beta`, length-`t` digit string: all digits are in range
and the most significant digit is nonzero. -/
def normalizedDigitString (fmt : FloatingPointFormat) (digits : List ℕ) : Prop :=
  fmt.digitStringInRange digits ∧ ∃ d rest, digits = d :: rest ∧ 0 < d
/-- The integer mantissa encoded by a big-endian digit string.  Mathlib's
`Nat.ofDigits` uses little-endian order, hence the reverse. -/
def positionalMantissa (fmt : FloatingPointFormat) (digits : List ℕ) : ℕ :=
  Nat.ofDigits fmt.beta digits.reverse
/-- Higham equation (2.2), represented through the equivalent integer mantissa
used in (2.1). -/
def positionalValue (fmt : FloatingPointFormat) (negative : Bool)
    (digits : List ℕ) (e : ℤ) : ℝ :=
  fmt.normalizedValue negative (fmt.positionalMantissa digits) e
/-- Same-exponent structural adjacency between normalized values.  The relation
is unordered; it records the two immediate mantissas `m` and `m+1` at a fixed
exponent before proving they are adjacent in the ordered real set. -/
def sameExponentAdjacentNormalized (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  ∃ negative m e,
    fmt.normalizedMantissa m ∧
    fmt.normalizedMantissa (m + 1) ∧
    ((x = fmt.normalizedValue negative m e ∧
        y = fmt.normalizedValue negative (m + 1) e) ∨
      (x = fmt.normalizedValue negative (m + 1) e ∧
        y = fmt.normalizedValue negative m e))
/-- Exponent-boundary structural adjacency: the largest mantissa at exponent
`e` next to the smallest mantissa at exponent `e+1`.  The relation is unordered
and does not yet assert there is no representable value between them. -/
def boundaryAdjacentNormalized (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  ∃ negative e,
    ((x = fmt.normalizedValue negative fmt.maxNormalMantissa e ∧
        y = fmt.normalizedValue negative fmt.minNormalMantissa (e + 1)) ∨
      (x = fmt.normalizedValue negative fmt.minNormalMantissa (e + 1) ∧
        y = fmt.normalizedValue negative fmt.maxNormalMantissa e))
/-- Structural adjacency for normalized values in Higham's unbounded-exponent
system: either adjacent mantissas at one exponent or the exponent-boundary
case.  Later lemmas must still prove this structural relation matches real-order
adjacency in the representable set. -/
def adjacentNormalized (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  fmt.sameExponentAdjacentNormalized x y ∨ fmt.boundaryAdjacentNormalized x y
/-- Real-order adjacency in Higham's unbounded normalized system `G`: both
endpoints are normalized representable values, they are distinct, and no
normalized representable value lies strictly between them in either order. -/
def realOrderAdjacentNormalized (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  fmt.unboundedNormalizedSystem x ∧
    fmt.unboundedNormalizedSystem y ∧
      x ≠ y ∧
        ∀ z, fmt.unboundedNormalizedSystem z →
          ¬ ((x < z ∧ z < y) ∨ (y < z ∧ z < x))
/-- Nearest-rounding relation into an arbitrary set of representable values.
This deliberately leaves tie-breaking as a relation rather than a function. -/
def nearestRoundingIn (S : ℝ → Prop) (x y : ℝ) : Prop :=
  S y ∧ ∀ z, S z → |x - y| ≤ |x - z|
/-- Nearest rounding into Higham's unbounded-exponent set `G`. -/
def nearestRoundingToUnbounded (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  nearestRoundingIn fmt.unboundedNormalizedSystem x y
/-- Nearest rounding into the finite system including zero and subnormals. -/
def nearestRoundingToFinite (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  nearestRoundingIn fmt.finiteSystem x y
/-- First IEEE-facing underflow-result predicate for Chapter 2: the exact real
input is in the source-facing underflow range, the returned value is a finite
nearest-rounded value, the underflow flag is set, and an inexact flag is set
whenever the rounded value differs from the exact real input.  This is the
finite gradual-underflow branch, not a complete IEEE special-value semantics. -/
def ieeeUnderflowResult
    (fmt : FloatingPointFormat) (x rounded : ℝ)
    (r : IeeeOperationResult) : Prop :=
  fmt.finiteUnderflowRange x ∧
    fmt.nearestRoundingToFinite x rounded ∧
    r.value = IeeeValue.finite rounded ∧
    r.hasFlag IeeeExceptionFlag.underflow ∧
    (rounded ≠ x → r.hasFlag IeeeExceptionFlag.inexact)
/-- Mode-dependent finite evidence for an IEEE-facing underflow result.  The
nearest/even mode keeps the nearest-finite requirement used by
`ieeeUnderflowResult`; directed modes record the finite one-sided/toward-zero
property appropriate for the mode. -/
def ieeeUnderflowModeRoundingEvidence
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (x rounded : ℝ) : Prop :=
  match mode with
  | IeeeRoundingMode.nearestEven =>
      fmt.nearestRoundingToFinite x rounded
  | IeeeRoundingMode.towardZero =>
      fmt.finiteSystem rounded ∧ |rounded| ≤ |x|
  | IeeeRoundingMode.towardPositive =>
      fmt.finiteSystem rounded ∧ x ≤ rounded
  | IeeeRoundingMode.towardNegative =>
      fmt.finiteSystem rounded ∧ rounded ≤ x
/-- Mode-aware IEEE-facing underflow-result predicate.  It generalizes
`ieeeUnderflowResult` from nearest/even to directed modes by separating the
rounding-policy evidence from the common result value and flag behavior. -/
def ieeeUnderflowModeResult
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (x rounded : ℝ) (r : IeeeOperationResult) : Prop :=
  fmt.finiteUnderflowRange x ∧
    fmt.ieeeUnderflowModeRoundingEvidence mode x rounded ∧
    r.value = IeeeValue.finite rounded ∧
    r.hasFlag IeeeExceptionFlag.underflow ∧
    (rounded ≠ x → r.hasFlag IeeeExceptionFlag.inexact)
/-- Default IEEE-facing underflow result for a finite exact real result in the
underflow range.  It returns the supplied finite rounded value, always sets the
underflow flag, and sets the inexact flag exactly when the rounded value is not
the exact real input. -/
def ieeeUnderflowDefaultResult
    (_fmt : FloatingPointFormat) (x rounded : ℝ) :
    IeeeOperationResult where
  value := IeeeValue.finite rounded
  flag := fun flag =>
    flag = IeeeExceptionFlag.underflow ∨
      (rounded ≠ x ∧ flag = IeeeExceptionFlag.inexact)
theorem ieeeUnderflowDefaultResult_value
    (fmt : FloatingPointFormat) (x rounded : ℝ) :
    (fmt.ieeeUnderflowDefaultResult x rounded).value =
      IeeeValue.finite rounded := rfl
theorem ieeeUnderflowDefaultResult_toReal?
    (fmt : FloatingPointFormat) (x rounded : ℝ) :
    (fmt.ieeeUnderflowDefaultResult x rounded).value.toReal? =
      some rounded := rfl
theorem ieeeUnderflowDefaultResult_hasFlag_iff
    (fmt : FloatingPointFormat) (x rounded : ℝ)
    (flag : IeeeExceptionFlag) :
    (fmt.ieeeUnderflowDefaultResult x rounded).hasFlag flag ↔
      flag = IeeeExceptionFlag.underflow ∨
        (rounded ≠ x ∧ flag = IeeeExceptionFlag.inexact) := by
  rfl
theorem ieeeUnderflowDefaultResult_hasUnderflowFlag
    (fmt : FloatingPointFormat) (x rounded : ℝ) :
    (fmt.ieeeUnderflowDefaultResult x rounded).hasFlag
      IeeeExceptionFlag.underflow := by
  simp [ieeeUnderflowDefaultResult, IeeeOperationResult.hasFlag]
theorem ieeeUnderflowDefaultResult_hasInexactFlag_of_ne
    (fmt : FloatingPointFormat) {x rounded : ℝ} (hne : rounded ≠ x) :
    (fmt.ieeeUnderflowDefaultResult x rounded).hasFlag
      IeeeExceptionFlag.inexact := by
  simp [ieeeUnderflowDefaultResult, IeeeOperationResult.hasFlag, hne]
theorem ieeeUnderflowDefaultResult_ieeeUnderflowResult
    {fmt : FloatingPointFormat} {x rounded : ℝ}
    (hx : fmt.finiteUnderflowRange x)
    (hround : fmt.nearestRoundingToFinite x rounded) :
    fmt.ieeeUnderflowResult x rounded
      (fmt.ieeeUnderflowDefaultResult x rounded) := by
  exact ⟨hx, hround, rfl,
    fmt.ieeeUnderflowDefaultResult_hasUnderflowFlag x rounded,
    fun hne => fmt.ieeeUnderflowDefaultResult_hasInexactFlag_of_ne hne⟩
theorem ieeeUnderflowDefaultResult_ieeeUnderflowModeResult
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x rounded : ℝ}
    (hx : fmt.finiteUnderflowRange x)
    (hround : fmt.ieeeUnderflowModeRoundingEvidence mode x rounded) :
    fmt.ieeeUnderflowModeResult mode x rounded
      (fmt.ieeeUnderflowDefaultResult x rounded) := by
  exact ⟨hx, hround, rfl,
    fmt.ieeeUnderflowDefaultResult_hasUnderflowFlag x rounded,
    fun hne => fmt.ieeeUnderflowDefaultResult_hasInexactFlag_of_ne hne⟩
/-- Explicit local round-away selector for an ordered adjacent bracket.  It
chooses the nearer endpoint, and in an exact distance tie chooses the endpoint
with larger magnitude.  This is a local policy for a supplied adjacent pair,
not yet a total finite-format rounding function. -/
def nearestAdjacentRoundAway (x a b : ℝ) : ℝ :=
  if |x - a| < |x - b| then a
  else if |x - b| < |x - a| then b
  else if |a| ≤ |b| then b else a
/-- Mantissa parity used by the local round-to-even tie policy.  For binary and
decimal-style formats this matches Higham's "even last digit" rule on adjacent
same-exponent mantissas. -/
def evenMantissa (m : ℕ) : Prop :=
  m % 2 = 0
instance decidableEvenMantissa (m : ℕ) : Decidable (evenMantissa m) := by
  unfold evenMantissa
  infer_instance
theorem evenMantissa_succ_iff_not_evenMantissa (m : ℕ) :
    evenMantissa (m + 1) ↔ ¬ evenMantissa m := by
  unfold evenMantissa
  omega
theorem evenMantissa_iff_not_evenMantissa_succ (m : ℕ) :
    evenMantissa m ↔ ¬ evenMantissa (m + 1) := by
  constructor
  · intro hm hm_succ
    exact (evenMantissa_succ_iff_not_evenMantissa m).mp hm_succ hm
  · intro hnot_succ
    by_contra hm
    exact hnot_succ ((evenMantissa_succ_iff_not_evenMantissa m).mpr hm)
/-- Explicit local round-to-even selector for an ordered adjacent bracket.  It
chooses the nearer endpoint, and in an exact distance tie chooses the endpoint
whose supplied left mantissa is even; otherwise it chooses the right endpoint.
This is a local policy for a supplied adjacent pair, not a total IEEE rounding
operation. -/
def nearestAdjacentRoundToEven (x a b : ℝ) (leftMantissa : ℕ) : ℝ :=
  if |x - a| < |x - b| then a
  else if |x - b| < |x - a| then b
  else if evenMantissa leftMantissa then a else b
/-- Local directed selector for rounding toward negative infinity on a supplied
ordered adjacent bracket `a <= x <= b`.  Exact endpoints are fixed; otherwise it
chooses the left endpoint. -/
def adjacentRoundTowardNegative (x a b : ℝ) : ℝ :=
  if x = b then b else a
/-- Local directed selector for rounding toward positive infinity on a supplied
ordered adjacent bracket `a <= x <= b`.  Exact endpoints are fixed; otherwise it
chooses the right endpoint. -/
def adjacentRoundTowardPositive (x a b : ℝ) : ℝ :=
  if x = a then a else b
/-- Local directed selector for rounding toward zero on a supplied adjacent
bracket.  On a nonnegative bracket it uses the toward-negative selector, and on
a negative bracket it uses the toward-positive selector, so exact endpoints are
fixed by the directed endpoint selectors. -/
def adjacentRoundTowardZero (x a b : ℝ) : ℝ :=
  if x < 0 then adjacentRoundTowardPositive x a b
  else adjacentRoundTowardNegative x a b
theorem minNormalMantissa_pos (fmt : FloatingPointFormat) :
    0 < fmt.minNormalMantissa := by
  unfold minNormalMantissa
  exact Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) fmt.beta_ge_two)
theorem mantissaBound_pos (fmt : FloatingPointFormat) :
    0 < fmt.beta ^ fmt.t :=
  Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) fmt.beta_ge_two)
theorem one_lt_beta (fmt : FloatingPointFormat) :
    1 < fmt.beta :=
  lt_of_lt_of_le (by decide : 1 < 2) fmt.beta_ge_two
theorem minNormalMantissa_lt_mantissaBound (fmt : FloatingPointFormat) :
    fmt.minNormalMantissa < fmt.beta ^ fmt.t := by
  unfold minNormalMantissa
  exact Nat.pow_lt_pow_right fmt.one_lt_beta (Nat.sub_lt fmt.t_pos Nat.one_pos)
theorem minNormalMantissa_mul_beta_eq_mantissaBound
    (fmt : FloatingPointFormat) :
    fmt.minNormalMantissa * fmt.beta = fmt.beta ^ fmt.t := by
  unfold minNormalMantissa
  rw [← pow_succ]
  congr 1
  exact Nat.sub_one_add_one_eq_of_pos fmt.t_pos
theorem normalizedMantissa_pos {fmt : FloatingPointFormat} {m : ℕ}
    (hm : fmt.normalizedMantissa m) :
    0 < m :=
  lt_of_lt_of_le fmt.minNormalMantissa_pos hm.1
theorem minNormalMantissa_le_mantissaBound (fmt : FloatingPointFormat) :
    fmt.minNormalMantissa ≤ fmt.beta ^ fmt.t := by
  unfold minNormalMantissa
  exact Nat.pow_le_pow_right
    (Nat.succ_le_of_lt (lt_of_lt_of_le (by decide : 0 < 2) fmt.beta_ge_two))
    (Nat.sub_le _ _)
theorem minNormalMantissa_normalized (fmt : FloatingPointFormat) :
    fmt.normalizedMantissa fmt.minNormalMantissa :=
  ⟨le_rfl, fmt.minNormalMantissa_lt_mantissaBound⟩
theorem maxNormalMantissa_add_one (fmt : FloatingPointFormat) :
    fmt.maxNormalMantissa + 1 = fmt.beta ^ fmt.t := by
  unfold maxNormalMantissa
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt fmt.mantissaBound_pos)
theorem maxNormalMantissa_lt_mantissaBound (fmt : FloatingPointFormat) :
    fmt.maxNormalMantissa < fmt.beta ^ fmt.t := by
  rw [← fmt.maxNormalMantissa_add_one]
  exact Nat.lt_succ_self fmt.maxNormalMantissa
theorem minNormalMantissa_le_maxNormalMantissa (fmt : FloatingPointFormat) :
    fmt.minNormalMantissa ≤ fmt.maxNormalMantissa := by
  have hlt : fmt.minNormalMantissa < fmt.maxNormalMantissa + 1 := by
    rw [fmt.maxNormalMantissa_add_one]
    exact fmt.minNormalMantissa_lt_mantissaBound
  exact Nat.le_of_lt_succ hlt
theorem maxNormalMantissa_normalized (fmt : FloatingPointFormat) :
    fmt.normalizedMantissa fmt.maxNormalMantissa :=
  ⟨fmt.minNormalMantissa_le_maxNormalMantissa,
    fmt.maxNormalMantissa_lt_mantissaBound⟩
theorem normalizedMantissa_succ_of_ne_maxNormalMantissa
    {fmt : FloatingPointFormat} {m : ℕ}
    (hm : fmt.normalizedMantissa m)
    (hne : m ≠ fmt.maxNormalMantissa) :
    fmt.normalizedMantissa (m + 1) := by
  have hm_le_max : m ≤ fmt.maxNormalMantissa := by
    have hm_bound : m < fmt.maxNormalMantissa + 1 := by
      simpa [fmt.maxNormalMantissa_add_one] using hm.2
    exact Nat.le_of_lt_succ hm_bound
  have hm_lt_max : m < fmt.maxNormalMantissa :=
    lt_of_le_of_ne hm_le_max hne
  exact
    ⟨le_trans hm.1 (Nat.le_succ m),
      lt_of_le_of_lt (Nat.succ_le_of_lt hm_lt_max)
        fmt.maxNormalMantissa_lt_mantissaBound⟩
theorem normalizedMantissa_pred_of_ne_minNormalMantissa
    {fmt : FloatingPointFormat} {m : ℕ}
    (hm : fmt.normalizedMantissa m)
    (hne : m ≠ fmt.minNormalMantissa) :
    fmt.normalizedMantissa (m - 1) := by
  have hmin_lt_m : fmt.minNormalMantissa < m :=
    lt_of_le_of_ne hm.1 hne.symm
  constructor
  · omega
  · exact lt_of_le_of_lt (Nat.sub_le m 1) hm.2
/-- If two normalized mantissas have distinct exponents, aligning the higher
exponent mantissa onto the lower exponent lattice dominates the lower mantissa.

This is the coefficient-order fact needed by the opposite-sign normalized
addition dispatchers after the same-exponent exact branch has been split off. -/
theorem normalizedMantissa_le_scaled_of_exponent_lt
    {fmt : FloatingPointFormat} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (hlt : eLow < eHigh) :
    mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) := by
  let shift := Int.toNat (eHigh - eLow)
  have hdiff_pos : 0 < eHigh - eLow := by omega
  have hshift_pos : 0 < shift := by
    have hshift_ne : shift ≠ 0 := by
      intro hzero
      have hle : eHigh - eLow ≤ 0 := by
        exact Int.toNat_eq_zero.mp hzero
      omega
    exact Nat.pos_of_ne_zero hshift_ne
  have hbeta_le_shift : fmt.beta ≤ fmt.beta ^ shift :=
    Nat.le_self_pow (Nat.ne_of_gt hshift_pos) fmt.beta
  have hmant_bound : mLow ≤ fmt.beta ^ fmt.t :=
    le_of_lt hmLow.2
  have hscaled_bound :
      fmt.beta ^ fmt.t ≤ mHigh * fmt.beta ^ shift := by
    calc
      fmt.beta ^ fmt.t = fmt.minNormalMantissa * fmt.beta := by
        rw [fmt.minNormalMantissa_mul_beta_eq_mantissaBound]
      _ ≤ mHigh * fmt.beta ^ shift :=
        Nat.mul_le_mul hmHigh.1 hbeta_le_shift
  exact le_trans hmant_bound hscaled_bound
theorem evenMantissa_minNormalMantissa_of_even_beta
    (fmt : FloatingPointFormat)
    (hbeta : evenMantissa fmt.beta) (ht : 1 < fmt.t) :
    evenMantissa fmt.minNormalMantissa := by
  unfold evenMantissa at *
  apply Nat.mod_eq_zero_of_dvd
  have hbeta_dvd : 2 ∣ fmt.beta := Nat.dvd_of_mod_eq_zero hbeta
  have hpow : fmt.beta ∣ fmt.beta ^ (fmt.t - 1) := by
    simpa using
      (Nat.pow_dvd_pow fmt.beta (by omega : 1 ≤ fmt.t - 1))
  exact dvd_trans hbeta_dvd hpow
theorem not_evenMantissa_maxNormalMantissa_of_even_beta
    (fmt : FloatingPointFormat)
    (hbeta : evenMantissa fmt.beta) :
    ¬ evenMantissa fmt.maxNormalMantissa := by
  unfold evenMantissa at *
  intro hmax
  have hbeta_dvd : 2 ∣ fmt.beta := Nat.dvd_of_mod_eq_zero hbeta
  have hpow : 2 ∣ fmt.beta ^ fmt.t := by
    have hbeta_pow : fmt.beta ∣ fmt.beta ^ fmt.t := by
      simpa using
        (Nat.pow_dvd_pow fmt.beta (Nat.succ_le_of_lt fmt.t_pos))
    exact dvd_trans hbeta_dvd hbeta_pow
  have hbound_mod : (fmt.beta ^ fmt.t) % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd hpow
  have hmax_add := fmt.maxNormalMantissa_add_one
  omega
theorem evenMantissa_minNormalMantissa_iff_not_evenMantissa_maxNormalMantissa_of_even_beta
    (fmt : FloatingPointFormat)
    (hbeta : evenMantissa fmt.beta) (ht : 1 < fmt.t) :
    evenMantissa fmt.minNormalMantissa ↔
      ¬ evenMantissa fmt.maxNormalMantissa := by
  constructor
  · intro _hmin
    exact fmt.not_evenMantissa_maxNormalMantissa_of_even_beta hbeta
  · intro _hmax
    exact fmt.evenMantissa_minNormalMantissa_of_even_beta hbeta ht
theorem evenMantissa_maxNormalMantissa_iff_not_evenMantissa_minNormalMantissa_of_even_beta
    (fmt : FloatingPointFormat)
    (hbeta : evenMantissa fmt.beta) (ht : 1 < fmt.t) :
    evenMantissa fmt.maxNormalMantissa ↔
      ¬ evenMantissa fmt.minNormalMantissa := by
  constructor
  · intro hmax
    exact False.elim
      ((fmt.not_evenMantissa_maxNormalMantissa_of_even_beta hbeta) hmax)
  · intro hnot_min
    exact False.elim
      (hnot_min (fmt.evenMantissa_minNormalMantissa_of_even_beta hbeta ht))
theorem minNormalMantissa_mem_normalizedSystem (fmt : FloatingPointFormat)
    (negative : Bool) :
    fmt.normalizedSystem
      (fmt.normalizedValue negative fmt.minNormalMantissa fmt.emin) :=
  ⟨negative, fmt.minNormalMantissa, fmt.emin,
    fmt.minNormalMantissa_normalized, ⟨le_rfl, fmt.emin_le_emax⟩, rfl⟩
theorem maxNormalMantissa_mem_normalizedSystem (fmt : FloatingPointFormat)
    (negative : Bool) :
    fmt.normalizedSystem
      (fmt.normalizedValue negative fmt.maxNormalMantissa fmt.emax) :=
  ⟨negative, fmt.maxNormalMantissa, fmt.emax,
    fmt.maxNormalMantissa_normalized, ⟨fmt.emin_le_emax, le_rfl⟩, rfl⟩
theorem subnormalMantissa_inRange {fmt : FloatingPointFormat} {m : ℕ}
    (hm : fmt.subnormalMantissa m) :
    fmt.mantissaInRange m := by
  unfold mantissaInRange
  exact lt_of_lt_of_le hm.2 fmt.minNormalMantissa_le_mantissaBound
theorem one_subnormalMantissa_of_subnormalMantissa
    {fmt : FloatingPointFormat} {m : ℕ} (hm : fmt.subnormalMantissa m) :
    fmt.subnormalMantissa 1 :=
  ⟨by norm_num, lt_of_le_of_lt (Nat.succ_le_of_lt hm.1) hm.2⟩
theorem digitStringInRange_reverse {fmt : FloatingPointFormat}
    {digits : List ℕ} (hdigits : fmt.digitStringInRange digits) :
    fmt.digitStringInRange digits.reverse := by
  rcases hdigits with ⟨hlen, hdigit_lt⟩
  constructor
  · rw [List.length_reverse]
    exact hlen
  · intro d hd
    exact hdigit_lt d (by simpa using List.mem_reverse.mp hd)
theorem positionalMantissa_lt_mantissaBound {fmt : FloatingPointFormat}
    {digits : List ℕ} (hdigits : fmt.digitStringInRange digits) :
    fmt.positionalMantissa digits < fmt.beta ^ fmt.t := by
  have hrev := fmt.digitStringInRange_reverse hdigits
  have hlt :=
    Nat.ofDigits_lt_base_pow_length fmt.one_lt_beta hrev.2
  simpa [positionalMantissa, hrev.1] using hlt
theorem minNormalMantissa_le_positionalMantissa
    {fmt : FloatingPointFormat} {digits : List ℕ}
    (hdigits : fmt.normalizedDigitString digits) :
    fmt.minNormalMantissa ≤ fmt.positionalMantissa digits := by
  rcases hdigits with ⟨hrange, d, rest, rfl, hdpos⟩
  have hlen : rest.length + 1 = fmt.t := by
    simpa using hrange.1
  unfold minNormalMantissa positionalMantissa
  rw [Nat.ofDigits_reverse_cons]
  have hrest : rest.length = fmt.t - 1 := by
    omega
  have hpow :
      fmt.beta ^ (fmt.t - 1) ≤ fmt.beta ^ rest.length * d := by
    rw [hrest]
    calc
      fmt.beta ^ (fmt.t - 1) = fmt.beta ^ (fmt.t - 1) * 1 := by
        rw [mul_one]
      _ ≤ fmt.beta ^ (fmt.t - 1) * d :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hdpos)
  exact le_trans hpow (Nat.le_add_left _ _)
theorem positionalMantissa_normalized {fmt : FloatingPointFormat}
    {digits : List ℕ} (hdigits : fmt.normalizedDigitString digits) :
    fmt.normalizedMantissa (fmt.positionalMantissa digits) :=
  ⟨fmt.minNormalMantissa_le_positionalMantissa hdigits,
    fmt.positionalMantissa_lt_mantissaBound hdigits.1⟩
theorem positionalValue_eq_normalizedValue_positionalMantissa
    (fmt : FloatingPointFormat) (negative : Bool)
    (digits : List ℕ) (e : ℤ) :
    fmt.positionalValue negative digits e =
      fmt.normalizedValue negative (fmt.positionalMantissa digits) e := rfl
theorem positionalValue_mem_normalizedSystem
    {fmt : FloatingPointFormat} {negative : Bool}
    {digits : List ℕ} {e : ℤ}
    (hdigits : fmt.normalizedDigitString digits)
    (he : fmt.exponentInRange e) :
    fmt.normalizedSystem (fmt.positionalValue negative digits e) :=
  ⟨negative, fmt.positionalMantissa digits, e,
    fmt.positionalMantissa_normalized hdigits, he, rfl⟩
theorem exists_digitStringInRange_positionalMantissa_eq
    {fmt : FloatingPointFormat} {m : ℕ} (hm : fmt.mantissaInRange m) :
    ∃ digits : List ℕ,
      fmt.digitStringInRange digits ∧
        fmt.positionalMantissa digits = m := by
  let little := Nat.digitsAppend fmt.beta fmt.t m
  refine ⟨little.reverse, ?_, ?_⟩
  · have hlittle := Nat.mapsTo_digitsAppend fmt.one_lt_beta fmt.t hm
    constructor
    · rw [List.length_reverse]
      exact hlittle.1
    · intro d hd
      exact hlittle.2 d (by simpa using List.mem_reverse.mp hd)
  · unfold positionalMantissa
    simp [little]
    exact (Nat.setInvOn_digitsAppend_ofDigits fmt.one_lt_beta fmt.t).2 hm
theorem exists_normalizedDigitString_positionalMantissa_eq
    {fmt : FloatingPointFormat} {m : ℕ}
    (hm : fmt.normalizedMantissa m) :
    ∃ digits : List ℕ,
      fmt.normalizedDigitString digits ∧
        fmt.positionalMantissa digits = m := by
  let little := fmt.beta.digits m
  have hmpos : 0 < m := fmt.normalizedMantissa_pos hm
  have hmne : m ≠ 0 := ne_of_gt hmpos
  have hmin : fmt.beta ^ (fmt.t - 1) ≤ m := by
    simpa [minNormalMantissa] using hm.1
  have hlen_le : little.length ≤ fmt.t := by
    exact (Nat.digits_length_le_iff fmt.one_lt_beta m).2 hm.2
  have hlen_gt : fmt.t - 1 < little.length := by
    exact (Nat.lt_digits_length_iff fmt.one_lt_beta m).2 hmin
  have hlen : little.length = fmt.t := by
    omega
  have hlittle_ne : little ≠ [] := by
    exact Nat.digits_ne_nil_iff_ne_zero.mpr hmne
  refine ⟨little.reverse, ?_, ?_⟩
  · constructor
    · constructor
      · rw [List.length_reverse]
        exact hlen
      · intro d hd
        exact Nat.digits_lt_base fmt.one_lt_beta
          (by simpa [little] using List.mem_reverse.mp hd)
    · refine ⟨little.getLast hlittle_ne, little.dropLast.reverse, ?_, ?_⟩
      · calc
          little.reverse =
              (little.dropLast ++ [little.getLast hlittle_ne]).reverse := by
            rw [List.dropLast_append_getLast hlittle_ne]
          _ = little.getLast hlittle_ne :: little.dropLast.reverse := by
            simp
      · exact Nat.pos_of_ne_zero
          (by
            simpa [little] using Nat.getLast_digit_ne_zero fmt.beta hmne)
  · unfold positionalMantissa
    simp [little, Nat.ofDigits_digits]
theorem digitStringInRange_eq_of_positionalMantissa_eq
    {fmt : FloatingPointFormat} {digits₁ digits₂ : List ℕ}
    (h₁ : fmt.digitStringInRange digits₁)
    (h₂ : fmt.digitStringInRange digits₂)
    (h : fmt.positionalMantissa digits₁ = fmt.positionalMantissa digits₂) :
    digits₁ = digits₂ := by
  have h₁rev := fmt.digitStringInRange_reverse h₁
  have h₂rev := fmt.digitStringInRange_reverse h₂
  have hrev :
      digits₁.reverse = digits₂.reverse :=
    Nat.injOn_ofDigits fmt.one_lt_beta fmt.t
      h₁rev h₂rev (by simpa [positionalMantissa] using h)
  have := congrArg List.reverse hrev
  simpa using this
theorem betaR_pos (fmt : FloatingPointFormat) :
    0 < fmt.betaR := by
  unfold betaR
  exact Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 2) fmt.beta_ge_two)
theorem betaR_nonneg (fmt : FloatingPointFormat) :
    0 ≤ fmt.betaR :=
  (fmt.betaR_pos).le
theorem betaR_zpow_pos (fmt : FloatingPointFormat) (e : ℤ) :
    0 < fmt.betaR ^ e :=
  zpow_pos fmt.betaR_pos e
theorem betaR_zpow_nonneg (fmt : FloatingPointFormat) (e : ℤ) :
    0 ≤ fmt.betaR ^ e :=
  (fmt.betaR_zpow_pos e).le
theorem betaR_zpow_le_zpow_of_le (fmt : FloatingPointFormat)
    {e e' : ℤ} (h : e ≤ e') :
    fmt.betaR ^ e ≤ fmt.betaR ^ e' := by
  have hone : (1 : ℝ) ≤ fmt.betaR := by
    unfold betaR
    exact_mod_cast (le_trans (by decide : 1 ≤ 2) fmt.beta_ge_two)
  exact zpow_le_zpow_right₀ hone h
theorem machineEpsilon_nonneg (fmt : FloatingPointFormat) :
    0 ≤ fmt.machineEpsilon := by
  unfold machineEpsilon
  exact fmt.betaR_zpow_nonneg (1 - (fmt.t : ℤ))
theorem machineEpsilon_pos (fmt : FloatingPointFormat) :
    0 < fmt.machineEpsilon := by
  unfold machineEpsilon
  exact fmt.betaR_zpow_pos (1 - (fmt.t : ℤ))
theorem unitRoundoff_nonneg (fmt : FloatingPointFormat) :
    0 ≤ fmt.unitRoundoff := by
  unfold unitRoundoff
  exact mul_nonneg (by norm_num) fmt.machineEpsilon_nonneg
theorem unitRoundoff_pos (fmt : FloatingPointFormat) :
    0 < fmt.unitRoundoff := by
  unfold unitRoundoff
  exact mul_pos (by norm_num) fmt.machineEpsilon_pos
theorem ulpAtExponent_nonneg (fmt : FloatingPointFormat) (e : ℤ) :
    0 ≤ fmt.ulpAtExponent e := by
  unfold ulpAtExponent
  exact fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ))
theorem ulpAtExponent_pos (fmt : FloatingPointFormat) (e : ℤ) :
    0 < fmt.ulpAtExponent e := by
  unfold ulpAtExponent
  exact fmt.betaR_zpow_pos (e - (fmt.t : ℤ))
theorem ulpAtExponent_one (fmt : FloatingPointFormat) :
    fmt.ulpAtExponent 1 = fmt.machineEpsilon :=
  rfl
theorem signValue_abs (fmt : FloatingPointFormat) (negative : Bool) :
    |fmt.signValue negative| = 1 := by
  unfold signValue
  cases negative <;> simp
theorem normalizedValue_abs (fmt : FloatingPointFormat) (negative : Bool)
    (m : ℕ) (e : ℤ) :
    |fmt.normalizedValue negative m e| =
      (m : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  unfold normalizedValue
  rw [abs_mul, abs_mul, fmt.signValue_abs negative,
    abs_of_nonneg (Nat.cast_nonneg m),
    abs_of_pos (fmt.betaR_zpow_pos (e - (fmt.t : ℤ)))]
  ring
theorem subnormalValue_abs (fmt : FloatingPointFormat) (negative : Bool)
    (m : ℕ) :
    |fmt.subnormalValue negative m| =
      (m : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
  unfold subnormalValue
  rw [abs_mul, abs_mul, fmt.signValue_abs negative,
    abs_of_nonneg (Nat.cast_nonneg m),
    abs_of_pos (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))]
  ring
theorem normalizedValue_ne_zero {fmt : FloatingPointFormat}
    {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    fmt.normalizedValue negative m e ≠ 0 := by
  have hpos :
      0 < |fmt.normalizedValue negative m e| := by
    rw [fmt.normalizedValue_abs negative m e]
    exact mul_pos
      (Nat.cast_pos.mpr (fmt.normalizedMantissa_pos hm))
      (fmt.betaR_zpow_pos (e - (fmt.t : ℤ)))
  exact abs_pos.mp hpos
theorem unboundedNormalizedSystem_ne_zero {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.unboundedNormalizedSystem y) :
    y ≠ 0 := by
  rcases hy with ⟨negative, m, e, hm, rfl⟩
  exact fmt.normalizedValue_ne_zero hm
theorem subnormalValue_ne_zero {fmt : FloatingPointFormat}
    {negative : Bool} {m : ℕ} (hm : fmt.subnormalMantissa m) :
    fmt.subnormalValue negative m ≠ 0 := by
  have hpos :
      0 < |fmt.subnormalValue negative m| := by
    rw [fmt.subnormalValue_abs negative m]
    exact mul_pos
      (Nat.cast_pos.mpr hm.1)
      (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))
  exact abs_pos.mp hpos
theorem subnormalValue_false_pos {fmt : FloatingPointFormat} {m : ℕ}
    (hm : fmt.subnormalMantissa m) :
    0 < fmt.subnormalValue false m := by
  simpa [subnormalValue, signValue] using
    mul_pos (Nat.cast_pos.mpr hm.1)
      (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))
theorem subnormalValue_true_neg {fmt : FloatingPointFormat} {m : ℕ}
    (hm : fmt.subnormalMantissa m) :
    fmt.subnormalValue true m < 0 := by
  have hpos :
      0 < (m : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) :=
    mul_pos (Nat.cast_pos.mpr hm.1)
      (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))
  have hneg :
      -((m : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) < 0 := by
    linarith
  simpa [subnormalValue, signValue] using hneg
theorem subnormalSystem_ne_zero {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.subnormalSystem y) :
    y ≠ 0 := by
  rcases hy with ⟨negative, m, hm, rfl⟩
  exact fmt.subnormalValue_ne_zero hm
theorem normalizedValue_true_eq_neg_false (fmt : FloatingPointFormat)
    (m : ℕ) (e : ℤ) :
    fmt.normalizedValue true m e = -fmt.normalizedValue false m e := by
  unfold normalizedValue signValue
  simp
theorem normalizedValue_not_eq_neg (fmt : FloatingPointFormat)
    (negative : Bool) (m : ℕ) (e : ℤ) :
    fmt.normalizedValue (!negative) m e =
      -fmt.normalizedValue negative m e := by
  cases negative
  · simp [normalizedValue, signValue]
  · simp [normalizedValue, signValue]
/-- Flipping the sign bit negates a subnormal value with the same mantissa. -/
theorem subnormalValue_not_eq_neg (fmt : FloatingPointFormat)
    (negative : Bool) (m : ℕ) :
    fmt.subnormalValue (!negative) m =
      -fmt.subnormalValue negative m := by
  cases negative
  · simp [subnormalValue, signValue]
  · simp [subnormalValue, signValue]
/-- The normalized finite system is closed under negation. -/
theorem normalizedSystem_neg
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.normalizedSystem y) :
    fmt.normalizedSystem (-y) := by
  rcases hy with ⟨negative, m, e, hm, he, rfl⟩
  refine ⟨!negative, m, e, hm, he, ?_⟩
  exact Eq.symm (fmt.normalizedValue_not_eq_neg negative m e)
/-- Higham's unbounded normalized system `G` is closed under negation. -/
theorem unboundedNormalizedSystem_neg
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.unboundedNormalizedSystem y) :
    fmt.unboundedNormalizedSystem (-y) := by
  rcases hy with ⟨negative, m, e, hm, rfl⟩
  refine ⟨!negative, m, e, hm, ?_⟩
  exact Eq.symm (fmt.normalizedValue_not_eq_neg negative m e)
/-- The subnormal finite system is closed under negation. -/
theorem subnormalSystem_neg
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.subnormalSystem y) :
    fmt.subnormalSystem (-y) := by
  rcases hy with ⟨negative, m, hm, rfl⟩
  refine ⟨!negative, m, hm, ?_⟩
  exact Eq.symm (fmt.subnormalValue_not_eq_neg negative m)
/-- The finite floating-point system is closed under negation. -/
theorem finiteSystem_neg
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.finiteSystem y) :
    fmt.finiteSystem (-y) := by
  rcases hy with hzero | hnorm | hsub
  · subst y
    simp [finiteSystem]
  · exact Or.inr (Or.inl (fmt.normalizedSystem_neg hnorm))
  · exact Or.inr (Or.inr (fmt.subnormalSystem_neg hsub))
theorem normalizedValue_sameExponent_lt_iff_false
    (fmt : FloatingPointFormat) (m n : ℕ) (e : ℤ) :
    fmt.normalizedValue false m e < fmt.normalizedValue false n e ↔
      m < n := by
  constructor
  · intro h
    have hscale_nonneg : 0 ≤ fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ))
    have hmul :
        (m : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) <
          (n : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      simpa [normalizedValue, signValue] using h
    exact Nat.cast_lt.mp (lt_of_mul_lt_mul_right hmul hscale_nonneg)
  · intro hmn
    have hscale_pos : 0 < fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.betaR_zpow_pos (e - (fmt.t : ℤ))
    have hcast : (m : ℝ) < n := Nat.cast_lt.mpr hmn
    have hmul :
        (m : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) <
          (n : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      mul_lt_mul_of_pos_right hcast hscale_pos
    simpa [normalizedValue, signValue] using hmul
theorem normalizedValue_sameExponent_lt_iff_true
    (fmt : FloatingPointFormat) (m n : ℕ) (e : ℤ) :
    fmt.normalizedValue true m e < fmt.normalizedValue true n e ↔
      n < m := by
  rw [fmt.normalizedValue_true_eq_neg_false m e,
    fmt.normalizedValue_true_eq_neg_false n e, neg_lt_neg_iff]
  exact fmt.normalizedValue_sameExponent_lt_iff_false n m e
theorem normalizedValue_sameExponent_no_between_succ
    (fmt : FloatingPointFormat) (negative : Bool) (m k : ℕ) (e : ℤ) :
    ¬ ((fmt.normalizedValue negative m e <
          fmt.normalizedValue negative k e ∧
        fmt.normalizedValue negative k e <
          fmt.normalizedValue negative (m + 1) e) ∨
      (fmt.normalizedValue negative (m + 1) e <
          fmt.normalizedValue negative k e ∧
        fmt.normalizedValue negative k e <
          fmt.normalizedValue negative m e)) := by
  cases negative
  · intro h
    rcases h with hbetween | hbetween
    · rcases hbetween with ⟨hmk_val, hkm1_val⟩
      have hmk : m < k :=
        (fmt.normalizedValue_sameExponent_lt_iff_false m k e).mp hmk_val
      have hkm1 : k < m + 1 :=
        (fmt.normalizedValue_sameExponent_lt_iff_false k (m + 1) e).mp hkm1_val
      exact (not_lt_of_ge (Nat.lt_succ_iff.mp hkm1)) hmk
    · rcases hbetween with ⟨hm1k_val, hkm_val⟩
      have hm1k : m + 1 < k :=
        (fmt.normalizedValue_sameExponent_lt_iff_false (m + 1) k e).mp hm1k_val
      have hkm : k < m :=
        (fmt.normalizedValue_sameExponent_lt_iff_false k m e).mp hkm_val
      have hm_lt_k : m < k := lt_trans (Nat.lt_succ_self m) hm1k
      exact (not_lt_of_ge (le_of_lt hkm)) hm_lt_k
  · intro h
    rcases h with hbetween | hbetween
    · rcases hbetween with ⟨hmk_val, hkm1_val⟩
      have hkm : k < m :=
        (fmt.normalizedValue_sameExponent_lt_iff_true m k e).mp hmk_val
      have hm1k : m + 1 < k :=
        (fmt.normalizedValue_sameExponent_lt_iff_true k (m + 1) e).mp hkm1_val
      have hm_lt_k : m < k := lt_trans (Nat.lt_succ_self m) hm1k
      exact (not_lt_of_ge (le_of_lt hkm)) hm_lt_k
    · rcases hbetween with ⟨hm1k_val, hkm_val⟩
      have hkm1 : k < m + 1 :=
        (fmt.normalizedValue_sameExponent_lt_iff_true (m + 1) k e).mp hm1k_val
      have hmk : m < k :=
        (fmt.normalizedValue_sameExponent_lt_iff_true k m e).mp hkm_val
      exact (not_lt_of_ge (Nat.lt_succ_iff.mp hkm1)) hmk
theorem normalizedValue_false_pos {fmt : FloatingPointFormat} {m : ℕ}
    {e : ℤ} (hm : fmt.normalizedMantissa m) :
    0 < fmt.normalizedValue false m e := by
  simpa [normalizedValue, signValue] using
    mul_pos (Nat.cast_pos.mpr (fmt.normalizedMantissa_pos hm))
      (fmt.betaR_zpow_pos (e - (fmt.t : ℤ)))
theorem normalizedValue_true_neg {fmt : FloatingPointFormat} {m : ℕ}
    {e : ℤ} (hm : fmt.normalizedMantissa m) :
    fmt.normalizedValue true m e < 0 := by
  have hpos := fmt.normalizedValue_false_pos (m := m) (e := e) hm
  simpa [fmt.normalizedValue_true_eq_neg_false m e] using
    (neg_lt_zero.mpr hpos : -fmt.normalizedValue false m e < 0)
/-- A nonnegative finite value has a nonnegative sign witness.

The sign witness is only needed for nonzero normalized/subnormal values; zero
is accepted for either supplied sign. -/
theorem finiteSystemWithSign_false_of_finiteSystem_of_nonneg
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.finiteSystem y) (hy_nonneg : 0 ≤ y) :
    fmt.finiteSystemWithSign false y := by
  rcases hy with hy0 | hynz
  · exact Or.inl hy0
  rcases hynz with hnorm | hsub
  · rcases hnorm with ⟨negative, m, e, hm, he, rfl⟩
    cases negative
    · exact Or.inr (Or.inl ⟨m, e, hm, he, rfl⟩)
    · exfalso
      exact (not_lt_of_ge hy_nonneg)
        (fmt.normalizedValue_true_neg (m := m) (e := e) hm)
  · rcases hsub with ⟨negative, m, hm, rfl⟩
    cases negative
    · exact Or.inr (Or.inr ⟨m, hm, rfl⟩)
    · exfalso
      exact (not_lt_of_ge hy_nonneg)
        (fmt.subnormalValue_true_neg (m := m) hm)
/-- A nonpositive finite value has a negative sign witness.

The sign witness is only needed for nonzero normalized/subnormal values; zero
is accepted for either supplied sign. -/
theorem finiteSystemWithSign_true_of_finiteSystem_of_nonpos
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.finiteSystem y) (hy_nonpos : y ≤ 0) :
    fmt.finiteSystemWithSign true y := by
  rcases hy with hy0 | hynz
  · exact Or.inl hy0
  rcases hynz with hnorm | hsub
  · rcases hnorm with ⟨negative, m, e, hm, he, rfl⟩
    cases negative
    · exfalso
      exact (not_lt_of_ge hy_nonpos)
        (fmt.normalizedValue_false_pos (m := m) (e := e) hm)
    · exact Or.inr (Or.inl ⟨m, e, hm, he, rfl⟩)
  · rcases hsub with ⟨negative, m, hm, rfl⟩
    cases negative
    · exfalso
      exact (not_lt_of_ge hy_nonpos)
        (fmt.subnormalValue_false_pos (m := m) hm)
    · exact Or.inr (Or.inr ⟨m, hm, rfl⟩)
theorem normalizedValue_abs_lower_mantissa {fmt : FloatingPointFormat}
    {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    (fmt.minNormalMantissa : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
      |fmt.normalizedValue negative m e| := by
  rw [fmt.normalizedValue_abs negative m e]
  exact mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr hm.1)
    (fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ)))
theorem minNormalMantissa_scale_eq (fmt : FloatingPointFormat) (e : ℤ) :
    (fmt.minNormalMantissa : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) =
      fmt.betaR ^ (e - 1) := by
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  have htcast : ((fmt.t - 1 : ℕ) : ℤ) = (fmt.t : ℤ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt fmt.t_pos), Nat.cast_one]
  calc
    (fmt.minNormalMantissa : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) =
        fmt.betaR ^ (((fmt.t - 1 : ℕ) : ℤ)) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      congr 1
      unfold minNormalMantissa betaR
      rw [zpow_natCast, Nat.cast_pow]
    _ = fmt.betaR ^ (((fmt.t - 1 : ℕ) : ℤ) + (e - (fmt.t : ℤ))) := by
      rw [← zpow_add₀ hbase]
    _ = fmt.betaR ^ (e - 1) := by
      congr 1
      rw [htcast]
      ring
theorem normalizedValue_minNormalMantissa_abs_eq
    (fmt : FloatingPointFormat) (negative : Bool) (e : ℤ) :
    |fmt.normalizedValue negative fmt.minNormalMantissa e| =
      fmt.betaR ^ (e - 1) := by
  rw [fmt.normalizedValue_abs negative fmt.minNormalMantissa e,
    fmt.minNormalMantissa_scale_eq e]
/-- The positive smallest normalized value at exponent `e` is the lower power
endpoint `beta^(e-1)`. -/
theorem normalizedValue_false_minNormalMantissa_eq
    (fmt : FloatingPointFormat) (e : ℤ) :
    fmt.normalizedValue false fmt.minNormalMantissa e =
      fmt.betaR ^ (e - 1) := by
  simpa [normalizedValue, signValue] using fmt.minNormalMantissa_scale_eq e
/-- Shifting one base digit from the exponent into the mantissa preserves the
represented normalized value.  This is the one-step renormalization identity
used by the direct Sterbenz same-exponent branch. -/
theorem normalizedValue_mul_beta_predExponent_eq
    (fmt : FloatingPointFormat) (negative : Bool) (m : ℕ) (e : ℤ) :
    fmt.normalizedValue negative (m * fmt.beta) (e - 1) =
      fmt.normalizedValue negative m e := by
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  have hpow :
      fmt.betaR * fmt.betaR ^ ((e - 1) - (fmt.t : ℤ)) =
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    calc
      fmt.betaR * fmt.betaR ^ ((e - 1) - (fmt.t : ℤ)) =
          fmt.betaR ^ (1 : ℤ) *
            fmt.betaR ^ ((e - 1) - (fmt.t : ℤ)) := by
        rw [zpow_one]
      _ = fmt.betaR ^ ((1 : ℤ) + ((e - 1) - (fmt.t : ℤ))) := by
        rw [← zpow_add₀ hbase]
      _ = fmt.betaR ^ (e - (fmt.t : ℤ)) := by
        congr 1
        ring
  have hpow_cast :
      (fmt.beta : ℝ) * fmt.betaR ^ ((e - 1) - (fmt.t : ℤ)) =
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    simpa [betaR] using hpow
  cases negative <;>
    simp [normalizedValue, signValue, Nat.cast_mul, mul_assoc, hpow_cast]
/-- Multiplying a normalized value by the radix shifts its exponent upward. -/
theorem betaR_mul_normalizedValue_eq_succExponent
    (fmt : FloatingPointFormat) (negative : Bool) (m : ℕ) (e : ℤ) :
    fmt.betaR * fmt.normalizedValue negative m e =
      fmt.normalizedValue negative m (e + 1) := by
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  have hpow :
      fmt.betaR * fmt.betaR ^ (e - (fmt.t : ℤ)) =
        fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) := by
    calc
      fmt.betaR * fmt.betaR ^ (e - (fmt.t : ℤ)) =
          fmt.betaR ^ (1 : ℤ) * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
        rw [zpow_one]
      _ = fmt.betaR ^ ((1 : ℤ) + (e - (fmt.t : ℤ))) := by
        rw [← zpow_add₀ hbase]
      _ = fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) := by
        congr 1
        ring
  cases negative <;>
    simp [normalizedValue, signValue]
    <;> calc
      fmt.betaR * ((m : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) =
          (m : ℝ) * (fmt.betaR * fmt.betaR ^ (e - (fmt.t : ℤ))) := by
        ring
      _ = (m : ℝ) * fmt.betaR ^ (e + 1 - (fmt.t : ℤ)) := by
        rw [hpow]
/-- Shifting any finite number of base digits from the exponent into the
mantissa preserves the represented normalized value. -/
theorem normalizedValue_mul_beta_pow_subExponent_eq
    (fmt : FloatingPointFormat) (negative : Bool) (m shift : ℕ) (e : ℤ) :
    fmt.normalizedValue negative (m * fmt.beta ^ shift)
        (e - (shift : ℤ)) =
      fmt.normalizedValue negative m e := by
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  have hpow :
      fmt.betaR ^ (shift : ℤ) *
          fmt.betaR ^ ((e - (shift : ℤ)) - (fmt.t : ℤ)) =
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    calc
      fmt.betaR ^ (shift : ℤ) *
          fmt.betaR ^ ((e - (shift : ℤ)) - (fmt.t : ℤ)) =
        fmt.betaR ^ ((shift : ℤ) +
          ((e - (shift : ℤ)) - (fmt.t : ℤ))) := by
          rw [← zpow_add₀ hbase]
      _ = fmt.betaR ^ (e - (fmt.t : ℤ)) := by
        congr 1
        ring
  have hpow_cast :
      (fmt.beta : ℝ) ^ shift *
          fmt.betaR ^ ((e - (shift : ℤ)) - (fmt.t : ℤ)) =
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    simpa [betaR, zpow_natCast] using hpow
  cases negative <;>
    simp [normalizedValue, signValue, Nat.cast_mul, Nat.cast_pow,
      hpow_cast, mul_assoc]
/-- If a normalized-style value is shifted down exactly to `emin`, then the
same real value is represented by the corresponding subnormal endpoint
coefficient.  No normalized-mantissa hypothesis is needed: this is just the
radix-shift identity used by the shifted Sterbenz endpoint branch. -/
theorem normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
    (fmt : FloatingPointFormat) (negative : Bool) (m shift : ℕ) (e : ℤ)
    (he : e - (shift : ℤ) = fmt.emin) :
    fmt.normalizedValue negative m e =
      fmt.subnormalValue negative (m * fmt.beta ^ shift) := by
  rw [← fmt.normalizedValue_mul_beta_pow_subExponent_eq
    (negative := negative) (m := m) (shift := shift) (e := e)]
  rw [he]
  rfl
theorem normalizedValue_abs_lower_power {fmt : FloatingPointFormat}
    {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    fmt.betaR ^ (e - 1) ≤ |fmt.normalizedValue negative m e| := by
  rw [← fmt.minNormalMantissa_scale_eq e]
  exact fmt.normalizedValue_abs_lower_mantissa hm
theorem normalizedValue_abs_lt_mantissaBound {fmt : FloatingPointFormat}
    {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    |fmt.normalizedValue negative m e| <
      fmt.betaR ^ fmt.t * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  rw [fmt.normalizedValue_abs negative m e]
  have hmant : (m : ℝ) < fmt.betaR ^ fmt.t := by
    simpa [betaR, Nat.cast_pow] using (Nat.cast_lt.mpr hm.2 : (m : ℝ) < (fmt.beta ^ fmt.t : ℕ))
  exact mul_lt_mul_of_pos_right hmant
    (fmt.betaR_zpow_pos (e - (fmt.t : ℤ)))
theorem mantissaBound_scale_eq (fmt : FloatingPointFormat) (e : ℤ) :
    fmt.betaR ^ fmt.t * fmt.betaR ^ (e - (fmt.t : ℤ)) =
      fmt.betaR ^ e := by
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  calc
    fmt.betaR ^ fmt.t * fmt.betaR ^ (e - (fmt.t : ℤ)) =
        fmt.betaR ^ ((fmt.t : ℤ)) * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      rw [zpow_natCast]
    _ = fmt.betaR ^ ((fmt.t : ℤ) + (e - (fmt.t : ℤ))) := by
      rw [← zpow_add₀ hbase]
    _ = fmt.betaR ^ e := by
      congr 1
      ring
theorem maxNormalMantissa_cast (fmt : FloatingPointFormat) :
    (fmt.maxNormalMantissa : ℝ) = fmt.betaR ^ fmt.t - 1 := by
  unfold maxNormalMantissa betaR
  rw [Nat.cast_sub (Nat.succ_le_of_lt fmt.mantissaBound_pos), Nat.cast_one,
    Nat.cast_pow]
theorem maxNormalMantissa_scale_eq (fmt : FloatingPointFormat) (e : ℤ) :
    (fmt.maxNormalMantissa : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) =
      fmt.betaR ^ e - fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  rw [fmt.maxNormalMantissa_cast]
  calc
    (fmt.betaR ^ fmt.t - 1) * fmt.betaR ^ (e - (fmt.t : ℤ)) =
        fmt.betaR ^ fmt.t * fmt.betaR ^ (e - (fmt.t : ℤ)) -
          fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      ring
    _ = fmt.betaR ^ e - fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      rw [fmt.mantissaBound_scale_eq e]
theorem normalizedValue_maxNormalMantissa_abs_eq_sub
    (fmt : FloatingPointFormat) (negative : Bool) (e : ℤ) :
    |fmt.normalizedValue negative fmt.maxNormalMantissa e| =
      fmt.betaR ^ e - fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  rw [fmt.normalizedValue_abs negative fmt.maxNormalMantissa e,
    fmt.maxNormalMantissa_scale_eq e]
theorem normalizedValue_maxNormalMantissa_abs_eq
    (fmt : FloatingPointFormat) (negative : Bool) (e : ℤ) :
    |fmt.normalizedValue negative fmt.maxNormalMantissa e| =
      fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) := by
  rw [fmt.normalizedValue_maxNormalMantissa_abs_eq_sub negative e]
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  have hsplit :
      fmt.betaR ^ (e - (fmt.t : ℤ)) =
        fmt.betaR ^ e * fmt.betaR ^ (-(fmt.t : ℤ)) := by
    rw [← zpow_add₀ hbase]
    congr 1
  rw [hsplit]
  ring
/-- The positive largest normalized value at exponent `e` is the upper source
endpoint `beta^e * (1 - beta^(-t))`. -/
theorem normalizedValue_false_maxNormalMantissa_eq
    (fmt : FloatingPointFormat) (e : ℤ) :
    fmt.normalizedValue false fmt.maxNormalMantissa e =
      fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) := by
  have hsub := fmt.maxNormalMantissa_scale_eq e
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  have hsplit :
      fmt.betaR ^ (e - (fmt.t : ℤ)) =
        fmt.betaR ^ e * fmt.betaR ^ (-(fmt.t : ℤ)) := by
    rw [← zpow_add₀ hbase]
    congr 1
  calc
    fmt.normalizedValue false fmt.maxNormalMantissa e =
        (fmt.maxNormalMantissa : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      simp [normalizedValue, signValue]
    _ = fmt.betaR ^ e - fmt.betaR ^ (e - (fmt.t : ℤ)) := hsub
    _ = fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) := by
      rw [hsplit]
      ring
theorem normalizedValue_abs_lt_beta_pow {fmt : FloatingPointFormat}
    {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    |fmt.normalizedValue negative m e| < fmt.betaR ^ e := by
  rw [← fmt.mantissaBound_scale_eq e]
  exact fmt.normalizedValue_abs_lt_mantissaBound hm
theorem normalizedValue_abs_between_beta_powers {fmt : FloatingPointFormat}
    {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    fmt.betaR ^ (e - 1) ≤ |fmt.normalizedValue negative m e| ∧
      |fmt.normalizedValue negative m e| < fmt.betaR ^ e :=
  ⟨fmt.normalizedValue_abs_lower_power hm, fmt.normalizedValue_abs_lt_beta_pow hm⟩
theorem normalizedValue_abs_lower_of_exp_ge {fmt : FloatingPointFormat}
    {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) (he : fmt.emin ≤ e) :
    fmt.betaR ^ (fmt.emin - 1) ≤
      |fmt.normalizedValue negative m e| := by
  exact le_trans
    (fmt.betaR_zpow_le_zpow_of_le (by omega : fmt.emin - 1 ≤ e - 1))
    (fmt.normalizedValue_abs_lower_power hm)
theorem normalizedValue_abs_le_maxNormalMantissa_same_exp
    {fmt : FloatingPointFormat} {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    |fmt.normalizedValue negative m e| ≤
      |fmt.normalizedValue false fmt.maxNormalMantissa e| := by
  have hle : m ≤ fmt.maxNormalMantissa := by
    unfold maxNormalMantissa
    exact Nat.le_sub_one_of_lt hm.2
  rw [fmt.normalizedValue_abs negative m e,
    fmt.normalizedValue_abs false fmt.maxNormalMantissa e]
  exact mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr hle)
    (fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ)))
theorem normalizedValue_abs_le_maxNormalMantissa_of_exp_le
    {fmt : FloatingPointFormat} {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) (he : e ≤ fmt.emax) :
    |fmt.normalizedValue negative m e| ≤
      |fmt.normalizedValue false fmt.maxNormalMantissa fmt.emax| := by
  by_cases heq : e = fmt.emax
  · subst e
    exact fmt.normalizedValue_abs_le_maxNormalMantissa_same_exp hm
  · have hlt : e < fmt.emax := lt_of_le_of_ne he heq
    calc
      |fmt.normalizedValue negative m e| ≤ fmt.betaR ^ e :=
        le_of_lt (fmt.normalizedValue_abs_lt_beta_pow hm)
      _ ≤ fmt.betaR ^ (fmt.emax - 1) :=
        fmt.betaR_zpow_le_zpow_of_le (by omega)
      _ = |fmt.normalizedValue false fmt.minNormalMantissa fmt.emax| := by
        rw [fmt.normalizedValue_minNormalMantissa_abs_eq false fmt.emax]
      _ ≤ |fmt.normalizedValue false fmt.maxNormalMantissa fmt.emax| :=
        fmt.normalizedValue_abs_le_maxNormalMantissa_same_exp
          (negative := false) (m := fmt.minNormalMantissa)
          (e := fmt.emax) fmt.minNormalMantissa_normalized
theorem normalizedSystem_abs_lower_bound {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.normalizedSystem y) :
    fmt.betaR ^ (fmt.emin - 1) ≤ |y| := by
  rcases hy with ⟨negative, m, e, hm, he, rfl⟩
  exact fmt.normalizedValue_abs_lower_of_exp_ge hm he.1
theorem normalizedSystem_abs_le_maxNormalMantissa
    {fmt : FloatingPointFormat} {y : ℝ} (hy : fmt.normalizedSystem y) :
    |y| ≤ |fmt.normalizedValue false fmt.maxNormalMantissa fmt.emax| := by
  rcases hy with ⟨negative, m, e, hm, he, rfl⟩
  exact fmt.normalizedValue_abs_le_maxNormalMantissa_of_exp_le hm he.2
theorem normalizedSystem_abs_le_maxFinite_bound
    {fmt : FloatingPointFormat} {y : ℝ} (hy : fmt.normalizedSystem y) :
    |y| ≤ fmt.betaR ^ fmt.emax *
      (1 - fmt.betaR ^ (-(fmt.t : ℤ))) := by
  calc
    |y| ≤ |fmt.normalizedValue false fmt.maxNormalMantissa fmt.emax| :=
      fmt.normalizedSystem_abs_le_maxNormalMantissa hy
    _ = fmt.betaR ^ fmt.emax * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) := by
      rw [fmt.normalizedValue_maxNormalMantissa_abs_eq false fmt.emax]
theorem normalizedSystem_abs_bounds {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.normalizedSystem y) :
    fmt.betaR ^ (fmt.emin - 1) ≤ |y| ∧
      |y| ≤ fmt.betaR ^ fmt.emax *
        (1 - fmt.betaR ^ (-(fmt.t : ℤ))) :=
  ⟨fmt.normalizedSystem_abs_lower_bound hy,
    fmt.normalizedSystem_abs_le_maxFinite_bound hy⟩
/-- The smallest positive normalized magnitude is positive. -/
theorem minNormalMagnitude_pos (fmt : FloatingPointFormat) :
    0 < fmt.minNormalMagnitude := by
  simpa [minNormalMagnitude] using fmt.betaR_zpow_pos (fmt.emin - 1)
/-- The smallest positive subnormal magnitude is positive. -/
theorem minSubnormalMagnitude_pos (fmt : FloatingPointFormat) :
    0 < fmt.minSubnormalMagnitude := by
  simpa [minSubnormalMagnitude] using
    fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ))
/-- The gradual-underflow additive-error bound `u * alpha` is half the
subnormal spacing. -/
theorem unitRoundoff_mul_minNormalMagnitude_eq_half_minSubnormalMagnitude
    (fmt : FloatingPointFormat) :
    fmt.unitRoundoff * fmt.minNormalMagnitude =
      (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  unfold unitRoundoff machineEpsilon minNormalMagnitude minSubnormalMagnitude
  calc
    ((1 / 2 : ℝ) * fmt.betaR ^ (1 - (fmt.t : ℤ))) *
        fmt.betaR ^ (fmt.emin - 1) =
        (1 / 2 : ℝ) *
          (fmt.betaR ^ (1 - (fmt.t : ℤ)) *
            fmt.betaR ^ (fmt.emin - 1)) := by
      ring
    _ = (1 / 2 : ℝ) *
          fmt.betaR ^ ((1 - (fmt.t : ℤ)) + (fmt.emin - 1)) := by
      rw [← zpow_add₀ hbase]
    _ = (1 / 2 : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
      congr 1
      ring_nf
/-- The smallest subnormal magnitude is no larger than the smallest normal
magnitude. -/
theorem minSubnormalMagnitude_le_minNormalMagnitude
    (fmt : FloatingPointFormat) :
    fmt.minSubnormalMagnitude ≤ fmt.minNormalMagnitude := by
  have ht : (1 : ℤ) ≤ (fmt.t : ℤ) := by
    exact_mod_cast fmt.t_pos
  simpa [minSubnormalMagnitude, minNormalMagnitude] using
    fmt.betaR_zpow_le_zpow_of_le (by omega : fmt.emin - (fmt.t : ℤ) ≤ fmt.emin - 1)
/-- The largest finite magnitude is at least the smallest normal magnitude. -/
theorem minNormalMagnitude_le_maxFiniteMagnitude
    (fmt : FloatingPointFormat) :
    fmt.minNormalMagnitude ≤ fmt.maxFiniteMagnitude := by
  have h :=
    fmt.normalizedSystem_abs_le_maxFinite_bound
      (fmt.minNormalMantissa_mem_normalizedSystem false)
  simpa [minNormalMagnitude, maxFiniteMagnitude,
    fmt.normalizedValue_minNormalMantissa_abs_eq false fmt.emin] using h
/-- The largest finite magnitude is nonnegative. -/
theorem maxFiniteMagnitude_nonneg (fmt : FloatingPointFormat) :
    0 ≤ fmt.maxFiniteMagnitude :=
  le_trans (le_of_lt fmt.minNormalMagnitude_pos)
    fmt.minNormalMagnitude_le_maxFiniteMagnitude
/-- The smallest subnormal magnitude is nonnegative. -/
theorem minSubnormalMagnitude_nonneg (fmt : FloatingPointFormat) :
    0 ≤ fmt.minSubnormalMagnitude :=
  le_of_lt fmt.minSubnormalMagnitude_pos
/-- The positive smallest normal magnitude is a normalized finite value. -/
theorem minNormalMagnitude_mem_normalizedSystem
    (fmt : FloatingPointFormat) :
    fmt.normalizedSystem fmt.minNormalMagnitude := by
  simpa [minNormalMagnitude,
    fmt.normalizedValue_false_minNormalMantissa_eq fmt.emin] using
    fmt.minNormalMantissa_mem_normalizedSystem false
/-- The positive largest finite magnitude is a normalized finite value. -/
theorem maxFiniteMagnitude_mem_normalizedSystem
    (fmt : FloatingPointFormat) :
    fmt.normalizedSystem fmt.maxFiniteMagnitude := by
  simpa [maxFiniteMagnitude,
    fmt.normalizedValue_false_maxNormalMantissa_eq fmt.emax] using
    fmt.maxNormalMantissa_mem_normalizedSystem false
/-- The largest finite magnitude is strictly below the next power
`beta^emax`. -/
theorem maxFiniteMagnitude_lt_beta_pow_emax
    (fmt : FloatingPointFormat) :
    fmt.maxFiniteMagnitude < fmt.betaR ^ fmt.emax := by
  have h :=
    fmt.normalizedValue_abs_lt_beta_pow
      (negative := false)
      (m := fmt.maxNormalMantissa) (e := fmt.emax)
      fmt.maxNormalMantissa_normalized
  have hpos :=
    fmt.normalizedValue_false_pos
      (m := fmt.maxNormalMantissa) (e := fmt.emax)
      fmt.maxNormalMantissa_normalized
  rw [abs_of_pos hpos] at h
  simpa [maxFiniteMagnitude,
    fmt.normalizedValue_false_maxNormalMantissa_eq fmt.emax] using h
/-- The negative smallest normal endpoint is a normalized finite value. -/
theorem neg_minNormalMagnitude_mem_normalizedSystem
    (fmt : FloatingPointFormat) :
    fmt.normalizedSystem (-fmt.minNormalMagnitude) := by
  have h := fmt.minNormalMantissa_mem_normalizedSystem true
  rw [fmt.normalizedValue_true_eq_neg_false] at h
  simpa [minNormalMagnitude,
    fmt.normalizedValue_false_minNormalMantissa_eq fmt.emin] using h
/-- The negative largest finite endpoint is a normalized finite value. -/
theorem neg_maxFiniteMagnitude_mem_normalizedSystem
    (fmt : FloatingPointFormat) :
    fmt.normalizedSystem (-fmt.maxFiniteMagnitude) := by
  have h := fmt.maxNormalMantissa_mem_normalizedSystem true
  rw [fmt.normalizedValue_true_eq_neg_false] at h
  simpa [maxFiniteMagnitude,
    fmt.normalizedValue_false_maxNormalMantissa_eq fmt.emax] using h
/-- The positive smallest normal magnitude is finite representable. -/
theorem minNormalMagnitude_mem_finiteSystem
    (fmt : FloatingPointFormat) :
    fmt.finiteSystem fmt.minNormalMagnitude :=
  Or.inr (Or.inl fmt.minNormalMagnitude_mem_normalizedSystem)
/-- The positive smallest normal magnitude is in Higham's unbounded normalized
system `G`. -/
theorem minNormalMagnitude_mem_unboundedNormalizedSystem
    (fmt : FloatingPointFormat) :
    fmt.unboundedNormalizedSystem fmt.minNormalMagnitude :=
  fmt.normalizedSystem_unboundedNormalizedSystem
    fmt.minNormalMagnitude_mem_normalizedSystem
/-- The positive largest finite magnitude is finite representable. -/
theorem maxFiniteMagnitude_mem_finiteSystem
    (fmt : FloatingPointFormat) :
    fmt.finiteSystem fmt.maxFiniteMagnitude :=
  Or.inr (Or.inl fmt.maxFiniteMagnitude_mem_normalizedSystem)
/-- The positive largest finite magnitude is in Higham's unbounded normalized
system `G`. -/
theorem maxFiniteMagnitude_mem_unboundedNormalizedSystem
    (fmt : FloatingPointFormat) :
    fmt.unboundedNormalizedSystem fmt.maxFiniteMagnitude :=
  fmt.normalizedSystem_unboundedNormalizedSystem
    fmt.maxFiniteMagnitude_mem_normalizedSystem
/-- The negative smallest normal endpoint is finite representable. -/
theorem neg_minNormalMagnitude_mem_finiteSystem
    (fmt : FloatingPointFormat) :
    fmt.finiteSystem (-fmt.minNormalMagnitude) :=
  Or.inr (Or.inl fmt.neg_minNormalMagnitude_mem_normalizedSystem)
/-- The negative smallest normal endpoint is in Higham's unbounded normalized
system `G`. -/
theorem neg_minNormalMagnitude_mem_unboundedNormalizedSystem
    (fmt : FloatingPointFormat) :
    fmt.unboundedNormalizedSystem (-fmt.minNormalMagnitude) :=
  fmt.normalizedSystem_unboundedNormalizedSystem
    fmt.neg_minNormalMagnitude_mem_normalizedSystem
/-- The negative largest finite endpoint is finite representable. -/
theorem neg_maxFiniteMagnitude_mem_finiteSystem
    (fmt : FloatingPointFormat) :
    fmt.finiteSystem (-fmt.maxFiniteMagnitude) :=
  Or.inr (Or.inl fmt.neg_maxFiniteMagnitude_mem_normalizedSystem)
/-- The negative largest finite endpoint is in Higham's unbounded normalized
system `G`. -/
theorem neg_maxFiniteMagnitude_mem_unboundedNormalizedSystem
    (fmt : FloatingPointFormat) :
    fmt.unboundedNormalizedSystem (-fmt.maxFiniteMagnitude) :=
  fmt.normalizedSystem_unboundedNormalizedSystem
    fmt.neg_maxFiniteMagnitude_mem_normalizedSystem
/-- Normalized finite values lie in the source-facing finite normal range. -/
theorem normalizedSystem_finiteNormalRange
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.normalizedSystem y) :
    fmt.finiteNormalRange y := by
  rcases fmt.normalizedSystem_abs_bounds hy with ⟨hlo, hhi⟩
  exact ⟨by simpa [minNormalMagnitude] using hlo,
    by simpa [maxFiniteMagnitude] using hhi⟩
/-- An unbounded normalized value whose magnitude lies in the finite normal
range is actually a bounded normalized finite value. -/
theorem unboundedNormalizedSystem_normalizedSystem_of_finiteNormalRange
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.unboundedNormalizedSystem y)
    (hrange : fmt.finiteNormalRange y) :
    fmt.normalizedSystem y := by
  rcases hy with ⟨negative, m, e, hm, rfl⟩
  have hemin : fmt.emin ≤ e := by
    by_contra hnot
    have he_lt : e < fmt.emin := lt_of_not_ge hnot
    have hpow_le :
        fmt.betaR ^ e ≤ fmt.betaR ^ (fmt.emin - 1) :=
      fmt.betaR_zpow_le_zpow_of_le (by omega : e ≤ fmt.emin - 1)
    have hlt :
        |fmt.normalizedValue negative m e| < fmt.minNormalMagnitude := by
      calc
        |fmt.normalizedValue negative m e| < fmt.betaR ^ e :=
          fmt.normalizedValue_abs_lt_beta_pow hm
        _ ≤ fmt.betaR ^ (fmt.emin - 1) := hpow_le
        _ = fmt.minNormalMagnitude := by rfl
    exact not_lt_of_ge hrange.1 hlt
  have hemax : e ≤ fmt.emax := by
    by_contra hnot
    have hlt : fmt.emax < e := lt_of_not_ge hnot
    have hpow_le :
        fmt.betaR ^ fmt.emax ≤ fmt.betaR ^ (e - 1) :=
      fmt.betaR_zpow_le_zpow_of_le (by omega : fmt.emax ≤ e - 1)
    have hmax_lt :
        fmt.maxFiniteMagnitude <
          |fmt.normalizedValue negative m e| := by
      exact lt_of_lt_of_le
        (lt_of_lt_of_le fmt.maxFiniteMagnitude_lt_beta_pow_emax hpow_le)
        (fmt.normalizedValue_abs_lower_power hm)
    exact not_lt_of_ge hrange.2 hmax_lt
  exact ⟨negative, m, e, hm, ⟨hemin, hemax⟩, rfl⟩
/-- Normalized finite values are not in the source-facing underflow range. -/
theorem normalizedSystem_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.normalizedSystem y) :
    ¬ fmt.finiteUnderflowRange y :=
  not_lt_of_ge (fmt.normalizedSystem_finiteNormalRange hy).1
/-- Normalized finite values are not in the source-facing overflow range. -/
theorem normalizedSystem_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.normalizedSystem y) :
    ¬ fmt.finiteOverflowRange y :=
  not_lt_of_ge (fmt.normalizedSystem_finiteNormalRange hy).2
/-- Normalized finite values have magnitude at least the smallest subnormal. -/
theorem normalizedSystem_abs_ge_minSubnormalMagnitude
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.normalizedSystem y) :
    fmt.minSubnormalMagnitude ≤ |y| :=
  le_trans fmt.minSubnormalMagnitude_le_minNormalMagnitude
    (fmt.normalizedSystem_finiteNormalRange hy).1
theorem normalizedExponentRepresentation_abs_lower_power
    {fmt : FloatingPointFormat} {y : ℝ} {e : ℤ}
    (h : fmt.normalizedExponentRepresentation y e) :
    fmt.betaR ^ (e - 1) ≤ |y| := by
  rcases h with ⟨negative, m, hm, _he, rfl⟩
  exact fmt.normalizedValue_abs_lower_power hm
theorem normalizedExponentRepresentation_abs_lt_beta_pow
    {fmt : FloatingPointFormat} {y : ℝ} {e : ℤ}
    (h : fmt.normalizedExponentRepresentation y e) :
    |y| < fmt.betaR ^ e := by
  rcases h with ⟨negative, m, hm, _he, rfl⟩
  exact fmt.normalizedValue_abs_lt_beta_pow hm
theorem betaR_zpow_add_one_le_of_two_mul
    (fmt : FloatingPointFormat) (e : ℤ) :
    2 * fmt.betaR ^ e ≤ fmt.betaR ^ (e + 1) := by
  have hb : (2 : ℝ) ≤ fmt.betaR := by
    unfold betaR
    exact_mod_cast fmt.beta_ge_two
  have hpow_nonneg : 0 ≤ fmt.betaR ^ e :=
    fmt.betaR_zpow_nonneg e
  have hmul : 2 * fmt.betaR ^ e ≤ fmt.betaR * fmt.betaR ^ e :=
    mul_le_mul_of_nonneg_right hb hpow_nonneg
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  calc
    2 * fmt.betaR ^ e ≤ fmt.betaR * fmt.betaR ^ e := hmul
    _ = fmt.betaR ^ (1 : ℤ) * fmt.betaR ^ e := by
      rw [zpow_one]
    _ = fmt.betaR ^ ((1 : ℤ) + e) := by
      rw [← zpow_add₀ hbase]
    _ = fmt.betaR ^ (e + 1) := by
      congr 1
      omega
theorem normalizedExponentRepresentation_sub_exponent_gap_le_one
    {fmt : FloatingPointFormat} {x y : ℝ} {ex ey ez : ℤ}
    (hx : fmt.normalizedExponentRepresentation x ex)
    (hy : fmt.normalizedExponentRepresentation y ey)
    (hz : fmt.normalizedExponentRepresentation (x - y) ez)
    (hcond : ez < min ex ey) :
    ex ≤ ey + 1 ∧ ey ≤ ex + 1 := by
  have hx_upper : |x| < fmt.betaR ^ ex :=
    fmt.normalizedExponentRepresentation_abs_lt_beta_pow hx
  have hy_upper : |y| < fmt.betaR ^ ey :=
    fmt.normalizedExponentRepresentation_abs_lt_beta_pow hy
  have hx_lower : fmt.betaR ^ (ex - 1) ≤ |x| :=
    fmt.normalizedExponentRepresentation_abs_lower_power hx
  have hy_lower : fmt.betaR ^ (ey - 1) ≤ |y| :=
    fmt.normalizedExponentRepresentation_abs_lower_power hy
  have hz_upper : |x - y| < fmt.betaR ^ ez :=
    fmt.normalizedExponentRepresentation_abs_lt_beta_pow hz
  have hlt_ex : ez < ex := lt_of_lt_of_le hcond (min_le_left ex ey)
  have hlt_ey : ez < ey := lt_of_lt_of_le hcond (min_le_right ex ey)
  have hz_lt_ex : |x - y| < fmt.betaR ^ ex :=
    lt_of_lt_of_le hz_upper
      (fmt.betaR_zpow_le_zpow_of_le (le_of_lt hlt_ex))
  have hz_lt_ey : |x - y| < fmt.betaR ^ ey :=
    lt_of_lt_of_le hz_upper
      (fmt.betaR_zpow_le_zpow_of_le (le_of_lt hlt_ey))
  constructor
  · by_contra hnot
    have hgap : ey + 1 < ex := by omega
    have hx_big : fmt.betaR ^ (ey + 1) ≤ |x| := by
      exact le_trans
        (fmt.betaR_zpow_le_zpow_of_le (by omega : ey + 1 ≤ ex - 1))
        hx_lower
    have hx_two : 2 * fmt.betaR ^ ey ≤ |x| :=
      le_trans (fmt.betaR_zpow_add_one_le_of_two_mul ey) hx_big
    have hsum_lt :
        fmt.betaR ^ ey + |y| < fmt.betaR ^ ey + fmt.betaR ^ ey := by
      simpa [add_comm] using add_lt_add_right hy_upper (fmt.betaR ^ ey)
    have htwo_eq : 2 * fmt.betaR ^ ey = fmt.betaR ^ ey + fmt.betaR ^ ey := by
      ring
    have hsum_le_x : fmt.betaR ^ ey + fmt.betaR ^ ey ≤ |x| := by
      simpa [htwo_eq] using hx_two
    have hdiff_lt : fmt.betaR ^ ey < |x| - |y| := by
      linarith
    have htriangle : |x| - |y| ≤ |x - y| := by
      exact abs_sub_abs_le_abs_sub x y
    have hlarge : fmt.betaR ^ ey < |x - y| := lt_of_lt_of_le hdiff_lt htriangle
    exact not_lt_of_ge (le_of_lt hlarge) hz_lt_ey
  · by_contra hnot
    have hgap : ex + 1 < ey := by omega
    have hy_big : fmt.betaR ^ (ex + 1) ≤ |y| := by
      exact le_trans
        (fmt.betaR_zpow_le_zpow_of_le (by omega : ex + 1 ≤ ey - 1))
        hy_lower
    have hy_two : 2 * fmt.betaR ^ ex ≤ |y| :=
      le_trans (fmt.betaR_zpow_add_one_le_of_two_mul ex) hy_big
    have hsum_lt :
        fmt.betaR ^ ex + |x| < fmt.betaR ^ ex + fmt.betaR ^ ex := by
      simpa [add_comm] using add_lt_add_right hx_upper (fmt.betaR ^ ex)
    have htwo_eq : 2 * fmt.betaR ^ ex = fmt.betaR ^ ex + fmt.betaR ^ ex := by
      ring
    have hsum_le_y : fmt.betaR ^ ex + fmt.betaR ^ ex ≤ |y| := by
      simpa [htwo_eq] using hy_two
    have hdiff_lt : fmt.betaR ^ ex < |y| - |x| := by
      linarith
    have htriangle : |y| - |x| ≤ |x - y| := by
      have htri_yx : |y| - |x| ≤ |y - x| := abs_sub_abs_le_abs_sub y x
      have htri_xy : |y| - |x| ≤ |x - y| := by
        simpa [abs_sub_comm] using htri_yx
      exact htri_xy
    have hlarge : fmt.betaR ^ ex < |x - y| := lt_of_lt_of_le hdiff_lt htriangle
    exact not_lt_of_ge (le_of_lt hlarge) hz_lt_ex
/-- Raw aligned subtraction value when two normalized mantissas have the same
exponent and sign.  This is the exact arithmetic identity before any
renormalization or rounding decision. -/
def alignedSameExponentSubtractionValue
    (fmt : FloatingPointFormat) (negative : Bool) (m n : ℕ) (e : ℤ) : ℝ :=
  fmt.signValue negative * ((m : ℝ) - (n : ℝ)) *
    fmt.betaR ^ (e - (fmt.t : ℤ))

end FloatingPointFormat

end

end NumStability
