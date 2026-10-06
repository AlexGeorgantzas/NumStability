import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic.Format

namespace NumStability

/-!
# Environment

Extracted without change from FloatingPointArithmetic.
-/

noncomputable section

namespace FloatingPointFormat

/-- Higham's note on MATLAB's permanent variable `eps` for IEEE double
arithmetic: it is the machine epsilon, not the unit roundoff. -/
def matlabIeeeDoubleEps : ℝ :=
  ieeeDoubleFormat.machineEpsilon
/-- Higham's Fortran `EPSILON` convention for a real kind represented by
`fmt`: it returns the kind's machine epsilon. -/
def fortranEpsilon (fmt : FloatingPointFormat) : ℝ :=
  fmt.machineEpsilon
theorem matlabIeeeDoubleEps_eq_ieeeDoubleFormat_machineEpsilon :
    matlabIeeeDoubleEps = ieeeDoubleFormat.machineEpsilon :=
  rfl
theorem matlabIeeeDoubleEps_eq_two_zpow_neg52 :
    matlabIeeeDoubleEps = (2 : ℝ) ^ (-52 : ℤ) := by
  simpa [matlabIeeeDoubleEps] using ieeeDoubleFormat_machineEpsilon
theorem matlabIeeeDoubleEps_eq_two_mul_ieeeDoubleFormat_unitRoundoff :
    matlabIeeeDoubleEps = 2 * ieeeDoubleFormat.unitRoundoff := by
  rw [matlabIeeeDoubleEps, unitRoundoff]
  ring
theorem fortranEpsilon_eq_machineEpsilon (fmt : FloatingPointFormat) :
    fmt.fortranEpsilon = fmt.machineEpsilon :=
  rfl
theorem fortranEpsilon_eq_two_mul_unitRoundoff
    (fmt : FloatingPointFormat) :
    fmt.fortranEpsilon = 2 * fmt.unitRoundoff := by
  rw [fortranEpsilon, unitRoundoff]
  ring
theorem ieeeSingleFormat_fortranEpsilon :
    ieeeSingleFormat.fortranEpsilon = (2 : ℝ) ^ (-23 : ℤ) := by
  simpa [fortranEpsilon] using ieeeSingleFormat_machineEpsilon
theorem ieeeDoubleFormat_fortranEpsilon :
    ieeeDoubleFormat.fortranEpsilon = (2 : ℝ) ^ (-52 : ℤ) := by
  simpa [fortranEpsilon] using ieeeDoubleFormat_machineEpsilon
theorem matlabIeeeDoubleEps_eq_ieeeDoubleFormat_fortranEpsilon :
    matlabIeeeDoubleEps = ieeeDoubleFormat.fortranEpsilon :=
  rfl
theorem fortranEpsilon_pos (fmt : FloatingPointFormat) :
    0 < fmt.fortranEpsilon := by
  rw [fortranEpsilon]
  exact fmt.machineEpsilon_pos
/-- Higham Chapter 2, Problem 2.17 core range fact: doubling the largest
positive finite value lies in the source-facing overflow range.  The
mode-specific IEEE value is supplied by `ieeeOverflowValue`. -/
theorem problem2_17_two_mul_maxFiniteMagnitude_finiteOverflowRange
    (fmt : FloatingPointFormat) :
    fmt.finiteOverflowRange (2 * fmt.maxFiniteMagnitude) := by
  have hmax_pos : 0 < fmt.maxFiniteMagnitude :=
    lt_of_lt_of_le fmt.minNormalMagnitude_pos
      fmt.minNormalMagnitude_le_maxFiniteMagnitude
  have htwo_pos : 0 < 2 * fmt.maxFiniteMagnitude := by
    linarith
  rw [finiteOverflowRange, abs_of_pos htwo_pos]
  linarith

end FloatingPointFormat

end

end NumStability
