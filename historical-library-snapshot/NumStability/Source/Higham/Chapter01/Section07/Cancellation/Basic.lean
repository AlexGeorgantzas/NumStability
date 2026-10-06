import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.Error.Measures.ScalarDefinitions
import NumStability.FloatingPoint.Model

-- Error.lean









namespace NumStability

/-!
# Floating-Point Error Measures

Following Higham, "Accuracy and Stability of Numerical Algorithms", Ch. 1.
We define absolute error and relative error as the standard measures of
floating-point approximation quality.
-/

-- ============================================================
-- §1.2  Error measures
-- ============================================================















































-- ============================================================
-- §2.4  No-guard digit model
-- ============================================================




































































































































































































namespace NoGuardFPModel



















































































































end NoGuardFPModel
























































































































































































































































-- ============================================================
-- §1.2  Componentwise relative error (for vectors)
-- ============================================================





















































-- ============================================================
-- §1.3  Sources of errors
-- ============================================================








namespace ErrorSource










end ErrorSource

-- ============================================================
-- §1.4  Precision versus accuracy
-- ============================================================








namespace AccuracyMeasure














end AccuracyMeasure







namespace PrecisionMeasure










end PrecisionMeasure















































-- ============================================================
-- §1.7  Cancellation
-- ============================================================

/-- Higham §1.7 cancellation algebra: subtracting two relatively perturbed
quantities leaves the exact subtraction error `a * δa - b * δb`. -/
theorem subtract_perturbed_error_eq (a b δa δb : ℝ) :
    (a * (1 + δa) - b * (1 + δb)) - (a - b) = a * δa - b * δb := by
  ring

/-- Absolute error bound for cancellation after relative perturbations of the
two inputs.  This is the elementary inequality behind the amplification factor
`(|a| + |b|) / |a - b|` when `a` and `b` are close. -/
theorem abs_subtract_perturbed_error_le (a b δa δb : ℝ) :
    |(a * (1 + δa) - b * (1 + δb)) - (a - b)| ≤
      |a| * |δa| + |b| * |δb| := by
  rw [subtract_perturbed_error_eq]
  have htri := abs_add_le (a * δa) (-(b * δb))
  simpa [sub_eq_add_neg, abs_mul, abs_neg] using htri

/-- If both inputs to a subtraction carry relative perturbations bounded by
`ε`, then the absolute subtraction error is bounded by
`ε * (|a| + |b|)`. -/
theorem abs_subtract_perturbed_error_le_eps (a b δa δb ε : ℝ)
    (hδa : |δa| ≤ ε) (hδb : |δb| ≤ ε) :
    |(a * (1 + δa) - b * (1 + δb)) - (a - b)| ≤
      ε * (|a| + |b|) := by
  calc
    |(a * (1 + δa) - b * (1 + δb)) - (a - b)|
        ≤ |a| * |δa| + |b| * |δb| :=
          abs_subtract_perturbed_error_le a b δa δb
    _ ≤ |a| * ε + |b| * ε :=
          add_le_add
            (mul_le_mul_of_nonneg_left hδa (abs_nonneg a))
            (mul_le_mul_of_nonneg_left hδb (abs_nonneg b))
    _ = ε * (|a| + |b|) := by
          ring

/-- Higham §1.7 cancellation amplification in relative-error form.  When
`a - b` is small compared with `|a| + |b|`, the input relative perturbation
bound `ε` is multiplied by the large factor
`(|a| + |b|) / |a - b|`. -/
theorem relError_subtract_perturbed_le_eps_amp (a b δa δb ε : ℝ)
    (hab : a - b ≠ 0) (hδa : |δa| ≤ ε) (hδb : |δb| ≤ ε) :
    relError (a * (1 + δa) - b * (1 + δb)) (a - b) ≤
      ε * (|a| + |b|) / |a - b| := by
  unfold relError
  have hden_pos : 0 < |a - b| := abs_pos.mpr hab
  exact div_le_div_of_nonneg_right
    (abs_subtract_perturbed_error_le_eps a b δa δb ε hδa hδb)
    hden_pos.le

end NumStability
