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

/-- Absolute error is nonnegative. -/
theorem absError_nonneg (computed exact : ℝ) :
    0 ≤ absError computed exact := by
  exact abs_nonneg _

/-- Relative error is nonnegative under Lean's totalized real division. -/
theorem relError_nonneg (computed exact : ℝ) :
    0 ≤ relError computed exact := by
  unfold relError
  exact div_nonneg (abs_nonneg _) (abs_nonneg _)

/-- Problem 1.1's alternate relative error, using the computed approximation
as denominator: `|computed - exact| / |computed|`. -/
noncomputable def relErrorComputedDenom (computed exact : ℝ) : ℝ :=
  |computed - exact| / |computed|

/-- The alternate denominator convention is the standard relative error with
the two arguments swapped. -/
theorem relErrorComputedDenom_eq_relError_swap (computed exact : ℝ) :
    relErrorComputedDenom computed exact = relError exact computed := by
  unfold relErrorComputedDenom relError
  rw [abs_sub_comm]

/-- Higham Problem 1.1: the computed-denominator relative error is bounded
below by `E/(1+E)`, where `E` is the standard exact-denominator relative
error. -/
theorem relErrorComputedDenom_lower_bound_from_relError
    (computed exact : ℝ) (hexact : exact ≠ 0) (hcomputed : computed ≠ 0) :
    relError computed exact / (1 + relError computed exact) ≤
      relErrorComputedDenom computed exact := by
  unfold relError relErrorComputedDenom
  have ha : 0 < |exact| := abs_pos.mpr hexact
  have hb : 0 < |computed| := abs_pos.mpr hcomputed
  have hleft :
      |computed - exact| / |exact| / (1 + |computed - exact| / |exact|)
        = |computed - exact| / (|exact| + |computed - exact|) := by
    field_simp [ne_of_gt ha]
  rw [hleft]
  have htri : |computed| ≤ |exact| + |computed - exact| := by
    have hsum : exact + (computed - exact) = computed := by ring
    calc
      |computed| = |exact + (computed - exact)| := by rw [hsum]
      _ ≤ |exact| + |computed - exact| := abs_add_le exact (computed - exact)
  exact div_le_div_of_nonneg_left (abs_nonneg _) hb htri

/-- Higham Problem 1.1: if the exact-denominator relative error is less than
one, then the computed-denominator relative error is bounded above by
`E/(1-E)`. -/
theorem relErrorComputedDenom_upper_bound_from_relError
    (computed exact : ℝ) (hexact : exact ≠ 0)
    (hsmall : relError computed exact < 1) :
    relErrorComputedDenom computed exact ≤
      relError computed exact / (1 - relError computed exact) := by
  unfold relError relErrorComputedDenom at *
  have ha : 0 < |exact| := abs_pos.mpr hexact
  have hd_lt_a : |computed - exact| < |exact| := (div_lt_one ha).mp hsmall
  have hdenpos : 0 < |exact| - |computed - exact| := by linarith
  have hcomputed : computed ≠ 0 := by
    intro hc
    have hd_eq : |computed - exact| = |exact| := by
      simp [hc]
    linarith
  have hright :
      |computed - exact| / |exact| / (1 - |computed - exact| / |exact|)
        = |computed - exact| / (|exact| - |computed - exact|) := by
    field_simp [ne_of_gt ha, ne_of_gt hdenpos]
  rw [hright]
  have htri : |exact| ≤ |computed| + |computed - exact| := by
    have hsum : computed + (exact - computed) = exact := by ring
    calc
      |exact| = |computed + (exact - computed)| := by rw [hsum]
      _ ≤ |computed| + |exact - computed| := abs_add_le computed (exact - computed)
      _ = |computed| + |computed - exact| := by rw [abs_sub_comm exact computed]
  have hlow : |exact| - |computed - exact| ≤ |computed| := by linarith
  exact div_le_div_of_nonneg_left (abs_nonneg _) hdenpos hlow

/-- The standard exact-denominator relative error is bounded below by the
computed-denominator error divided by `1 +` that error. -/
theorem relError_lower_bound_from_computedDenom
    (computed exact : ℝ) (hexact : exact ≠ 0) (hcomputed : computed ≠ 0) :
    relErrorComputedDenom computed exact / (1 + relErrorComputedDenom computed exact) ≤
      relError computed exact := by
  have h :=
    relErrorComputedDenom_lower_bound_from_relError exact computed hcomputed hexact
  simpa [relErrorComputedDenom_eq_relError_swap, relErrorComputedDenom, relError,
    abs_sub_comm] using h

/-- If the computed-denominator relative error is less than one, then the
standard exact-denominator relative error is bounded above by
`Etilde/(1-Etilde)`. -/
theorem relError_upper_bound_from_computedDenom
    (computed exact : ℝ) (hcomputed : computed ≠ 0)
    (hsmall : relErrorComputedDenom computed exact < 1) :
    relError computed exact ≤
      relErrorComputedDenom computed exact /
        (1 - relErrorComputedDenom computed exact) := by
  have hsmall' : relError exact computed < 1 := by
    simpa [relErrorComputedDenom_eq_relError_swap] using hsmall
  have h := relErrorComputedDenom_upper_bound_from_relError exact computed hcomputed hsmall'
  simpa [relErrorComputedDenom_eq_relError_swap, relErrorComputedDenom, relError,
    abs_sub_comm] using h


















































































































































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

















































end NumStability
