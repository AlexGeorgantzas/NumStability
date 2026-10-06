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































































































































/-- Absolute error scales by the magnitude of the common scalar. -/
theorem absError_smul (α computed exact : ℝ) :
    absError (α * computed) (α * exact) = |α| * absError computed exact := by
  unfold absError
  have hdiff : α * computed - α * exact = α * (computed - exact) := by
    ring
  rw [hdiff, abs_mul]

/-- Higham §1.2: relative error is scale independent when the scale is nonzero. -/
theorem relError_smul (α computed exact : ℝ) (hα : α ≠ 0) :
    relError (α * computed) (α * exact) = relError computed exact := by
  unfold relError
  have hdiff : α * computed - α * exact = α * (computed - exact) := by
    ring
  rw [hdiff, abs_mul, abs_mul]
  have hαabs : |α| ≠ 0 := abs_ne_zero.mpr hα
  by_cases hex : |exact| = 0
  · simp [hex]
  · field_simp [hαabs, hex]

/-- Higham §1.2: if `computed = exact * (1 + ρ)`, then relative error is `|ρ|`. -/
theorem relError_eq_abs_of_signedRelErrorWitness {computed exact ρ : ℝ}
    (hexact : relErrorDefined exact)
    (hρ : signedRelErrorWitness computed exact ρ) :
    relError computed exact = |ρ| := by
  unfold relError signedRelErrorWitness at *
  rw [hρ]
  have hden : |exact| ≠ 0 := abs_ne_zero.mpr hexact
  have hdiff : exact * (1 + ρ) - exact = exact * ρ := by
    ring
  rw [hdiff, abs_mul]
  field_simp [hden]

/-- Higham §1.2 converse: every nonzero exact value admits a signed relative-error
witness whose magnitude equals the relative error. -/
theorem exists_signedRelErrorWitness_of_relErrorDefined (computed exact : ℝ)
    (hexact : relErrorDefined exact) :
    ∃ ρ : ℝ,
      signedRelErrorWitness computed exact ρ ∧
      relError computed exact = |ρ| := by
  refine ⟨computed / exact - 1, ?_, ?_⟩
  · unfold signedRelErrorWitness
    have hcalc : exact * (1 + (computed / exact - 1)) = computed := by
      calc
        exact * (1 + (computed / exact - 1)) = exact * (computed / exact) := by ring
        _ = computed := by
          rw [mul_comm]
          exact div_mul_cancel₀ computed hexact
    exact hcalc.symm
  · apply relError_eq_abs_of_signedRelErrorWitness hexact
    unfold signedRelErrorWitness
    have hcalc : exact * (1 + (computed / exact - 1)) = computed := by
      calc
        exact * (1 + (computed / exact - 1)) = exact * (computed / exact) := by ring
        _ = computed := by
          rw [mul_comm]
          exact div_mul_cancel₀ computed hexact
    exact hcalc.symm































































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
