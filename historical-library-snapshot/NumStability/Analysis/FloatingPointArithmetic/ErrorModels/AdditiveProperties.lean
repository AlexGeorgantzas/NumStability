import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.Error.Measures.ScalarDefinitions
import NumStability.Analysis.FloatingPointArithmetic.ErrorModels.Additive
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


























































































































































































/-- A standard relative-error witness is the normal branch of the additive
underflow model with additive term `η = 0`. -/
theorem additiveErrorWitness_of_signedRelErrorWitness
    {computed exact δ : ℝ}
    (h : signedRelErrorWitness computed exact δ) :
    additiveErrorWitness computed exact δ 0 := by
  simpa [additiveErrorWitness, signedRelErrorWitness] using h

/-- Non-strict additive model, normal branch: a relative-error witness with
`|δ| < u` gives equation (2.8) with `η = 0`. -/
theorem additiveUnderflowModelWitness_normal_branch
    {computed exact u ηBound δ : ℝ}
    (hδ : |δ| < u) (hηBound : 0 ≤ ηBound)
    (h : signedRelErrorWitness computed exact δ) :
    additiveUnderflowModelWitness computed exact u ηBound δ 0 := by
  refine ⟨additiveErrorWitness_of_signedRelErrorWitness h, hδ, ?_, ?_⟩
  · simpa using hηBound
  · exact Or.inr rfl

/-- Strict additive model, normal branch: a relative-error witness with
`|δ| < u` gives equation (2.8) with `η = 0`, provided the additive bound is
positive. -/
theorem strictAdditiveUnderflowModelWitness_normal_branch
    {computed exact u ηBound δ : ℝ}
    (hδ : |δ| < u) (hηBound : 0 < ηBound)
    (h : signedRelErrorWitness computed exact δ) :
    strictAdditiveUnderflowModelWitness computed exact u ηBound δ 0 := by
  refine ⟨additiveErrorWitness_of_signedRelErrorWitness h, hδ, ?_, ?_⟩
  · simpa using hηBound
  · exact Or.inr rfl

/-- The underflow branch of equation (2.8) writes the whole absolute error as
the additive term, with `δ = 0`. -/
theorem additiveErrorWitness_underflow_branch
    (computed exact : ℝ) :
    additiveErrorWitness computed exact 0 (computed - exact) := by
  unfold additiveErrorWitness
  ring

/-- Non-strict additive model, underflow branch: an absolute-error bound gives
equation (2.8) with `δ = 0` and `η = computed - exact`. -/
theorem additiveUnderflowModelWitness_underflow_branch_of_absError_le
    {computed exact u ηBound : ℝ}
    (hu : 0 < u) (habs : absError computed exact ≤ ηBound) :
    additiveUnderflowModelWitness computed exact u ηBound 0 (computed - exact) := by
  refine ⟨additiveErrorWitness_underflow_branch computed exact, ?_, ?_, ?_⟩
  · simpa using hu
  · simpa [absError] using habs
  · exact Or.inl rfl

/-- Strict additive model, underflow branch: a strict absolute-error bound gives
equation (2.8) with `δ = 0` and `η = computed - exact`. -/
theorem strictAdditiveUnderflowModelWitness_underflow_branch_of_absError_lt
    {computed exact u ηBound : ℝ}
    (hu : 0 < u) (habs : absError computed exact < ηBound) :
    strictAdditiveUnderflowModelWitness computed exact u ηBound 0
      (computed - exact) := by
  refine ⟨additiveErrorWitness_underflow_branch computed exact, ?_, ?_, ?_⟩
  · simpa using hu
  · simpa [absError] using habs
  · exact Or.inl rfl

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
