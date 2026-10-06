import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.Error.Measures.ScalarDefinitions
import NumStability.Analysis.Error.Measures.ScalarProperties
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

/-- Normwise relative error for vector approximations, parameterized by the
chosen norm.  This captures Higham's `‖x - xhat‖ / ‖x‖` convention without
committing this foundational file to a particular norm implementation. -/
noncomputable def normwiseRelError (n : ℕ) (norm : (Fin n → ℝ) → ℝ)
    (computed exact : Fin n → ℝ) : ℝ :=
  norm (fun i => exact i - computed i) / norm exact

/-- Componentwise relative error bound for a computed vector approximation.

    Asserts that every component's relative error is at most ε:
      ∀ i, |computed_i - exact_i| / |exact_i| ≤ ε

    This is the form most directly usable in error-bound lemmas.
    Requires all exact components to be nonzero; the caller must enforce this. -/
def compRelErrorBounded (n : ℕ) (computed exact : Fin n → ℝ) (ε : ℝ) : Prop :=
  ∀ i : Fin n, relError (computed i) (exact i) ≤ ε

/-- Componentwise relative error as Higham's finite maximum
`max_i |x_i - xhat_i| / |x_i|`.  The positive-dimension hypothesis supplies
the nonempty index set needed by `Finset.sup'`. -/
noncomputable def compRelError (n : ℕ) (computed exact : Fin n → ℝ)
    (hn : 0 < n) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin n))
    (by exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩)
    (fun i => relError (computed i) (exact i))

/-- Each component relative error is bounded by the componentwise maximum. -/
theorem relError_le_compRelError (n : ℕ) (computed exact : Fin n → ℝ)
    (hn : 0 < n) (i : Fin n) :
    relError (computed i) (exact i) ≤ compRelError n computed exact hn := by
  unfold compRelError
  exact Finset.le_sup' (fun i => relError (computed i) (exact i)) (Finset.mem_univ i)

/-- The componentwise maximum is the least scalar that bounds every component. -/
theorem compRelError_le_iff (n : ℕ) (computed exact : Fin n → ℝ)
    (hn : 0 < n) (ε : ℝ) :
    compRelError n computed exact hn ≤ ε ↔ compRelErrorBounded n computed exact ε := by
  constructor
  · intro h i
    exact le_trans (relError_le_compRelError n computed exact hn i) h
  · intro h
    unfold compRelError
    exact Finset.sup'_le _ _ (fun i _ => h i)

/-- Componentwise relative error is nonnegative in positive dimension. -/
theorem compRelError_nonneg (n : ℕ) (computed exact : Fin n → ℝ)
    (hn : 0 < n) :
    0 ≤ compRelError n computed exact hn := by
  have h0 : 0 ≤ relError (computed ⟨0, hn⟩) (exact ⟨0, hn⟩) :=
    relError_nonneg _ _
  exact le_trans h0 (relError_le_compRelError n computed exact hn ⟨0, hn⟩)

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
