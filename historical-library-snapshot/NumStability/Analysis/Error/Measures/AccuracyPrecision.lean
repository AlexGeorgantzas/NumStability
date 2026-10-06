import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.Error.Measures.ScalarDefinitions
import NumStability.Analysis.Error.Measures.ScalarWitnesses
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

/-- Higham §1.4's two standard scalar accuracy measures for an approximate
quantity: absolute error and relative error. -/
inductive AccuracyMeasure where
  | absolute
  | relative
  deriving DecidableEq, Repr

namespace AccuracyMeasure

/-- Interpret an accuracy measure as the corresponding scalar error quantity. -/
noncomputable def value : AccuracyMeasure → ℝ → ℝ → ℝ
  | absolute, computed, exact => absError computed exact
  | relative, computed, exact => relError computed exact

/-- The absolute-error accuracy measure is `absError`. -/
theorem value_absolute (computed exact : ℝ) :
    value absolute computed exact = absError computed exact := rfl

/-- The relative-error accuracy measure is `relError`. -/
theorem value_relative (computed exact : ℝ) :
    value relative computed exact = relError computed exact := rfl

end AccuracyMeasure

/-- Higham §1.4 precision for a floating-point arithmetic, represented by the
unit roundoff governing the basic arithmetic operations. -/
structure PrecisionMeasure where
  unitRoundoff : ℝ
  unitRoundoff_nonneg : 0 ≤ unitRoundoff

namespace PrecisionMeasure

/-- The precision measure carried by an abstract `FPModel`. -/
def ofFPModel (fp : FPModel) : PrecisionMeasure where
  unitRoundoff := fp.u
  unitRoundoff_nonneg := fp.u_nonneg

/-- `ofFPModel` records exactly the model's unit roundoff. -/
theorem ofFPModel_unitRoundoff (fp : FPModel) :
    (ofFPModel fp).unitRoundoff = fp.u := rfl

end PrecisionMeasure

/-- Higham §1.4's implicit caveat: working arithmetic can be used to simulate
arithmetic of a higher precision.  This predicate records that the simulated
unit roundoff is strictly smaller than the working unit roundoff. -/
def SimulatesHigherPrecision
    (working simulated : PrecisionMeasure) : Prop :=
  simulated.unitRoundoff < working.unitRoundoff

/-- Basic-operation precision contract: every primitive operation is computed
with a signed relative factor bounded by the arithmetic precision `fp.u`.
Division carries the usual nonzero-denominator side condition. -/
def BasicOperationPrecisionBounded (fp : FPModel) : Prop :=
  ∀ op x y, (op = BasicOp.div → y ≠ 0) →
    ∃ δ : ℝ,
      |δ| ≤ (PrecisionMeasure.ofFPModel fp).unitRoundoff ∧
      fp.round op x y = BasicOp.exact op x y * (1 + δ)

/-- Every `FPModel` satisfies the §1.4 basic-operation precision contract by
its primitive operation model. -/
theorem FPModel.basicOperationPrecisionBounded (fp : FPModel) :
    BasicOperationPrecisionBounded fp := by
  intro op x y hy
  simpa [PrecisionMeasure.ofFPModel_unitRoundoff] using
    fp.model_basicOp op x y hy

/-- For the scalar computation `c = a*b`, the model's multiplication precision
is also a signed relative-accuracy witness for the computed product. -/
theorem fl_mul_accuracy_witness_of_precision (fp : FPModel) (a b : ℝ) :
    ∃ δ : ℝ,
      |δ| ≤ (PrecisionMeasure.ofFPModel fp).unitRoundoff ∧
      signedRelErrorWitness (fp.fl_mul a b) (a * b) δ := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul a b
  refine ⟨δ, ?_, ?_⟩
  · simpa [PrecisionMeasure.ofFPModel_unitRoundoff] using hδ
  · exact hfl

/-- If the exact product is nonzero, the relative accuracy of one rounded
scalar multiplication is bounded by the arithmetic precision `u`. -/
theorem fl_mul_relError_le_precision (fp : FPModel) (a b : ℝ)
    (hab : a * b ≠ 0) :
    relError (fp.fl_mul a b) (a * b) ≤
      (PrecisionMeasure.ofFPModel fp).unitRoundoff := by
  obtain ⟨δ, hδ, hρ⟩ := fl_mul_accuracy_witness_of_precision fp a b
  have hrel := relError_eq_abs_of_signedRelErrorWitness hab hρ
  rw [hrel]
  exact hδ

-- ============================================================
-- §1.7  Cancellation
-- ============================================================

















































end NumStability
