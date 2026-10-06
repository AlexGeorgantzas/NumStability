import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.Error.Measures.ScalarDefinitions
import NumStability.Analysis.FloatingPointArithmetic.ErrorModels.Additive
import NumStability.Analysis.FloatingPointArithmetic.ErrorModels.NoGuardBasic
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











































































































































































/-- Abstract no-guard floating-point model for Higham Chapter 2 equation
(2.6a,b).  This is intentionally separate from `FPModel`: add/sub use the
weaker two-input perturbation model, while mul/div retain the ordinary
boundary-inclusive relative-error model. -/
structure NoGuardFPModel where
  u : ℝ
  unit_roundoff_pos : 0 < u
  fl_add : ℝ → ℝ → ℝ
  fl_sub : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_div : ℝ → ℝ → ℝ
  model_add :
    ∀ x y, ∃ α β : ℝ,
      noGuardAddWitness (fl_add x y) x y u α β
  model_sub :
    ∀ x y, ∃ α β : ℝ,
      noGuardSubWitness (fl_sub x y) x y u α β
  model_mul :
    ∀ x y, ∃ δ : ℝ,
      noGuardMulDivWitness (fl_mul x y) (x * y) u δ
  model_div :
    ∀ x y, y ≠ 0 →
      ∃ δ : ℝ,
        noGuardMulDivWitness (fl_div x y) (x / y) u δ

namespace NoGuardFPModel

/-- Rounded operation associated with a primitive operation in the no-guard
model. -/
def round (fp : NoGuardFPModel) : BasicOp → ℝ → ℝ → ℝ
  | BasicOp.add, x, y => fp.fl_add x y
  | BasicOp.sub, x, y => fp.fl_sub x y
  | BasicOp.mul, x, y => fp.fl_mul x y
  | BasicOp.div, x, y => fp.fl_div x y

/-- Exact arithmetic packaged as a no-guard model with a positive advertised
unit roundoff. -/
noncomputable def exactWithUnitRoundoff (u0 : ℝ) (hu0 : 0 < u0) :
    NoGuardFPModel where
  u := u0
  unit_roundoff_pos := hu0
  fl_add := fun x y => x + y
  fl_sub := fun x y => x - y
  fl_mul := fun x y => x * y
  fl_div := fun x y => x / y
  model_add := by
    intro x y
    refine ⟨0, 0, ?_⟩
    constructor
    · simpa using le_of_lt hu0
    constructor
    · simpa using le_of_lt hu0
    · ring
  model_sub := by
    intro x y
    refine ⟨0, 0, ?_⟩
    constructor
    · simpa using le_of_lt hu0
    constructor
    · simpa using le_of_lt hu0
    · ring
  model_mul := by
    intro x y
    refine ⟨0, ?_⟩
    constructor
    · simpa using le_of_lt hu0
    · unfold signedRelErrorWitness
      ring
  model_div := by
    intro x y _hy
    refine ⟨0, ?_⟩
    constructor
    · simpa using le_of_lt hu0
    · unfold signedRelErrorWitness
      ring

/-- The unit roundoff of a no-guard model is positive. -/
theorem u_pos (fp : NoGuardFPModel) :
    0 < fp.u :=
  fp.unit_roundoff_pos

/-- Unified operation witness for a no-guard model. -/
theorem model_basicOp
    (fp : NoGuardFPModel) (op : BasicOp) (x y : ℝ)
    (hy : op = BasicOp.div → y ≠ 0) :
    noGuardBasicOpWitness op (fp.round op x y) x y fp.u := by
  cases op with
  | add =>
      simpa [round, noGuardBasicOpWitness] using fp.model_add x y
  | sub =>
      simpa [round, noGuardBasicOpWitness] using fp.model_sub x y
  | mul =>
      simpa [round, noGuardBasicOpWitness] using fp.model_mul x y
  | div =>
      have hy' : y ≠ 0 := hy rfl
      have hmodel :
          ∃ δ : ℝ,
            noGuardMulDivWitness (fp.fl_div x y) (x / y) fp.u δ :=
        fp.model_div x y hy'
      exact ⟨hy', hmodel⟩

/-- The no-guard add model exposes the Chapter 2 error split
`fl(x + y) - (x + y) = x*α + y*β`. -/
theorem model_add_error_eq
    (fp : NoGuardFPModel) (x y : ℝ) :
    ∃ α β : ℝ,
      |α| ≤ fp.u ∧ |β| ≤ fp.u ∧
        fp.fl_add x y - (x + y) = x * α + y * β := by
  rcases fp.model_add x y with ⟨α, β, h⟩
  exact
    ⟨α, β, h.1, h.2.1, noGuardAddWitness_error_eq h⟩

/-- The no-guard subtraction model exposes the Chapter 2 error split
`fl(x - y) - (x - y) = x*α - y*β`. -/
theorem model_sub_error_eq
    (fp : NoGuardFPModel) (x y : ℝ) :
    ∃ α β : ℝ,
      |α| ≤ fp.u ∧ |β| ≤ fp.u ∧
        fp.fl_sub x y - (x - y) = x * α - y * β := by
  rcases fp.model_sub x y with ⟨α, β, h⟩
  exact
    ⟨α, β, h.1, h.2.1, noGuardSubWitness_error_eq h⟩

/-- Multiplication keeps the ordinary source standard-model witness under the
no-guard model. -/
theorem model_mul_signedRelErrorWitness
    (fp : NoGuardFPModel) (x y : ℝ) :
    ∃ δ : ℝ,
      |δ| ≤ fp.u ∧ signedRelErrorWitness (fp.fl_mul x y) (x * y) δ := by
  rcases fp.model_mul x y with ⟨δ, h⟩
  exact ⟨δ, h.1, h.2⟩

/-- Division keeps the ordinary source standard-model witness under the
no-guard model, with the usual nonzero denominator side condition. -/
theorem model_div_signedRelErrorWitness
    (fp : NoGuardFPModel) (x y : ℝ) (hy : y ≠ 0) :
    ∃ δ : ℝ,
      |δ| ≤ fp.u ∧ signedRelErrorWitness (fp.fl_div x y) (x / y) δ := by
  rcases fp.model_div x y hy with ⟨δ, h⟩
  exact ⟨δ, h.1, h.2⟩

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

















































end NumStability
