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









/-- Higham Chapter 2 no-guard subtraction model (2.6a):
`fl(x - y) = x * (1 + α) - y * (1 + β)`, with the literal source
componentwise bounds `|α|, |β| ≤ u`. -/
def noGuardSubWitness
    (computed x y u α β : ℝ) : Prop :=
  |α| ≤ u ∧ |β| ≤ u ∧
    computed = x * (1 + α) - y * (1 + β)

/-- Higham Chapter 2 no-guard multiply/divide branch (2.6b): multiplication
and division retain the ordinary source relative-error bound `|δ| ≤ u`. -/
def noGuardMulDivWitness
    (computed exact u δ : ℝ) : Prop :=
  |δ| ≤ u ∧ signedRelErrorWitness computed exact δ

/-- Unified per-operation witness for the no-guard model (2.6a,b).
Addition and subtraction use separate perturbations on the two input terms;
multiplication and division use the standard strict relative-error form.
Division carries the usual nonzero-denominator side condition. -/
def noGuardBasicOpWitness
    (op : BasicOp) (computed x y u : ℝ) : Prop :=
  match op with
  | BasicOp.add =>
      ∃ α β : ℝ, noGuardAddWitness computed x y u α β
  | BasicOp.sub =>
      ∃ α β : ℝ, noGuardSubWitness computed x y u α β
  | BasicOp.mul =>
      ∃ δ : ℝ, noGuardMulDivWitness computed (x * y) u δ
  | BasicOp.div =>
      y ≠ 0 ∧ ∃ δ : ℝ, noGuardMulDivWitness computed (x / y) u δ

theorem noGuardAddWitness_alpha_bound
    {computed x y u α β : ℝ}
    (h : noGuardAddWitness computed x y u α β) :
    |α| ≤ u :=
  h.1

theorem noGuardAddWitness_beta_bound
    {computed x y u α β : ℝ}
    (h : noGuardAddWitness computed x y u α β) :
    |β| ≤ u :=
  h.2.1

theorem noGuardAddWitness_value
    {computed x y u α β : ℝ}
    (h : noGuardAddWitness computed x y u α β) :
    computed = x * (1 + α) + y * (1 + β) :=
  h.2.2

/-- Additive error form implied by the no-guard add model: the error in
`fl(x + y)` is `x*α + y*β`. -/
theorem noGuardAddWitness_error_eq
    {computed x y u α β : ℝ}
    (h : noGuardAddWitness computed x y u α β) :
    computed - (x + y) = x * α + y * β := by
  rw [noGuardAddWitness_value h]
  ring

theorem noGuardSubWitness_alpha_bound
    {computed x y u α β : ℝ}
    (h : noGuardSubWitness computed x y u α β) :
    |α| ≤ u :=
  h.1

theorem noGuardSubWitness_beta_bound
    {computed x y u α β : ℝ}
    (h : noGuardSubWitness computed x y u α β) :
    |β| ≤ u :=
  h.2.1

theorem noGuardSubWitness_value
    {computed x y u α β : ℝ}
    (h : noGuardSubWitness computed x y u α β) :
    computed = x * (1 + α) - y * (1 + β) :=
  h.2.2

/-- Additive error form implied by the no-guard subtraction model: the error
in `fl(x - y)` is `x*α - y*β`. -/
theorem noGuardSubWitness_error_eq
    {computed x y u α β : ℝ}
    (h : noGuardSubWitness computed x y u α β) :
    computed - (x - y) = x * α - y * β := by
  rw [noGuardSubWitness_value h]
  ring

theorem noGuardMulDivWitness_delta_bound
    {computed exact u δ : ℝ}
    (h : noGuardMulDivWitness computed exact u δ) :
    |δ| ≤ u :=
  h.1

theorem noGuardMulDivWitness_signedRelErrorWitness
    {computed exact u δ : ℝ}
    (h : noGuardMulDivWitness computed exact u δ) :
    signedRelErrorWitness computed exact δ :=
  h.2

theorem noGuardMulDivWitness_of_signedRelErrorWitness
    {computed exact u δ : ℝ}
    (hδ : |δ| ≤ u)
    (h : signedRelErrorWitness computed exact δ) :
    noGuardMulDivWitness computed exact u δ :=
  ⟨hδ, h⟩

/-- Multiplication/division no-guard branch in additive-error form. -/
theorem noGuardMulDivWitness_error_eq
    {computed exact u δ : ℝ}
    (h : noGuardMulDivWitness computed exact u δ) :
    computed - exact = exact * δ := by
  have hw := noGuardMulDivWitness_signedRelErrorWitness h
  unfold signedRelErrorWitness at hw
  rw [hw]
  ring

theorem noGuardBasicOpWitness_add_iff
    {computed x y u : ℝ} :
    noGuardBasicOpWitness BasicOp.add computed x y u ↔
      ∃ α β : ℝ, noGuardAddWitness computed x y u α β :=
  Iff.rfl

theorem noGuardBasicOpWitness_sub_iff
    {computed x y u : ℝ} :
    noGuardBasicOpWitness BasicOp.sub computed x y u ↔
      ∃ α β : ℝ, noGuardSubWitness computed x y u α β :=
  Iff.rfl

theorem noGuardBasicOpWitness_mul_iff
    {computed x y u : ℝ} :
    noGuardBasicOpWitness BasicOp.mul computed x y u ↔
      ∃ δ : ℝ, noGuardMulDivWitness computed (x * y) u δ :=
  Iff.rfl

theorem noGuardBasicOpWitness_div_iff
    {computed x y u : ℝ} :
    noGuardBasicOpWitness BasicOp.div computed x y u ↔
      y ≠ 0 ∧ ∃ δ : ℝ, noGuardMulDivWitness computed (x / y) u δ :=
  Iff.rfl



















































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

















































end NumStability
