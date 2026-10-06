-- Error.lean

import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model

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

/-- Absolute error of a floating-point approximation.
    Defined as |computed - exact|. No assumption on exact. -/
noncomputable def absError (computed exact : ℝ) : ℝ :=
  |computed - exact|

/-- Relative error of a floating-point approximation.
    Defined as |computed - exact| / |exact|.
    Meaningful only when `exact ≠ 0`; the caller must enforce this. -/
noncomputable def relError (computed exact : ℝ) : ℝ :=
  |computed - exact| / |exact|

/-- Domain predicate for Higham's relative error: the exact value must be nonzero. -/
def relErrorDefined (exact : ℝ) : Prop :=
  exact ≠ 0

/-- Signed relative-error witness: `computed = exact * (1 + ρ)`. -/
def signedRelErrorWitness (computed exact ρ : ℝ) : Prop :=
  computed = exact * (1 + ρ)

/-- Higham Chapter 2 additive underflow/overflow witness:
`computed = exact * (1 + δ) + η`.  This is the algebraic surface of
equation (2.8); bounds on `δ` and `η` are carried by the model predicate below. -/
def additiveErrorWitness (computed exact δ η : ℝ) : Prop :=
  computed = exact * (1 + δ) + η

/-- Equation (2.8)'s branch condition: at most one of the relative term `δ`
and additive term `η` is active.  Both may be zero for an exact operation. -/
def oneAdditiveErrorTermZero (δ η : ℝ) : Prop :=
  δ = 0 ∨ η = 0

/-- Non-strict formal variant of Higham Chapter 2 equation (2.8):
`computed = exact * (1 + δ) + η`, `|δ| < u`, `|η| <= ηBound`, and one
of `δ`, `η` is zero. -/
def additiveUnderflowModelWitness
    (computed exact u ηBound δ η : ℝ) : Prop :=
  additiveErrorWitness computed exact δ η ∧
    |δ| < u ∧ |η| ≤ ηBound ∧ oneAdditiveErrorTermZero δ η

/-- Strict source-shaped variant of Higham Chapter 2 equation (2.8):
`computed = exact * (1 + δ) + η`, `|δ| < u`, `|η| < ηBound`, and one
of `δ`, `η` is zero. -/
def strictAdditiveUnderflowModelWitness
    (computed exact u ηBound δ η : ℝ) : Prop :=
  additiveErrorWitness computed exact δ η ∧
    |δ| < u ∧ |η| < ηBound ∧ oneAdditiveErrorTermZero δ η

-- ============================================================
-- §2.4  No-guard digit model
-- ============================================================

/-- Higham Chapter 2 no-guard add model (2.6a):
`fl(x + y) = x * (1 + α) + y * (1 + β)`, with the literal source
componentwise bounds `|α|, |β| ≤ u`. -/
def noGuardAddWitness
    (computed x y u α β : ℝ) : Prop :=
  |α| ≤ u ∧ |β| ≤ u ∧
    computed = x * (1 + α) + y * (1 + β)

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

/-- Higham §2.4 no-guard example: in base two with three mantissa digits,
`1.0 - 0.111₂` has exact real value `1/8`. -/
theorem noGuardBinaryT3_exact_difference :
    (1 : ℝ) - (7 / 8 : ℝ) = 1 / 8 := by
  norm_num

/-- Higham §2.4 no-guard example after dropping the guard digit:
the aligned `0.0111₂` operand is truncated to `0.011₂`, giving `1/4`. -/
theorem noGuardBinaryT3_truncated_difference :
    (1 : ℝ) - (3 / 4 : ℝ) = 1 / 4 := by
  norm_num

/-- The dropped-digit no-guard result in Higham's three-bit binary example is
twice the exact result. -/
theorem noGuardBinaryT3_truncated_factor_two :
    (1 / 4 : ℝ) = 2 * (1 / 8 : ℝ) := by
  norm_num

/-- The dropped-digit no-guard result in Higham's three-bit binary example has
relative error exactly one. -/
theorem noGuardBinaryT3_truncated_relError_eq_one :
    relError (1 / 4 : ℝ) (1 / 8 : ℝ) = 1 := by
  norm_num [relError]
  rfl

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

/-- Higham Problem 1.1 packaged form: when both denominators are nonzero and
both relative errors are below one, the exact-denominator and
computed-denominator relative errors bound each other by the standard
`E/(1±E)` envelopes. -/
theorem problem_1_1_relError_bounds
    (computed exact : ℝ) (hexact : exact ≠ 0) (hcomputed : computed ≠ 0)
    (hrel : relError computed exact < 1)
    (hrelTilde : relErrorComputedDenom computed exact < 1) :
    (relError computed exact / (1 + relError computed exact) ≤
        relErrorComputedDenom computed exact ∧
      relErrorComputedDenom computed exact ≤
        relError computed exact / (1 - relError computed exact)) ∧
    (relErrorComputedDenom computed exact /
          (1 + relErrorComputedDenom computed exact) ≤
        relError computed exact ∧
      relError computed exact ≤
        relErrorComputedDenom computed exact /
          (1 - relErrorComputedDenom computed exact)) := by
  exact ⟨
    ⟨relErrorComputedDenom_lower_bound_from_relError computed exact hexact hcomputed,
      relErrorComputedDenom_upper_bound_from_relError computed exact hexact hrel⟩,
    ⟨relError_lower_bound_from_computedDenom computed exact hexact hcomputed,
      relError_upper_bound_from_computedDenom computed exact hcomputed hrelTilde⟩⟩

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

/-- Higham §1.3's three main sources of errors in numerical computation. -/
inductive ErrorSource where
  | rounding
  | dataUncertainty
  | truncation
  deriving DecidableEq, Repr

namespace ErrorSource

/-- Exhaustive predicate for the three Chapter 1 error-source classes. -/
def IsChapterOneMainSource (s : ErrorSource) : Prop :=
  s = rounding ∨ s = dataUncertainty ∨ s = truncation

/-- Higham §1.3: the Chapter 1 taxonomy has exactly these three main classes. -/
theorem chapterOneMainSource_exhaustive (s : ErrorSource) :
    IsChapterOneMainSource s := by
  cases s <;> simp [IsChapterOneMainSource]

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
