-- Model.lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace NumStability

/-- The four primitive arithmetic operations in Higham Chapter 1, equation (1.1). -/
inductive BasicOp where
  | add
  | sub
  | mul
  | div
  deriving DecidableEq, Repr

namespace BasicOp

/-- Exact real operation associated with a primitive floating-point operation. -/
noncomputable def exact : BasicOp → ℝ → ℝ → ℝ
  | add, x, y => x + y
  | sub, x, y => x - y
  | mul, x, y => x * y
  | div, x, y => x / y

end BasicOp

/--
A Higham-style abstract floating-point model.

Source: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
§1.1, equation (1.1), and §2.2, standard model (2.4).  We use the non-strict
formal variant `|δ| ≤ u` of Higham's usual `|δ| < u`.

Each primitive arithmetic operation satisfies:
`fl(x op y) = (x op y) * (1 + δ)`, with `|δ| ≤ u`.

The square-root operation is included because algorithms such as Householder
reflector construction and Cholesky factorization need it as a primitive
rounded operation.  Higham explicitly notes after (2.4) that the same standard
model is normally assumed for square root.  Its relative-error law is stated
only for nonnegative inputs, which is the mathematical domain of real square
root.
-/

structure FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u

  fl_add : ℝ → ℝ → ℝ
  fl_sub : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_div : ℝ → ℝ → ℝ
  fl_sqrt : ℝ → ℝ

  /-- Additional exactness law: `fl(0 + x) = x`.

      This is not a consequence of the relative-error standard model above.
      It is included explicitly because tight recursive-summation constants use
      the first addition from zero as exact. -/
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x

  model_add :
    ∀ x y, ∃ δ : ℝ,
      |δ| ≤ u ∧
      fl_add x y = (x + y) * (1 + δ)

  model_sub :
    ∀ x y, ∃ δ : ℝ,
      |δ| ≤ u ∧
      fl_sub x y = (x - y) * (1 + δ)

  model_mul :
    ∀ x y, ∃ δ : ℝ,
      |δ| ≤ u ∧
      fl_mul x y = (x * y) * (1 + δ)

  model_div :
    ∀ x y, y ≠ 0 →
      ∃ δ : ℝ,
        |δ| ≤ u ∧
        fl_div x y = (x / y) * (1 + δ)

  model_sqrt :
    ∀ x, 0 ≤ x →
      ∃ δ : ℝ,
        |δ| ≤ u ∧
        fl_sqrt x = Real.sqrt x * (1 + δ)

namespace FPModel

/-- Rounded operation associated with a primitive Higham operation. -/
def round (fp : FPModel) : BasicOp → ℝ → ℝ → ℝ
  | BasicOp.add, x, y => fp.fl_add x y
  | BasicOp.sub, x, y => fp.fl_sub x y
  | BasicOp.mul, x, y => fp.fl_mul x y
  | BasicOp.div, x, y => fp.fl_div x y

/-- Unified form of Higham Chapter 1 equation (1.1) for the four primitive
operations.  Division carries the usual nonzero denominator side condition. -/
theorem model_basicOp (fp : FPModel) (op : BasicOp) (x y : ℝ)
    (hy : op = BasicOp.div → y ≠ 0) :
    ∃ δ : ℝ,
      |δ| ≤ fp.u ∧
      fp.round op x y = BasicOp.exact op x y * (1 + δ) := by
  cases op with
  | add =>
      exact fp.model_add x y
  | sub =>
      exact fp.model_sub x y
  | mul =>
      exact fp.model_mul x y
  | div =>
      exact fp.model_div x y (hy rfl)

/-- Exact arithmetic viewed as an `FPModel` with an arbitrary nonnegative
declared unit roundoff.

This constructor is useful for route-elimination statements: since the abstract
model stores only `0 <= u`, any theorem that tries to derive a fixed numerical
cap on `u` from `FPModel` alone is false. -/
noncomputable def exactWithUnitRoundoff (u0 : ℝ) (hu0 : 0 ≤ u0) :
    FPModel where
  u := u0
  u_nonneg := hu0
  fl_add := fun x y => x + y
  fl_sub := fun x y => x - y
  fl_mul := fun x y => x * y
  fl_div := fun x y => x / y
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by
    intro x
    ring
  model_add := by
    intro x y
    refine ⟨0, ?_, ?_⟩
    · simpa using hu0
    · ring
  model_sub := by
    intro x y
    refine ⟨0, ?_, ?_⟩
    · simpa using hu0
    · ring
  model_mul := by
    intro x y
    refine ⟨0, ?_, ?_⟩
    · simpa using hu0
    · ring
  model_div := by
    intro x y _hy
    refine ⟨0, ?_, ?_⟩
    · simpa using hu0
    · ring
  model_sqrt := by
    intro x _hx
    refine ⟨0, ?_, ?_⟩
    · simpa using hu0
    · ring

/-- No fixed unit-roundoff cap follows from the abstract `FPModel` structure.

The model only assumes `0 <= fp.u`.  Therefore any theorem that needs
`fp.u <= Ucap` must carry it as a floating-point/domain assumption or derive it
from a more concrete machine model. -/
theorem not_forall_u_le_cap (Ucap : ℝ) :
    ¬ ∀ fp : FPModel, fp.u ≤ Ucap := by
  intro hcap
  let uBig : ℝ := max 0 Ucap + 1
  have huBig_nonneg : 0 ≤ uBig := by
    have hmax : 0 ≤ max 0 Ucap := le_max_left 0 Ucap
    linarith
  let fp : FPModel := FPModel.exactWithUnitRoundoff uBig huBig_nonneg
  have hle : uBig ≤ Ucap := by
    simpa [fp, uBig] using hcap fp
  have hU : Ucap ≤ max 0 Ucap := le_max_right 0 Ucap
  linarith

end FPModel

end NumStability
