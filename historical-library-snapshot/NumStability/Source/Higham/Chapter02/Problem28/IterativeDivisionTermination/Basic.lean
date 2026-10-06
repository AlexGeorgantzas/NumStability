import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Source.Higham.Chapter02.FloatingPointArithmetic.AdditiveUnderflowModel

/-!
# Chapter02 Problem28 IterativeDivisionTermination Basic

Canonical destination for material split out of
`NumStability.Analysis.Problem2_27` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

/-- Residual for testing whether `z` solves `z = x/y`. -/
def problem2_27_residual (x y z : ℝ) : ℝ :=
  x - y * z

/-- Full residual accuracy for the quotient equation, stated without division. -/
def problem2_27_fullAccuracy (x y z : ℝ) : Prop :=
  y * z = x

theorem problem2_27_residual_eq_zero_iff_fullAccuracy {x y z : ℝ} :
    problem2_27_residual x y z = 0 ↔
      problem2_27_fullAccuracy x y z := by
  unfold problem2_27_residual problem2_27_fullAccuracy
  constructor
  · intro h
    linarith
  · intro h
    linarith

theorem problem2_27_fullAccuracy_iff_eq_div {x y z : ℝ} (hy : y ≠ 0) :
    problem2_27_fullAccuracy x y z ↔ z = x / y := by
  unfold problem2_27_fullAccuracy
  constructor
  · intro h
    have hz : z = (y * z) / y := by
      field_simp [hy]
    calc
      z = (y * z) / y := hz
      _ = x / y := by rw [h]
  · intro h
    rw [h]
    field_simp [hy]

namespace FloatingPointFormat

/-- Rounded product used by the concrete residual test. -/
def problem2_27_computedProduct
    (fmt : FloatingPointFormat) (y z : ℝ) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.mul y z

/-- Concrete finite round-to-even residual test `fl(x - fl(y*z))`. -/
def problem2_27_computedResidual
    (fmt : FloatingPointFormat) (x y z : ℝ) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.sub x
    (fmt.problem2_27_computedProduct y z)

/-- The executable-looking convergence predicate: the computed residual is
zero.  The theorems below state which hypotheses make this a full-accuracy
certificate. -/
def problem2_27_convergenceTest
    (fmt : FloatingPointFormat) (x y z : ℝ) : Prop :=
  fmt.problem2_27_computedResidual x y z = 0

theorem problem2_27_computedProduct_eq_exact_of_finiteSystem
    {fmt : FloatingPointFormat} {y z : ℝ}
    (hprod : fmt.finiteSystem (y * z)) :
    fmt.problem2_27_computedProduct y z = y * z := by
  simpa [problem2_27_computedProduct, BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := y) (y := z)
      (by simpa [BasicOp.exact] using hprod))

theorem problem2_27_computedResidual_eq_exact_of_finiteSystem
    {fmt : FloatingPointFormat} {x y z : ℝ}
    (hprod : fmt.finiteSystem (y * z))
    (hres : fmt.finiteSystem (problem2_27_residual x y z)) :
    fmt.problem2_27_computedResidual x y z =
      problem2_27_residual x y z := by
  have hprod_eq :=
    fmt.problem2_27_computedProduct_eq_exact_of_finiteSystem
      (y := y) (z := z) hprod
  have hsub :
      fmt.finiteRoundToEvenOp BasicOp.sub x (y * z) = x - y * z := by
    simpa [BasicOp.exact, problem2_27_residual] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := x) (y := y * z)
        (by simpa [BasicOp.exact, problem2_27_residual] using hres))
  rw [problem2_27_computedResidual, hprod_eq]
  simpa [problem2_27_residual] using hsub

theorem problem2_27_convergenceTest_iff_fullAccuracy_of_exact_residual_path
    {fmt : FloatingPointFormat} {x y z : ℝ}
    (hprod : fmt.finiteSystem (y * z))
    (hres : fmt.finiteSystem (problem2_27_residual x y z)) :
    fmt.problem2_27_convergenceTest x y z ↔
      problem2_27_fullAccuracy x y z := by
  unfold problem2_27_convergenceTest
  rw [fmt.problem2_27_computedResidual_eq_exact_of_finiteSystem hprod hres]
  exact problem2_27_residual_eq_zero_iff_fullAccuracy

theorem problem2_27_convergenceTest_iff_eq_div_of_exact_residual_path
    {fmt : FloatingPointFormat} {x y z : ℝ}
    (hy : y ≠ 0)
    (hprod : fmt.finiteSystem (y * z))
    (hres : fmt.finiteSystem (problem2_27_residual x y z)) :
    fmt.problem2_27_convergenceTest x y z ↔ z = x / y := by
  rw [fmt.problem2_27_convergenceTest_iff_fullAccuracy_of_exact_residual_path
    hprod hres]
  exact problem2_27_fullAccuracy_iff_eq_div hy

/-- Converse normal-branch result: if full accuracy has already been achieved,
then the (2.8) normal-branch residual computation returns zero and the
convergence test terminates. -/
theorem problem2_27_convergenceTest_of_fullAccuracy_additive_model_normal_branch
    {fmt : FloatingPointFormat} {x y z delta : ℝ}
    (hmodel :
      additiveUnderflowModelWitness
        (fmt.problem2_27_computedResidual x y z)
        (problem2_27_residual x y z)
        fmt.unitRoundoff fmt.gradualUnderflowEtaBound delta 0)
    (hfull : problem2_27_fullAccuracy x y z) :
    fmt.problem2_27_convergenceTest x y z := by
  rcases hmodel with ⟨hvalue, _hdelta, _hetaBound, _hbranch⟩
  have hres : problem2_27_residual x y z = 0 :=
    problem2_27_residual_eq_zero_iff_fullAccuracy.2 hfull
  unfold problem2_27_convergenceTest
  unfold additiveErrorWitness at hvalue
  rw [hres] at hvalue
  simpa using hvalue

end FloatingPointFormat
end NumStability

end
