-- NumStability/Source/Higham/Chapter02/Problem28/IterativeDivisionTermination/UnderflowAwareConvergence/Results.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Analysis.Problem2_27`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Source.Higham.Chapter02.Problem14.UnitRoundoffProbe.IeeeExamples.Results
import NumStability.Source.Higham.Chapter02.Problem28.IterativeDivisionTermination.Basic
import NumStability.Source.Higham.Chapter02.Section06.ReciprocalIteration.Basic

/-!
# Results

Relocated from `NumStability.Analysis.Problem2_27` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# Problem2_27 (compatibility module)

Historical path, retained so existing imports of `NumStability.Analysis.Problem2_27`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

noncomputable section

namespace NumStability

private theorem problem2_27_one_add_ne_zero_of_abs_lt_u_le_one
    {u delta : ℝ} (hdelta : |delta| < u) (hu : u ≤ 1) :
    1 + delta ≠ 0 := by
  have hdelta_lt_one : |delta| < 1 := lt_of_lt_of_le hdelta hu
  have hbounds := abs_lt.mp hdelta_lt_one
  have hpos : 0 < 1 + delta := by linarith
  exact ne_of_gt hpos

/-- If the computed residual is zero and (2.8) is in the normal branch
`eta = 0`, then the exact residual is zero. -/
theorem problem2_27_zero_exact_residual_of_additive_model_normal_branch
    {residual u etaBound delta : ℝ}
    (hu : u ≤ 1)
    (hmodel : additiveUnderflowModelWitness 0 residual u etaBound delta 0) :
    residual = 0 := by
  rcases hmodel with ⟨hvalue, hdelta, _hetaBound, _hbranch⟩
  unfold additiveErrorWitness at hvalue
  have hfactor_ne :=
    problem2_27_one_add_ne_zero_of_abs_lt_u_le_one hdelta hu
  have hmul : residual * (1 + delta) = 0 := by linarith
  rcases mul_eq_zero.mp hmul with hres | hfactor
  · exact hres
  · exact False.elim (hfactor_ne hfactor)

/-- A zero computed residual in the additive model proves either exact
residual zero or that the exact residual lies inside the additive underflow
bound.  This is the precise (2.8) ambiguity that the convergence test must
exclude to terminate only at full accuracy. -/
theorem problem2_27_zero_exact_residual_or_underflow_bound_of_additive_model
    {residual u etaBound delta eta : ℝ}
    (hu : u ≤ 1)
    (hmodel : additiveUnderflowModelWitness 0 residual u etaBound delta eta) :
    residual = 0 ∨ |residual| ≤ etaBound := by
  rcases hmodel with ⟨hvalue, hdelta, hetaBound, hbranch⟩
  rcases hbranch with hdelta_zero | heta_zero
  · right
    subst delta
    unfold additiveErrorWitness at hvalue
    have hres : residual = -eta := by linarith
    calc
      |residual| = |eta| := by rw [hres, abs_neg]
      _ ≤ etaBound := hetaBound
  · left
    subst eta
    exact
      problem2_27_zero_exact_residual_of_additive_model_normal_branch
        (u := u) (etaBound := etaBound) (delta := delta) hu
        ⟨hvalue, hdelta, by simpa using hetaBound, Or.inr rfl⟩

/-- Strict variant matching the source's strict additive bound away from
half-cell ties. -/
theorem problem2_27_zero_exact_residual_or_strict_underflow_bound_of_strict_model
    {residual u etaBound delta eta : ℝ}
    (hu : u ≤ 1)
    (hmodel : strictAdditiveUnderflowModelWitness 0 residual u etaBound delta eta) :
    residual = 0 ∨ |residual| < etaBound := by
  rcases hmodel with ⟨hvalue, hdelta, hetaBound, hbranch⟩
  rcases hbranch with hdelta_zero | heta_zero
  · right
    subst delta
    unfold additiveErrorWitness at hvalue
    have hres : residual = -eta := by linarith
    calc
      |residual| = |eta| := by rw [hres, abs_neg]
      _ < etaBound := hetaBound
  · left
    subst eta
    have hle : |(0 : ℝ)| ≤ etaBound := le_of_lt hetaBound
    exact
      problem2_27_zero_exact_residual_of_additive_model_normal_branch
        (u := u) (etaBound := etaBound) (delta := delta) hu
        ⟨hvalue, hdelta, hle, Or.inr rfl⟩

theorem problem2_27_fullAccuracy_of_zero_residual_normal_branch
    {x y z u etaBound delta : ℝ}
    (hu : u ≤ 1)
    (hmodel :
      additiveUnderflowModelWitness 0 (problem2_27_residual x y z)
        u etaBound delta 0) :
    problem2_27_fullAccuracy x y z := by
  exact
    problem2_27_residual_eq_zero_iff_fullAccuracy.1
      (problem2_27_zero_exact_residual_of_additive_model_normal_branch
        (u := u) (etaBound := etaBound) (delta := delta) hu hmodel)

theorem problem2_27_fullAccuracy_or_underflow_bound_of_zero_residual_model
    {x y z u etaBound delta eta : ℝ}
    (hu : u ≤ 1)
    (hmodel :
      additiveUnderflowModelWitness 0 (problem2_27_residual x y z)
        u etaBound delta eta) :
    problem2_27_fullAccuracy x y z ∨
      |problem2_27_residual x y z| ≤ etaBound := by
  rcases
    problem2_27_zero_exact_residual_or_underflow_bound_of_additive_model
      (residual := problem2_27_residual x y z) hu hmodel with
    hzero | hsmall
  · exact Or.inl (problem2_27_residual_eq_zero_iff_fullAccuracy.1 hzero)
  · exact Or.inr hsmall

namespace FloatingPointFormat

/-- Source-facing (2.8) convergence-test theorem: if the residual computation
is modeled by the additive gradual-underflow equation and returns zero, then
either full accuracy has been achieved or the exact residual is hidden inside
the additive underflow bound. -/
theorem problem2_27_convergenceTest_fullAccuracy_or_underflow_bound_of_additive_model
    {fmt : FloatingPointFormat} {x y z delta eta : ℝ}
    (hu : fmt.unitRoundoff ≤ 1)
    (hmodel :
      additiveUnderflowModelWitness
        (fmt.problem2_27_computedResidual x y z)
        (problem2_27_residual x y z)
        fmt.unitRoundoff fmt.gradualUnderflowEtaBound delta eta)
    (htest : fmt.problem2_27_convergenceTest x y z) :
    problem2_27_fullAccuracy x y z ∨
      |problem2_27_residual x y z| ≤ fmt.gradualUnderflowEtaBound := by
  have hmodel0 := hmodel
  rw [htest] at hmodel0
  exact
    problem2_27_fullAccuracy_or_underflow_bound_of_zero_residual_model
      (x := x) (y := y) (z := z)
      (u := fmt.unitRoundoff) (etaBound := fmt.gradualUnderflowEtaBound)
      (delta := delta) (eta := eta) hu hmodel0

/-- Strict (2.8) convergence-test variant: with a strict additive-underflow
model, a zero computed residual proves either full accuracy or a strict
eta-bound on the exact residual. -/
theorem problem2_27_convergenceTest_fullAccuracy_or_strict_underflow_bound_of_strict_model
    {fmt : FloatingPointFormat} {x y z delta eta : ℝ}
    (hu : fmt.unitRoundoff ≤ 1)
    (hmodel :
      strictAdditiveUnderflowModelWitness
        (fmt.problem2_27_computedResidual x y z)
        (problem2_27_residual x y z)
        fmt.unitRoundoff fmt.gradualUnderflowEtaBound delta eta)
    (htest : fmt.problem2_27_convergenceTest x y z) :
    problem2_27_fullAccuracy x y z ∨
      |problem2_27_residual x y z| < fmt.gradualUnderflowEtaBound := by
  have hmodel0 := hmodel
  rw [htest] at hmodel0
  rcases
      problem2_27_zero_exact_residual_or_strict_underflow_bound_of_strict_model
        (residual := problem2_27_residual x y z)
        (u := fmt.unitRoundoff)
        (etaBound := fmt.gradualUnderflowEtaBound)
        (delta := delta) (eta := eta) hu hmodel0 with
    hzero | hsmall
  · exact Or.inl (problem2_27_residual_eq_zero_iff_fullAccuracy.1 hzero)
  · exact Or.inr hsmall

/-- The conservative convergence test promised by Problem 2.27: a zero
computed residual certifies full accuracy when the (2.8) residual model is in
the normal branch, equivalently when the additive underflow term is zero. -/
theorem problem2_27_convergenceTest_fullAccuracy_of_additive_model_normal_branch
    {fmt : FloatingPointFormat} {x y z delta : ℝ}
    (hu : fmt.unitRoundoff ≤ 1)
    (hmodel :
      additiveUnderflowModelWitness
        (fmt.problem2_27_computedResidual x y z)
        (problem2_27_residual x y z)
        fmt.unitRoundoff fmt.gradualUnderflowEtaBound delta 0)
    (htest : fmt.problem2_27_convergenceTest x y z) :
    problem2_27_fullAccuracy x y z := by
  have hmodel0 := hmodel
  rw [htest] at hmodel0
  exact
    problem2_27_fullAccuracy_of_zero_residual_normal_branch
      (x := x) (y := y) (z := z)
      (u := fmt.unitRoundoff) (etaBound := fmt.gradualUnderflowEtaBound)
      (delta := delta) hu hmodel0

/-- In the (2.8) normal branch, the zero residual convergence test is exactly
equivalent to full residual accuracy. -/
theorem problem2_27_convergenceTest_iff_fullAccuracy_of_additive_model_normal_branch
    {fmt : FloatingPointFormat} {x y z delta : ℝ}
    (hu : fmt.unitRoundoff ≤ 1)
    (hmodel :
      additiveUnderflowModelWitness
        (fmt.problem2_27_computedResidual x y z)
        (problem2_27_residual x y z)
        fmt.unitRoundoff fmt.gradualUnderflowEtaBound delta 0) :
    fmt.problem2_27_convergenceTest x y z ↔
      problem2_27_fullAccuracy x y z := by
  constructor
  · intro htest
    exact
      fmt.problem2_27_convergenceTest_fullAccuracy_of_additive_model_normal_branch
        hu hmodel htest
  · intro hfull
    exact
      fmt.problem2_27_convergenceTest_of_fullAccuracy_additive_model_normal_branch
        hmodel hfull

/-- Division form of the normal-branch convergence test: when `y ≠ 0`, the
zero residual test certifies the actual quotient `z = x/y`. -/
theorem problem2_27_convergenceTest_eq_div_of_additive_model_normal_branch
    {fmt : FloatingPointFormat} {x y z delta : ℝ}
    (hy : y ≠ 0)
    (hu : fmt.unitRoundoff ≤ 1)
    (hmodel :
      additiveUnderflowModelWitness
        (fmt.problem2_27_computedResidual x y z)
        (problem2_27_residual x y z)
        fmt.unitRoundoff fmt.gradualUnderflowEtaBound delta 0)
    (htest : fmt.problem2_27_convergenceTest x y z) :
    z = x / y := by
  exact (problem2_27_fullAccuracy_iff_eq_div hy).mp
    (fmt.problem2_27_convergenceTest_fullAccuracy_of_additive_model_normal_branch
      hu hmodel htest)

/-- Iff division form of the normal-branch convergence test: for `y ≠ 0`,
terminating is equivalent to having computed the exact quotient. -/
theorem problem2_27_convergenceTest_iff_eq_div_of_additive_model_normal_branch
    {fmt : FloatingPointFormat} {x y z delta : ℝ}
    (hy : y ≠ 0)
    (hu : fmt.unitRoundoff ≤ 1)
    (hmodel :
      additiveUnderflowModelWitness
        (fmt.problem2_27_computedResidual x y z)
        (problem2_27_residual x y z)
        fmt.unitRoundoff fmt.gradualUnderflowEtaBound delta 0) :
    fmt.problem2_27_convergenceTest x y z ↔ z = x / y := by
  rw [fmt.problem2_27_convergenceTest_iff_fullAccuracy_of_additive_model_normal_branch
    hu hmodel]
  exact problem2_27_fullAccuracy_iff_eq_div hy

/-- Division form of the gradual-underflow ambiguity: without the normal branch,
the zero residual test proves either the exact quotient or that the exact
residual is hidden inside the additive underflow bound. -/
theorem problem2_27_convergenceTest_eq_div_or_underflow_bound_of_additive_model
    {fmt : FloatingPointFormat} {x y z delta eta : ℝ}
    (hy : y ≠ 0)
    (hu : fmt.unitRoundoff ≤ 1)
    (hmodel :
      additiveUnderflowModelWitness
        (fmt.problem2_27_computedResidual x y z)
        (problem2_27_residual x y z)
        fmt.unitRoundoff fmt.gradualUnderflowEtaBound delta eta)
    (htest : fmt.problem2_27_convergenceTest x y z) :
    z = x / y ∨
      |problem2_27_residual x y z| ≤ fmt.gradualUnderflowEtaBound := by
  rcases
      fmt.problem2_27_convergenceTest_fullAccuracy_or_underflow_bound_of_additive_model
        hu hmodel htest with
    hfull | hbound
  · exact Or.inl ((problem2_27_fullAccuracy_iff_eq_div hy).mp hfull)
  · exact Or.inr hbound

/-- Division form of the strict gradual-underflow ambiguity: with a strict
additive-underflow model, the zero residual test proves either the exact
quotient or a strict eta-bound on the exact residual. -/
theorem problem2_27_convergenceTest_eq_div_or_strict_underflow_bound_of_strict_model
    {fmt : FloatingPointFormat} {x y z delta eta : ℝ}
    (hy : y ≠ 0)
    (hu : fmt.unitRoundoff ≤ 1)
    (hmodel :
      strictAdditiveUnderflowModelWitness
        (fmt.problem2_27_computedResidual x y z)
        (problem2_27_residual x y z)
        fmt.unitRoundoff fmt.gradualUnderflowEtaBound delta eta)
    (htest : fmt.problem2_27_convergenceTest x y z) :
    z = x / y ∨
      |problem2_27_residual x y z| < fmt.gradualUnderflowEtaBound := by
  rcases
      fmt.problem2_27_convergenceTest_fullAccuracy_or_strict_underflow_bound_of_strict_model
        hu hmodel htest with
    hfull | hbound
  · exact Or.inl ((problem2_27_fullAccuracy_iff_eq_div hy).mp hfull)
  · exact Or.inr hbound

end FloatingPointFormat
end NumStability

end
