import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Analysis.MatrixAlgebra

/-!
# Chapter15 Equation04 NormalizedDualDiscrepancy Basic

Canonical destination for material split out of
`NumStability.Algorithms.PNormPowerMethod` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open scoped BigOperators

/-- The one-dimensional matrix `[2]` used to audit the literal coefficient in
equation (15.4). -/
noncomputable def eq15_4_counterexampleA : Fin 1 → Fin 1 → ℝ := fun _ _ => 2

/-- The unit vector `[1]` in the equation-(15.4) audit. -/
noncomputable def eq15_4_counterexampleX : Fin 1 → ℝ := fun _ => 1

lemma eq15_4_counterexampleX_norm : vecNorm2 eq15_4_counterexampleX = 1 := by
  simp [eq15_4_counterexampleX, vecNorm2, vecNorm2Sq]

lemma eq15_4_counterexample_y :
    (pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).yof
      eq15_4_counterexampleX = (fun _ : Fin 1 => 2) := by
  funext i
  change (∑ j : Fin 1, eq15_4_counterexampleA i j * eq15_4_counterexampleX j) = 2
  simp [eq15_4_counterexampleA, eq15_4_counterexampleX]

lemma eq15_4_normalize2_two :
    normalize2 (by omega : 0 < 1) (fun _ : Fin 1 => (2 : ℝ)) =
      (fun _ => 1) := by
  have hne : (fun _ : Fin 1 => (2 : ℝ)) ≠ 0 := by
    intro h
    have hh := congrFun h (0 : Fin 1)
    norm_num at hh
  rw [normalize2, if_neg hne]
  funext i
  simp [vecNorm2, vecNorm2Sq]

lemma eq15_4_counterexample_z :
    (pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).zof
      eq15_4_counterexampleX = (fun _ : Fin 1 => 2) := by
  have hdp : (pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).dp
      ((pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).yof
        eq15_4_counterexampleX) = (fun _ : Fin 1 => 1) := by
    change normalize2 (by omega : 0 < 1)
      ((pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).yof
        eq15_4_counterexampleX) = _
    rw [eq15_4_counterexample_y]
    exact eq15_4_normalize2_two
  funext j
  change (∑ i : Fin 1, eq15_4_counterexampleA i j *
    (pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).dp
      ((pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).yof
        eq15_4_counterexampleX) i) = 2
  rw [hdp]
  simp [eq15_4_counterexampleA]

lemma eq15_4_normalize2_one :
    normalize2 (by omega : 0 < 1) (fun _ : Fin 1 => (1 : ℝ)) =
      (fun _ => 1) := by
  have hne : (fun _ : Fin 1 => (1 : ℝ)) ≠ 0 := by
    intro h
    have hh := congrFun h (0 : Fin 1)
    norm_num at hh
  rw [normalize2, if_neg hne]
  funext i
  simp [vecNorm2, vecNorm2Sq]

lemma eq15_4_counterexample_y_norm :
    (pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).pN
      ((pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).yof
        eq15_4_counterexampleX) = 2 := by
  change vecNorm2
    ((pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).yof
      eq15_4_counterexampleX) = 2
  rw [eq15_4_counterexample_y]
  simp [vecNorm2, vecNorm2Sq]

lemma eq15_4_counterexample_dp_x :
    (pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).dp
      eq15_4_counterexampleX = (fun _ : Fin 1 => 1) := by
  change normalize2 (by omega : 0 < 1) eq15_4_counterexampleX = _
  change normalize2 (by omega : 0 < 1) (fun _ : Fin 1 => (1 : ℝ)) = _
  exact eq15_4_normalize2_one

lemma eq15_4_counterexample_dq_z :
    (pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).dq
      ((pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).zof
        eq15_4_counterexampleX) = (fun _ : Fin 1 => 1) := by
  change normalize2 (by omega : 0 < 1)
    ((pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).zof
      eq15_4_counterexampleX) = _
  rw [eq15_4_counterexample_z]
  exact eq15_4_normalize2_two

/-- The displayed Kuhn--Tucker equation preceding (15.4) holds exactly for
`A=[2]`, `x=[1]` in the concrete `p=2` power-method model. -/
theorem eq15_4_counterexample_satisfies_KKT :
    (pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).zof
      eq15_4_counterexampleX =
      fun i =>
        ((pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).pN
          ((pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).yof
            eq15_4_counterexampleX) /
        (pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).pN
          eq15_4_counterexampleX) *
        (pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).dp
          eq15_4_counterexampleX i := by
  rw [eq15_4_counterexample_z, eq15_4_counterexample_y_norm]
  change (fun _ : Fin 1 => (2 : ℝ)) = fun i =>
    (2 / vecNorm2 eq15_4_counterexampleX) *
      (pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).dp
        eq15_4_counterexampleX i
  rw [eq15_4_counterexampleX_norm, eq15_4_counterexample_dp_x]
  norm_num

/-- **Literal equation (15.4) is false for normalized dual maps.**  For the
same stationary `p=2` example, its printed right-hand side is `[1/2]`, not
`x=[1]`.  Thus the coefficient `‖x‖ₚ²/‖Ax‖ₚ` cannot be an equality with the
unit-norm `dualq` used by Algorithm 15.1.  The scale-invariant normalized-dual
relation is instead `x = ‖x‖ₚ dualq(Aᵀ dualp(Ax))`. -/
theorem eq15_4_literal_counterexample :
    eq15_4_counterexampleX ≠ fun i =>
      ((pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).pN
          eq15_4_counterexampleX ^ 2 /
        (pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).pN
          ((pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).yof
            eq15_4_counterexampleX)) *
        (pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).dq
          ((pNormPair_two (by omega : 0 < 1) eq15_4_counterexampleA).zof
            eq15_4_counterexampleX) i := by
  intro heq
  have h0 := congrFun heq (0 : Fin 1)
  rw [eq15_4_counterexample_y_norm, eq15_4_counterexample_dq_z] at h0
  change (1 : ℝ) = (vecNorm2 eq15_4_counterexampleX ^ 2 / 2) * 1 at h0
  rw [eq15_4_counterexampleX_norm] at h0
  norm_num at h0

end Ch15
end NumStability
