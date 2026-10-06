import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
import NumStability.Algorithms.CondEstimation
import NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Convergence.ConvergenceStatements
import NumStability.Algorithms.NormEstimation.PNorm.Duality.ConvergenceStatements
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.OneAndInfinityNorms.Rectangular
import NumStability.Algorithms.NormEstimation.PNorm.OneAndInfinityNorms.Square
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.RectangularTermination
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Algorithm01.PNormPowerMethod.ConvergenceStatements
import NumStability.Source.Higham.Chapter15.Algorithm01.PNormPowerMethod.PNormPowerMethod
import NumStability.Source.Higham.Chapter15.Algorithm01.PNormPowerMethod.PNormRectangular
import NumStability.Source.Higham.Chapter15.Equation02.Subgradient.PNormGeneral
import NumStability.Source.Higham.Chapter15.Equation02.Subgradient.PNormPowerMethod
import NumStability.Source.Higham.Chapter15.Equation03.GradientQuotient.ConvergenceStatements
import NumStability.Source.Higham.Chapter15.Equation03.GradientQuotient.PNormGeneral
import NumStability.Source.Higham.Chapter15.Equation03.GradientQuotient.PNormPowerMethod
import NumStability.Source.Higham.Chapter15.Equation04.NormalizedDualDiscrepancy.Basic
import NumStability.Source.Higham.Chapter15.Equation05.SubgradientInequality.Basic
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.PNormPowerMethod
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.PNormRectangular
import NumStability.Source.Higham.Chapter15.Section02.Boyd.Corrections.ConvergenceStatements
import NumStability.Source.Higham.Chapter15.Section02.Boyd.EndpointTermination.ConvergenceStatements
import NumStability.Source.Higham.Chapter15.Section02.Boyd.EndpointTermination.RectangularTermination
import NumStability.Source.Higham.Chapter15.Section02.Boyd.GlobalConvergence.ConvergenceStatements

/-!
# Trace

Canonical destination for the frozen declaration block of
`NumStability.Algorithms.HighamChapter15RectTermination`, routed by wave R02 of the August 2026 repository reorganization
completion phase. Declaration names, kinds, visibilities, signatures and
proofs are unchanged; only the module they live in has changed. Private
declarations keep their logical names and are re-mangled against this module,
exactly as recorded in the reviewed private normalization.
-/

/-!
# HighamChapter15RectTermination (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.HighamChapter15RectTermination`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

namespace NumStability

open scoped BigOperators

open Ch15

namespace RectPNormPair

private def infinityNPlusOneCounterexampleX1 : Fin 3 -> Real := ![-1, 1, 1]

private def infinityNPlusOneCounterexampleX2 : Fin 3 -> Real := ![1, 1, 1]

private def infinityNPlusOneCounterexampleX3 : Fin 3 -> Real := ![1, 1, -1]

private def infinityNPlusOneCounterexampleX4 : Fin 3 -> Real := ![-1, 1, -1]

private noncomputable def infinityNPlusOneCounterexampleY0 : Fin 5 -> Real :=
  ![76 / 5, -6 / 5, 69 / 5, -31 / 5, 71 / 5]

private def infinityNPlusOneCounterexampleY1 : Fin 5 -> Real :=
  ![16, 6, 1, -19, 3]

private def infinityNPlusOneCounterexampleY2 : Fin 5 -> Real :=
  ![-12, -12, 3, -25, -29]

private def infinityNPlusOneCounterexampleY3 : Fin 5 -> Real :=
  ![-14, 12, -33, -13, -31]

private def infinityNPlusOneCounterexampleY4 : Fin 5 -> Real :=
  ![14, 30, -35, -7, 1]

private theorem infinityNPlusOneCounterexample_yof_x0 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).yof infinityNPlusOneCounterexampleX0 =
        infinityNPlusOneCounterexampleY0 := by
  funext i
  fin_cases i <;>
    simp [RectPNormPair.yof, infinity, infinityNPlusOneCounterexampleA,
      infinityNPlusOneCounterexampleX0, infinityNPlusOneCounterexampleY0,
      Fin.sum_univ_succ] <;>
    norm_num

private theorem infinityNPlusOneCounterexample_yof_x1 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).yof infinityNPlusOneCounterexampleX1 =
        infinityNPlusOneCounterexampleY1 := by
  funext i
  fin_cases i <;>
    simp [RectPNormPair.yof, infinity, infinityNPlusOneCounterexampleA,
      infinityNPlusOneCounterexampleX1, infinityNPlusOneCounterexampleY1,
      Fin.sum_univ_succ] <;>
    norm_num

private theorem infinityNPlusOneCounterexample_yof_x2 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).yof infinityNPlusOneCounterexampleX2 =
        infinityNPlusOneCounterexampleY2 := by
  funext i
  fin_cases i <;>
    simp [RectPNormPair.yof, infinity, infinityNPlusOneCounterexampleA,
      infinityNPlusOneCounterexampleX2, infinityNPlusOneCounterexampleY2,
      Fin.sum_univ_succ] <;>
    norm_num
  all_goals change (1 : Real) + 2 = 3
  all_goals norm_num

private theorem infinityNPlusOneCounterexample_yof_x3 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).yof infinityNPlusOneCounterexampleX3 =
        infinityNPlusOneCounterexampleY3 := by
  funext i
  fin_cases i <;>
    simp [RectPNormPair.yof, infinity, infinityNPlusOneCounterexampleA,
      infinityNPlusOneCounterexampleX3, infinityNPlusOneCounterexampleY3,
      Fin.sum_univ_succ] <;>
    norm_num

private theorem infinityNPlusOneCounterexample_yof_x4 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).yof infinityNPlusOneCounterexampleX4 =
        infinityNPlusOneCounterexampleY4 := by
  funext i
  fin_cases i <;>
    simp [RectPNormPair.yof, infinity, infinityNPlusOneCounterexampleA,
      infinityNPlusOneCounterexampleX4, infinityNPlusOneCounterexampleY4,
      Fin.sum_univ_succ] <;>
    norm_num

private theorem infinityNPlusOneCounterexample_argmax_x0 :
    argmaxAbs (by norm_num : 0 < 5)
        ((infinity (by norm_num) (by norm_num) infinityNPlusOneCounterexampleA).yof
          infinityNPlusOneCounterexampleX0) = (0 : Fin 5) := by
  let P := infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
    infinityNPlusOneCounterexampleA
  let J := argmaxAbs (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX0)
  have hJ := argmaxAbs_spec (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX0) (0 : Fin 5)
  change |P.yof infinityNPlusOneCounterexampleX0 0| <=
    |P.yof infinityNPlusOneCounterexampleX0 J| at hJ
  have hy : P.yof infinityNPlusOneCounterexampleX0 =
      infinityNPlusOneCounterexampleY0 := by
    simpa [P] using infinityNPlusOneCounterexample_yof_x0
  rw [hy] at hJ
  change J = (0 : Fin 5)
  rcases J with ⟨j, hj⟩
  by_cases htarget : j = 0
  · subst j
    rfl
  · interval_cases j <;>
      norm_num [infinityNPlusOneCounterexampleY0] at htarget
    all_goals norm_num [infinityNPlusOneCounterexampleY0] at hJ

private theorem infinityNPlusOneCounterexample_argmax_x1 :
    argmaxAbs (by norm_num : 0 < 5)
        ((infinity (by norm_num) (by norm_num) infinityNPlusOneCounterexampleA).yof
          infinityNPlusOneCounterexampleX1) = (3 : Fin 5) := by
  let P := infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
    infinityNPlusOneCounterexampleA
  let J := argmaxAbs (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX1)
  have hJ := argmaxAbs_spec (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX1) (3 : Fin 5)
  change |P.yof infinityNPlusOneCounterexampleX1 3| <=
    |P.yof infinityNPlusOneCounterexampleX1 J| at hJ
  have hy : P.yof infinityNPlusOneCounterexampleX1 =
      infinityNPlusOneCounterexampleY1 := by
    simpa [P] using infinityNPlusOneCounterexample_yof_x1
  rw [hy] at hJ
  have htargetValue :
      |infinityNPlusOneCounterexampleY1 (3 : Fin 5)| = 19 := by
    change |(-19 : Real)| = 19
    norm_num
  rw [htargetValue] at hJ
  change J = (3 : Fin 5)
  rcases J with ⟨j, hj⟩
  by_cases htarget : j = 3
  · subst j
    rfl
  · interval_cases j <;>
      norm_num [infinityNPlusOneCounterexampleY1] at htarget
    all_goals norm_num [infinityNPlusOneCounterexampleY1] at hJ

private theorem infinityNPlusOneCounterexample_argmax_x2 :
    argmaxAbs (by norm_num : 0 < 5)
        ((infinity (by norm_num) (by norm_num) infinityNPlusOneCounterexampleA).yof
          infinityNPlusOneCounterexampleX2) = (4 : Fin 5) := by
  let P := infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
    infinityNPlusOneCounterexampleA
  let J := argmaxAbs (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX2)
  have hJ := argmaxAbs_spec (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX2) (4 : Fin 5)
  change |P.yof infinityNPlusOneCounterexampleX2 4| <=
    |P.yof infinityNPlusOneCounterexampleX2 J| at hJ
  have hy : P.yof infinityNPlusOneCounterexampleX2 =
      infinityNPlusOneCounterexampleY2 := by
    simpa [P] using infinityNPlusOneCounterexample_yof_x2
  rw [hy] at hJ
  have htargetValue :
      |infinityNPlusOneCounterexampleY2 (4 : Fin 5)| = 29 := by
    change |(-29 : Real)| = 29
    norm_num
  rw [htargetValue] at hJ
  change J = (4 : Fin 5)
  rcases J with ⟨j, hj⟩
  by_cases htarget : j = 4
  · subst j
    rfl
  · interval_cases j <;>
      norm_num [infinityNPlusOneCounterexampleY2] at htarget
    all_goals norm_num [infinityNPlusOneCounterexampleY2] at hJ

private theorem infinityNPlusOneCounterexample_argmax_x3 :
    argmaxAbs (by norm_num : 0 < 5)
        ((infinity (by norm_num) (by norm_num) infinityNPlusOneCounterexampleA).yof
          infinityNPlusOneCounterexampleX3) = (2 : Fin 5) := by
  let P := infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
    infinityNPlusOneCounterexampleA
  let J := argmaxAbs (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX3)
  have hJ := argmaxAbs_spec (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX3) (2 : Fin 5)
  change |P.yof infinityNPlusOneCounterexampleX3 2| <=
    |P.yof infinityNPlusOneCounterexampleX3 J| at hJ
  have hy : P.yof infinityNPlusOneCounterexampleX3 =
      infinityNPlusOneCounterexampleY3 := by
    simpa [P] using infinityNPlusOneCounterexample_yof_x3
  rw [hy] at hJ
  have htargetValue :
      |infinityNPlusOneCounterexampleY3 (2 : Fin 5)| = 33 := by
    change |(-33 : Real)| = 33
    norm_num
  rw [htargetValue] at hJ
  change J = (2 : Fin 5)
  rcases J with ⟨j, hj⟩
  by_cases htarget : j = 2
  · subst j
    rfl
  · interval_cases j <;>
      norm_num [infinityNPlusOneCounterexampleY3] at htarget
    all_goals norm_num [infinityNPlusOneCounterexampleY3] at hJ

private theorem infinityNPlusOneCounterexample_argmax_x4 :
    argmaxAbs (by norm_num : 0 < 5)
        ((infinity (by norm_num) (by norm_num) infinityNPlusOneCounterexampleA).yof
          infinityNPlusOneCounterexampleX4) = (2 : Fin 5) := by
  let P := infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
    infinityNPlusOneCounterexampleA
  let J := argmaxAbs (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX4)
  have hJ := argmaxAbs_spec (by norm_num : 0 < 5)
    (P.yof infinityNPlusOneCounterexampleX4) (2 : Fin 5)
  change |P.yof infinityNPlusOneCounterexampleX4 2| <=
    |P.yof infinityNPlusOneCounterexampleX4 J| at hJ
  have hy : P.yof infinityNPlusOneCounterexampleX4 =
      infinityNPlusOneCounterexampleY4 := by
    simpa [P] using infinityNPlusOneCounterexample_yof_x4
  rw [hy] at hJ
  have htargetValue :
      |infinityNPlusOneCounterexampleY4 (2 : Fin 5)| = 35 := by
    change |(-35 : Real)| = 35
    norm_num
  rw [htargetValue] at hJ
  change J = (2 : Fin 5)
  rcases J with ⟨j, hj⟩
  by_cases htarget : j = 2
  · subst j
    rfl
  · interval_cases j <;>
      norm_num [infinityNPlusOneCounterexampleY4] at htarget
    all_goals norm_num [infinityNPlusOneCounterexampleY4] at hJ

private def infinityNPlusOneCounterexampleZ0 : Fin 3 -> Real := ![-14, 1, 1]

private def infinityNPlusOneCounterexampleZ1 : Fin 3 -> Real := ![3, 16, 6]

private def infinityNPlusOneCounterexampleZ2 : Fin 3 -> Real := ![16, 14, -1]

private def infinityNPlusOneCounterexampleZ3 : Fin 3 -> Real := ![-1, 16, -18]

private def infinityNPlusOneCounterexampleZ4 : Fin 3 -> Real := ![-1, 16, -18]

private theorem infinityNPlusOneCounterexample_zof_x0 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX0 =
        infinityNPlusOneCounterexampleZ0 := by
  rw [zof_infinity_eq_signed_selected_row_rect,
    infinityNPlusOneCounterexample_argmax_x0,
    infinityNPlusOneCounterexample_yof_x0]
  have hs : signVec infinityNPlusOneCounterexampleY0 (0 : Fin 5) = 1 := by
    change (if 0 <= (76 / 5 : Real) then 1 else -1) = 1
    norm_num
  rw [hs]
  funext j
  fin_cases j <;>
    norm_num [infinityNPlusOneCounterexampleA,
      infinityNPlusOneCounterexampleZ0]

private theorem infinityNPlusOneCounterexample_zof_x1 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX1 =
        infinityNPlusOneCounterexampleZ1 := by
  rw [zof_infinity_eq_signed_selected_row_rect,
    infinityNPlusOneCounterexample_argmax_x1,
    infinityNPlusOneCounterexample_yof_x1]
  have hs : signVec infinityNPlusOneCounterexampleY1 (3 : Fin 5) = -1 := by
    change (if 0 <= (-19 : Real) then 1 else -1) = -1
    norm_num
  rw [hs]
  have hrow :
      (fun j => infinityNPlusOneCounterexampleA (3 : Fin 5) j) =
        ![-3, -16, -6] := by
    rfl
  funext j
  rw [congrFun hrow j]
  fin_cases j <;>
    simp [infinityNPlusOneCounterexampleZ1]

private theorem infinityNPlusOneCounterexample_zof_x2 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX2 =
        infinityNPlusOneCounterexampleZ2 := by
  rw [zof_infinity_eq_signed_selected_row_rect,
    infinityNPlusOneCounterexample_argmax_x2,
    infinityNPlusOneCounterexample_yof_x2]
  have hs : signVec infinityNPlusOneCounterexampleY2 (4 : Fin 5) = -1 := by
    change (if 0 <= (-29 : Real) then 1 else -1) = -1
    norm_num
  rw [hs]
  have hrow :
      (fun j => infinityNPlusOneCounterexampleA (4 : Fin 5) j) =
        ![-16, -14, 1] := by
    rfl
  funext j
  rw [congrFun hrow j]
  fin_cases j <;>
    simp [infinityNPlusOneCounterexampleZ2]

private theorem infinityNPlusOneCounterexample_zof_x3 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX3 =
        infinityNPlusOneCounterexampleZ3 := by
  rw [zof_infinity_eq_signed_selected_row_rect,
    infinityNPlusOneCounterexample_argmax_x3,
    infinityNPlusOneCounterexample_yof_x3]
  have hs : signVec infinityNPlusOneCounterexampleY3 (2 : Fin 5) = -1 := by
    change (if 0 <= (-33 : Real) then 1 else -1) = -1
    norm_num
  rw [hs]
  have hrow :
      (fun j => infinityNPlusOneCounterexampleA (2 : Fin 5) j) =
        ![1, -16, 18] := by
    rfl
  funext j
  rw [congrFun hrow j]
  fin_cases j <;>
    simp [infinityNPlusOneCounterexampleZ3]

private theorem infinityNPlusOneCounterexample_zof_x4 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX4 =
        infinityNPlusOneCounterexampleZ4 := by
  rw [zof_infinity_eq_signed_selected_row_rect,
    infinityNPlusOneCounterexample_argmax_x4,
    infinityNPlusOneCounterexample_yof_x4]
  have hs : signVec infinityNPlusOneCounterexampleY4 (2 : Fin 5) = -1 := by
    change (if 0 <= (-35 : Real) then 1 else -1) = -1
    norm_num
  rw [hs]
  have hrow :
      (fun j => infinityNPlusOneCounterexampleA (2 : Fin 5) j) =
        ![1, -16, 18] := by
    rfl
  funext j
  rw [congrFun hrow j]
  fin_cases j <;>
    simp [infinityNPlusOneCounterexampleZ4]

private theorem infinityNPlusOneCounterexample_xnext_x0 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).xnext infinityNPlusOneCounterexampleX0 =
        infinityNPlusOneCounterexampleX1 := by
  change signVec
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX0) =
    infinityNPlusOneCounterexampleX1
  rw [infinityNPlusOneCounterexample_zof_x0]
  funext j
  fin_cases j <;>
    simp [signVec, infinityNPlusOneCounterexampleZ0,
      infinityNPlusOneCounterexampleX1]

private theorem infinityNPlusOneCounterexample_xnext_x1 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).xnext infinityNPlusOneCounterexampleX1 =
        infinityNPlusOneCounterexampleX2 := by
  change signVec
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX1) =
    infinityNPlusOneCounterexampleX2
  rw [infinityNPlusOneCounterexample_zof_x1]
  funext j
  fin_cases j <;>
    simp [signVec, infinityNPlusOneCounterexampleZ1,
      infinityNPlusOneCounterexampleX2]

private theorem infinityNPlusOneCounterexample_xnext_x2 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).xnext infinityNPlusOneCounterexampleX2 =
        infinityNPlusOneCounterexampleX3 := by
  change signVec
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX2) =
    infinityNPlusOneCounterexampleX3
  rw [infinityNPlusOneCounterexample_zof_x2]
  funext j
  fin_cases j <;>
    simp [signVec, infinityNPlusOneCounterexampleZ2,
      infinityNPlusOneCounterexampleX3]

private theorem infinityNPlusOneCounterexample_xnext_x3 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).xnext infinityNPlusOneCounterexampleX3 =
        infinityNPlusOneCounterexampleX4 := by
  change signVec
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX3) =
    infinityNPlusOneCounterexampleX4
  rw [infinityNPlusOneCounterexample_zof_x3]
  funext j
  fin_cases j <;>
    simp [signVec, infinityNPlusOneCounterexampleZ3,
      infinityNPlusOneCounterexampleX4]

private theorem infinityNPlusOneCounterexample_xseq_zero :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).xseq infinityNPlusOneCounterexampleX0 0 =
        infinityNPlusOneCounterexampleX0 := by
  rfl

private theorem infinityNPlusOneCounterexample_xseq_one :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).xseq infinityNPlusOneCounterexampleX0 1 =
        infinityNPlusOneCounterexampleX1 := by
  change (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
    infinityNPlusOneCounterexampleA).xnext infinityNPlusOneCounterexampleX0 =
      infinityNPlusOneCounterexampleX1
  exact infinityNPlusOneCounterexample_xnext_x0

private theorem infinityNPlusOneCounterexample_xseq_two :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).xseq infinityNPlusOneCounterexampleX0 2 =
        infinityNPlusOneCounterexampleX2 := by
  change (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
    infinityNPlusOneCounterexampleA).xnext
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).xnext infinityNPlusOneCounterexampleX0) =
    infinityNPlusOneCounterexampleX2
  rw [infinityNPlusOneCounterexample_xnext_x0,
    infinityNPlusOneCounterexample_xnext_x1]

private theorem infinityNPlusOneCounterexample_xseq_three :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).xseq infinityNPlusOneCounterexampleX0 3 =
        infinityNPlusOneCounterexampleX3 := by
  change (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
    infinityNPlusOneCounterexampleA).xnext
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).xnext
        ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
          infinityNPlusOneCounterexampleA).xnext infinityNPlusOneCounterexampleX0)) =
    infinityNPlusOneCounterexampleX3
  rw [infinityNPlusOneCounterexample_xnext_x0,
    infinityNPlusOneCounterexample_xnext_x1,
    infinityNPlusOneCounterexample_xnext_x2]

private theorem infinityNPlusOneCounterexample_xseq_four :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).xseq infinityNPlusOneCounterexampleX0 4 =
        infinityNPlusOneCounterexampleX4 := by
  change (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
    infinityNPlusOneCounterexampleA).xnext
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).xnext
        ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
          infinityNPlusOneCounterexampleA).xnext
          ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
            infinityNPlusOneCounterexampleA).xnext infinityNPlusOneCounterexampleX0))) =
    infinityNPlusOneCounterexampleX4
  rw [infinityNPlusOneCounterexample_xnext_x0,
    infinityNPlusOneCounterexample_xnext_x1,
    infinityNPlusOneCounterexample_xnext_x2,
    infinityNPlusOneCounterexample_xnext_x3]

private theorem infinityNPlusOneCounterexample_not_stops_x0 :
    Not ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).StopsAt infinityNPlusOneCounterexampleX0) := by
  change Not (oneNormVec
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX0) <=
    Finset.univ.sum (fun j : Fin 3 =>
      (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX0 j *
          infinityNPlusOneCounterexampleX0 j))
  rw [infinityNPlusOneCounterexample_zof_x0]
  simp [oneNormVec, infinityNPlusOneCounterexampleZ0,
    infinityNPlusOneCounterexampleX0, Fin.sum_univ_succ]
  norm_num

private theorem infinityNPlusOneCounterexample_not_stops_x1 :
    Not ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).StopsAt infinityNPlusOneCounterexampleX1) := by
  change Not (oneNormVec
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX1) <=
    Finset.univ.sum (fun j : Fin 3 =>
      (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX1 j *
          infinityNPlusOneCounterexampleX1 j))
  rw [infinityNPlusOneCounterexample_zof_x1]
  simp [oneNormVec, infinityNPlusOneCounterexampleZ1,
    infinityNPlusOneCounterexampleX1, Fin.sum_univ_succ]
  calc
    (16 : Real) + 6 < 3 + (16 + 6) := lt_add_of_pos_left _ (by norm_num)
    _ < 3 + (3 + (16 + 6)) := lt_add_of_pos_left _ (by norm_num)

private theorem infinityNPlusOneCounterexample_not_stops_x2 :
    Not ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).StopsAt infinityNPlusOneCounterexampleX2) := by
  change Not (oneNormVec
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX2) <=
    Finset.univ.sum (fun j : Fin 3 =>
      (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX2 j *
          infinityNPlusOneCounterexampleX2 j))
  rw [infinityNPlusOneCounterexample_zof_x2]
  simp [oneNormVec, infinityNPlusOneCounterexampleZ2,
    infinityNPlusOneCounterexampleX2, Fin.sum_univ_succ]
  calc
    (14 : Real) < 14 + 1 := lt_add_of_pos_right _ (by norm_num)
    _ < 14 + 1 + 1 := lt_add_of_pos_right _ (by norm_num)

private theorem infinityNPlusOneCounterexample_not_stops_x3 :
    Not ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).StopsAt infinityNPlusOneCounterexampleX3) := by
  change Not (oneNormVec
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX3) <=
    Finset.univ.sum (fun j : Fin 3 =>
      (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX3 j *
          infinityNPlusOneCounterexampleX3 j))
  rw [infinityNPlusOneCounterexample_zof_x3]
  simp [oneNormVec, infinityNPlusOneCounterexampleZ3,
    infinityNPlusOneCounterexampleX3, Fin.sum_univ_succ]
  calc
    (16 : Real) + 18 < 1 + (16 + 18) := lt_add_of_pos_left _ (by norm_num)
    _ < 1 + (1 + (16 + 18)) := lt_add_of_pos_left _ (by norm_num)

private theorem infinityNPlusOneCounterexample_stops_x4 :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).StopsAt infinityNPlusOneCounterexampleX4 := by
  change oneNormVec
      ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX4) <=
    Finset.univ.sum (fun j : Fin 3 =>
      (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).zof infinityNPlusOneCounterexampleX4 j *
          infinityNPlusOneCounterexampleX4 j)
  rw [infinityNPlusOneCounterexample_zof_x4]
  simp [oneNormVec, infinityNPlusOneCounterexampleZ4,
    infinityNPlusOneCounterexampleX4, Fin.sum_univ_succ]

/-- **Formal discrepancy witness for Higham p. 291.**  For this `5 x 3`
matrix and unit start, none of the first `n+1 = 4` tests (`k = 0,1,2,3`)
succeeds.  Thus the printed rectangular `n+1` bound is false at
`p = infinity`; the valid general bound is the output-dimensional `m+1`
bound proved by `infinity_terminates_by_m_plus_one_rect`. -/
theorem higham15_rectangular_infinity_n_plus_one_source_discrepancy :
    Not (exists k : Nat, k <= 3 /\
      (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
        infinityNPlusOneCounterexampleA).StopsAt
          ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
            infinityNPlusOneCounterexampleA).xseq
              infinityNPlusOneCounterexampleX0 k)) := by
  rintro ⟨k, hk, hstop⟩
  interval_cases k
  · rw [infinityNPlusOneCounterexample_xseq_zero] at hstop
    exact infinityNPlusOneCounterexample_not_stops_x0 hstop
  · rw [infinityNPlusOneCounterexample_xseq_one] at hstop
    exact infinityNPlusOneCounterexample_not_stops_x1 hstop
  · rw [infinityNPlusOneCounterexample_xseq_two] at hstop
    exact infinityNPlusOneCounterexample_not_stops_x2 hstop
  · rw [infinityNPlusOneCounterexample_xseq_three] at hstop
    exact infinityNPlusOneCounterexample_not_stops_x3 hstop

/-- The same discrepancy trace does stop at its fifth test, `k = 4`. -/
theorem higham15_rectangular_infinity_counterexample_stops_at_four :
    (infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
      infinityNPlusOneCounterexampleA).StopsAt
        ((infinity (by norm_num : 0 < 5) (by norm_num : 0 < 3)
          infinityNPlusOneCounterexampleA).xseq
            infinityNPlusOneCounterexampleX0 4) := by
  rw [infinityNPlusOneCounterexample_xseq_four]
  exact infinityNPlusOneCounterexample_stops_x4

end RectPNormPair
end NumStability
