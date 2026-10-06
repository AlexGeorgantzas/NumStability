import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.PNorm.Duality.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Boyd Differentiation BoydInterface

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydBridges` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

/-- The concrete rectangular objective `x ↦ ‖A x‖_p` is continuous. -/
theorem continuous_rect_general_objective {m n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) :
    Continuous (fun x : Fin n → ℝ =>
      realVecLpNorm p ((RectPNormPair.general hn hpq A).yof x)) := by
  apply (continuous_realVecLpNorm hpq.pos).comp
  unfold RectPNormPair.yof
  fun_prop

theorem continuous_rect_general_yof {m n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) :
    Continuous (RectPNormPair.general hn hpq A).yof := by
  unfold RectPNormPair.yof
  fun_prop

theorem continuousAt_rect_general_zof {m n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) {x : Fin n → ℝ}
    (hyne : (RectPNormPair.general hn hpq A).yof x ≠ 0) :
    ContinuousAt (RectPNormPair.general hn hpq A).zof x := by
  let P := RectPNormPair.general hn hpq A
  have hycont : ContinuousAt P.yof x := by
    exact (continuous_rect_general_yof hn hpq A).continuousAt
  have hdualcomp : ContinuousAt (fun v => realLpDual hpq (P.yof v)) x :=
    (continuousAt_realLpDual hpq hyne).comp hycont
  apply continuousAt_pi'
  intro j
  change ContinuousAt
    (fun v => ∑ i : Fin m, A i j * realLpDual hpq (P.yof v) i) x
  have hsum : ∀ s : Finset (Fin m), ContinuousAt
      (fun v => ∑ i ∈ s, A i j * realLpDual hpq (P.yof v) i) x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using
          (continuousAt_const : ContinuousAt
            (fun _ : Fin n → ℝ => (0 : ℝ)) x)
    | @insert i s hi ih =>
        simp only [Finset.sum_insert, hi, not_false_eq_true]
        have hcoord : ContinuousAt
            (fun v => realLpDual hpq (P.yof v) i) x :=
          (continuous_apply i).continuousAt.comp hdualcomp
        exact (continuousAt_const.mul hcoord).add ih
  simpa using hsum Finset.univ

theorem continuousAt_rect_general_xnext {m n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) {x : Fin n → ℝ}
    (hyne : (RectPNormPair.general hn hpq A).yof x ≠ 0)
    (hzne : (RectPNormPair.general hn hpq A).zof x ≠ 0) :
    ContinuousAt (RectPNormPair.general hn hpq A).xnext x := by
  let P := RectPNormPair.general hn hpq A
  have hzcont : ContinuousAt P.zof x :=
    continuousAt_rect_general_zof hn hpq A hyne
  change ContinuousAt (fun v => realLpDualUnit hn hpq.symm (P.zof v)) x
  exact (continuousAt_realLpDualUnit hn hpq.symm hzne).comp hzcont

end Ch15
end NumStability
