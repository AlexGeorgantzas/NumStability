import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Seminorm
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
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Scalar.BoydLocal
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Boyd Scalar BoydDomain

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydSourceDomain` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

/-- The derivative of `t ↦ |t|^(p-2)t` remains the textbook formula at zero
when `p >= 2`. -/
theorem hasDerivAt_abs_rpow_sub_two_mul_self_of_two_le
    (p x : ℝ) (hp : 2 ≤ p) :
    HasDerivAt (fun t : ℝ => |t| ^ (p - 2) * t)
      ((p - 1) * |x| ^ (p - 2)) x := by
  apply hasDerivAt_of_hasDerivAt_of_ne'
      (x := (0 : ℝ)) (g := fun t : ℝ => (p - 1) * |t| ^ (p - 2))
  · intro y hy
    exact hasDerivAt_abs_rpow_sub_two_mul_self p y hy
  · exact ((continuous_abs.rpow_const (fun _ => Or.inr (sub_nonneg.mpr hp))).mul
      continuous_id).continuousAt
  · exact (continuous_const.mul
      (continuous_abs.rpow_const (fun _ => Or.inr (sub_nonneg.mpr hp)))).continuousAt

end Ch15
end NumStability
