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
# NumStability Algorithms NormEstimation PNorm Boyd Scalar BoydRowwise

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydRowwiseDomain` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

/-- Holder conjugacy reverses the side of two: if `p ≤ 2`, then its conjugate
exponent satisfies `2 ≤ q`. -/
theorem holderConjugate_two_le_right_of_left_le_two {p q : Real}
    (hpq : p.HolderConjugate q) (hp2 : p ≤ 2) : 2 ≤ q := by
  have hp1 : 0 < p - 1 := sub_pos.mpr hpq.lt
  have hprod : 0 ≤ (p - 1) * (q - 2) := by
    rw [boyd_holder_sub_one_mul_sub_two hpq]
    linarith
  have hprod' : 0 ≤ (q - 2) * (p - 1) := by
    simpa [mul_comm] using hprod
  have hqsub : 0 ≤ q - 2 := nonneg_of_mul_nonneg_left hprod' hp1
  linarith

end Ch15
end NumStability
