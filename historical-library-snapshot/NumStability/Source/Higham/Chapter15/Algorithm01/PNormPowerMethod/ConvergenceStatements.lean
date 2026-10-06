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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Algorithm01.PNormPowerMethod.PNormPowerMethod

/-!
# Chapter15 Algorithm01 PNormPowerMethod ConvergenceStatements

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15ConvergenceProse` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Set

open scoped Topology BigOperators

namespace PNormPair

variable {n : ℕ} (P : PNormPair n)

/-- The estimates in Algorithm 15.1 are monotone as a function of the
iteration number, not merely pairwise ordered at consecutive iterations. -/
theorem gammaSeq_monotone (x0 : Fin n → ℝ) (hx0 : P.pN x0 = 1) :
    Monotone (P.gammaSeq x0) :=
  monotone_nat_of_le_succ (P.gammaSeq_mono x0 hx0)

/-- The range of the scalar estimates is bounded above by the induced
operator norm appearing in Algorithm 15.1. -/
theorem gammaSeq_bddAbove (x0 : Fin n → ℝ) (hx0 : P.pN x0 = 1) :
    BddAbove (Set.range (P.gammaSeq x0)) := by
  refine ⟨P.opP, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact P.gammaSeq_le_opP x0 hx0 k

end PNormPair
end Ch15
end NumStability
