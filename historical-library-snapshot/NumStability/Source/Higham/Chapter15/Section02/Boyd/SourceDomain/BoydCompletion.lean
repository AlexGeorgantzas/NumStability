import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.MeanInequalitiesPow
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
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Carrier.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydConcrete
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.RowwiseDomain.Basic
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.SecondVariation.BoydConcrete
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Section02.Boyd.Corrections.BoydConcrete

/-!
# Chapter15 Section02 Boyd SourceDomain BoydCompletion

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydSourceClosure` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

/-- Audit-facing correction of Higham's phrase "strong local maximum with no
zero components".  It records all and only the data used by the corrected
Boyd proof: stationary normalized data, a uniform negative constrained-Hessian
gap, nonzero coordinates of the limiting vector, and the exact inner
composition smoothness domain. -/
def IsBoydConcreteSourceStrongLocalMaximum {m n : Nat} (p : Real)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real) : Prop :=
  IsBoydConcreteStrongLocalMaximum p A x /\
    (forall j : Fin n, x j ≠ 0) /\
    IsBoydInnerRowwiseSmoothDomain p A x

/-- A concrete `p < 2` source-domain witness with a genuine zero coordinate
of `A*x`: the second row is identically zero and is therefore harmless. -/
theorem boyd_inner_rowwise_domain_zero_row_example :
    IsBoydInnerRowwiseSmoothDomain ((3 : Real) / 2)
      (fun i : Fin 2 => fun _j : Fin 1 => if i = 0 then 1 else 0)
      (fun _j : Fin 1 => 1) := by
  right
  intro i
  fin_cases i
  · left
    simp [boydRectActionCLM_apply]
  · right
    intro j
    simp

/-- The complete corrected strong-local-maximum predicate is nonvacuous on
the genuinely enlarged `p < 2` source domain: the second row is identically
zero, while the one-dimensional active problem has a normalized stationary
point and a vacuous tangent space. -/
theorem boyd_concrete_source_strongLocalMaximum_zero_row_example :
    IsBoydConcreteSourceStrongLocalMaximum ((3 : Real) / 2)
      (fun i : Fin 2 => fun _j : Fin 1 => if i = 0 then 1 else 0)
      (fun _j : Fin 1 => 1) := by
  let A : Fin 2 -> Fin 1 -> Real :=
    fun i _j => if i = 0 then 1 else 0
  let x : Fin 1 -> Real := fun _j => 1
  have hsmooth : IsBoydInnerRowwiseSmoothDomain ((3 : Real) / 2) A x := by
    simpa [A, x] using boyd_inner_rowwise_domain_zero_row_example
  have hunit : realLpPowerSum ((3 : Real) / 2) x = 1 := by
    simp [realLpPowerSum, x]
  have hS : 0 < realLpPowerSum ((3 : Real) / 2)
      (boydRectActionCLM A x) := by
    norm_num [realLpPowerSum, boydRectActionCLM_apply, A, x]
  have hstationary : forall j : Fin 1,
      (∑ i : Fin 2, A i j *
        (|boydRectActionCLM A x i| ^ (((3 : Real) / 2) - 2) *
          boydRectActionCLM A x i)) =
        realLpPowerSum ((3 : Real) / 2) (boydRectActionCLM A x) *
          (|x j| ^ (((3 : Real) / 2) - 2) * x j) := by
    intro j
    fin_cases j
    norm_num [realLpPowerSum, boydRectActionCLM_apply, A, x]
  have hnondeg : IsBoydConcreteNondegenerate ((3 : Real) / 2) A x := by
    refine ⟨1, by norm_num, ?_⟩
    intro h htangent
    have hzero : h (0 : Fin 1) = 0 := by
      simpa [boydWeightedPair, x] using htangent
    have hh : h = 0 := by
      funext j
      have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      exact hzero
    simp [hh, boydConstrainedSecondVariation, boydWeightedPair]
  change IsBoydConcreteSourceStrongLocalMaximum ((3 : Real) / 2) A x
  exact ⟨⟨⟨hunit, hS, hstationary⟩, hnondeg⟩,
    (by intro j; simp [x]), hsmooth⟩

end Ch15
end NumStability
