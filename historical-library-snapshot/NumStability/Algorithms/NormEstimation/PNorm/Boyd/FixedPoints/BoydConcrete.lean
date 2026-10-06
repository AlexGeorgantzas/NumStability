import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
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
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Carrier.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Boyd FixedPoints BoydConcrete

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydConcreteLemma3` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

/-- The exact stationary (nonlinear singular-vector) equation used in Boyd's
Lemma 3, including normalization and positivity of the attained value. -/
def IsBoydConcreteStationary {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Prop :=
  realLpPowerSum p x = 1 ∧
    0 < realLpPowerSum p (boydRectActionCLM A x) ∧
      ∀ j : Fin n,
        (∑ i : Fin m, A i j *
          (|boydRectActionCLM A x i| ^ (p - 2) *
            boydRectActionCLM A x i)) =
          realLpPowerSum p (boydRectActionCLM A x) *
            (|x j| ^ (p - 2) * x j)

end Ch15
end NumStability
