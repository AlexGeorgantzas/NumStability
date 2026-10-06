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
# NumStability Algorithms NormEstimation PNorm Boyd SecondVariation BoydConcrete

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

/-- The Lagrangian line through `x` in direction `h` for the constrained
power objective. -/
noncomputable def boydConstrainedLagrangianLine {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i : Fin m,
      |boydRectActionCLM A x i + t * boydRectActionCLM A h i| ^ p) -
    realLpPowerSum p (boydRectActionCLM A x) *
      ∑ j : Fin n, |x j + t * h j| ^ p

/-- The literal first-derivative formula of the constrained Lagrangian line. -/
noncomputable def boydConstrainedLagrangianFirst {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i : Fin m, p * boydRectActionCLM A h i *
      (|boydRectActionCLM A x i + t * boydRectActionCLM A h i| ^ (p - 2) *
        (boydRectActionCLM A x i + t * boydRectActionCLM A h i))) -
    realLpPowerSum p (boydRectActionCLM A x) *
      ∑ j : Fin n, p * h j *
        (|x j + t * h j| ^ (p - 2) * (x j + t * h j))

/-- The quadratic second variation of
`powerSum p (A u) - powerSum p (A x) * powerSum p u` at `x`.
The theorem below identifies it with an actual second derivative, so this is
not a renamed contraction premise. -/
noncomputable def boydConstrainedSecondVariation {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ) : ℝ :=
  p * (p - 1) *
    ((∑ i : Fin m, |boydRectActionCLM A x i| ^ (p - 2) *
        boydRectActionCLM A h i * boydRectActionCLM A h i) -
      realLpPowerSum p (boydRectActionCLM A x) *
        boydWeightedPair p x h h)

/-- Nondegeneracy is a uniform negative gap in the actual constrained second
variation, only on tangent directions. -/
def IsBoydConcreteNondegenerate {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∀ h : Fin n → ℝ,
    boydWeightedPair p x x h = 0 →
      boydConstrainedSecondVariation p A x h ≤
        -η * boydWeightedPair p x h h

end Ch15
end NumStability
