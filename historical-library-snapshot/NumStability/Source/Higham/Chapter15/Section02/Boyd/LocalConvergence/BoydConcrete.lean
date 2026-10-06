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
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydConcrete
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydConcrete
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydLocalStability
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.SecondVariation.BoydConcrete
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Section02.Boyd.Corrections.BoydConcrete
import NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.BoydConcrete

/-!
# Chapter15 Section02 Boyd LocalConvergence BoydConcrete

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

/-- Source-facing wrapper of the preceding theorem under the corrected
single hypothesis called a “strong local maximum”.  The definition records
the nondegeneracy missing from an arbitrary strict maximum; it does not
silently repair the mismatch in Boyd's printed wording. -/
theorem higham15_boyd_concrete_linear_of_strongLocalMaximum_subsequentialLimit
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x0 x : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hstrong : IsBoydConcreteStrongLocalMaximum p A x)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hcluster : Tendsto
      (fun s => (RectPNormPair.general hn hpq A).xseq x0 (φ s))
      atTop (nhds x)) :
    ∃ r N : ℕ, 0 < N ∧ ∃ c K : NNReal,
      0 < c ∧ c < K ∧ K < 1 ∧
        (∀ k : ℕ,
          powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
              ((RectPNormPair.general hn hpq A).xseq x0 (φ r + k) - x) ≤
            (K : ℝ) ^ k *
              powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
                ((RectPNormPair.general hn hpq A).xseq x0 (φ r) - x)) ∧
        Tendsto ((RectPNormPair.general hn hpq A).xseq x0)
          atTop (nhds x) :=
  rect_general_boyd_concrete_linear_of_subsequential_limit
    hm hn hpq A x0 x hxcoord hycoord hstrong.1 hstrong.2 φ hφ hcluster

end Ch15
end NumStability
