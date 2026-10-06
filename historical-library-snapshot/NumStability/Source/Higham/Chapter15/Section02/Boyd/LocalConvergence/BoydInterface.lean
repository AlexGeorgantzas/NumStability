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
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# Chapter15 Section02 Boyd LocalConvergence BoydInterface

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

/-- Audit-grade local-linear bridge for the literal rectangular Algorithm
15.1 trace.  Once a proof from Boyd's exact "strong local maximum" condition
to `IsLocalContractionTo` is supplied, this theorem gives both the advertised
linear rate and `x_k → xbar` without assuming either conclusion. -/
theorem higham15_boyd_local_linear_of_local_contraction
    {m n : ℕ} (P : RectPNormPair m n)
    (x0 xbar : Fin n → ℝ) (K : NNReal) (δ : ℝ)
    (hlocal : IsLocalContractionTo P.xnext xbar K δ)
    (hx0 : dist x0 xbar ≤ δ) :
    (∀ k : ℕ,
      dist (P.xseq x0 k) xbar ≤ (K : ℝ) ^ k * dist x0 xbar) ∧
      Tendsto (P.xseq x0) atTop (𝓝 xbar) := by
  constructor
  · intro k
    rw [rectPNormPair_xseq_eq_iterate P x0 k]
    exact (iterate_dist_le_geometric_of_isLocalContractionTo hlocal hx0 k).1
  · have h := tendsto_iterate_of_isLocalContractionTo hlocal hx0
    rw [show P.xseq x0 = (fun k : ℕ => P.xnext^[k] x0) by
      funext k
      exact rectPNormPair_xseq_eq_iterate P x0 k]
    exact h

/-- Derivative-level local-linear convergence for the literal rectangular
Algorithm 15.1 trace.  Unlike `higham15_boyd_local_linear_of_local_contraction`,
this theorem constructs the contraction radius from differentiability and a
strict derivative-norm bound. -/
theorem higham15_boyd_local_linear_of_fderiv_norm_lt
    {m n : ℕ} (P : RectPNormPair m n)
    (x0 xbar : Fin n → ℝ) (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : NNReal)
    (hfixed : P.xnext xbar = xbar)
    (hderiv : HasFDerivAt P.xnext L xbar)
    (hLK : ‖L‖ < (K : ℝ)) (hK : K < 1) :
    ∃ δ : ℝ, 0 < δ ∧
      (dist x0 xbar ≤ δ →
        (∀ k : ℕ,
          dist (P.xseq x0 k) xbar ≤
            (K : ℝ) ^ k * dist x0 xbar) ∧
        Tendsto (P.xseq x0) atTop (nhds xbar)) := by
  obtain ⟨δ, hδ, hlocal⟩ :=
    exists_isLocalContractionTo_of_hasFDerivAt_norm_lt
      hfixed hderiv hLK hK
  refine ⟨δ, hδ, ?_⟩
  intro hx0
  exact higham15_boyd_local_linear_of_local_contraction
    P x0 xbar K δ hlocal hx0

end Ch15
end NumStability
