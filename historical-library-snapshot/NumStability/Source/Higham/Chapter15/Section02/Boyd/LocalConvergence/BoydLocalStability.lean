import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
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
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydLocalStability
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# Chapter15 Section02 Boyd LocalConvergence BoydLocalStability

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydLocalStability` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function

open scoped BigOperators Topology

/-- Power-stable derivative bridge for the literal Algorithm 15.1 trace.
It gives a geometric error estimate and convergence on every `N`th iterate.
This is the exact local conclusion needed before the routine finite-residue
argument (or an adapted-norm argument) upgrades it to the full trace. -/
theorem higham15_boyd_local_linear_subsequence_of_fderiv_pow_norm_lt
    {m n : ℕ} (P : RectPNormPair m n)
    (x0 xbar : Fin n → ℝ)
    (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (N : ℕ) (K : NNReal)
    (hfixed : P.xnext xbar = xbar)
    (hderiv : HasFDerivAt P.xnext L xbar)
    (hpow : ‖L ^ N‖ < (K : ℝ)) (hK : K < 1) :
    ∃ δ : ℝ, 0 < δ ∧
      (dist x0 xbar ≤ δ →
        (∀ k : ℕ,
          dist (P.xseq x0 (N * k)) xbar ≤
            (K : ℝ) ^ k * dist x0 xbar) ∧
        Tendsto (fun k : ℕ => P.xseq x0 (N * k)) atTop (nhds xbar)) := by
  obtain ⟨δ, hδ, hlocal⟩ :=
    exists_isLocalContractionTo_iterate_of_hasFDerivAt_pow_norm_lt
      hfixed hderiv hpow hK
  refine ⟨δ, hδ, fun hx0 => ?_⟩
  have hgeom := iterate_dist_le_geometric_of_isLocalContractionTo hlocal hx0
  have hconv := tendsto_iterate_of_isLocalContractionTo hlocal hx0
  constructor
  · intro k
    rw [rectPNormPair_xseq_eq_iterate P x0 (N * k),
      Function.iterate_mul]
    exact (hgeom k).1
  · convert hconv using 1
    funext k
    rw [rectPNormPair_xseq_eq_iterate P x0 (N * k),
      Function.iterate_mul]

/-- Full-trace local linear convergence for Algorithm 15.1 from a stable
derivative.  The finite power certificate is what spectral radius below one
supplies in finite dimension; the theorem constructs the adapted norm rather
than assuming contraction in the repository's default norm. -/
theorem higham15_boyd_local_linear_of_fderiv_power_stable
    {m n : ℕ} (P : RectPNormPair m n)
    (x0 xbar : Fin n → ℝ)
    (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    {N : ℕ} (hN : 0 < N) {c K : NNReal}
    (hc : 0 < c) (hcK : c < K) (hK : K < 1)
    (hpow : ‖L ^ N‖ ≤ (c : ℝ) ^ N)
    (hfixed : P.xnext xbar = xbar)
    (hderiv : HasFDerivAt P.xnext L xbar) :
    ∃ δ : ℝ, 0 < δ ∧
      (powerAdaptedSeminorm L c N (x0 - xbar) ≤ δ →
        (∀ k : ℕ,
          powerAdaptedSeminorm L c N (P.xseq x0 k - xbar) ≤
            (K : ℝ) ^ k * powerAdaptedSeminorm L c N (x0 - xbar)) ∧
        Tendsto (P.xseq x0) atTop (nhds xbar)) := by
  obtain ⟨δ, hδ, hlocal⟩ :=
    exists_local_powerAdaptedSeminormContraction
      hN hc hcK hK hpow hfixed hderiv
  refine ⟨δ, hδ, fun hx0 => ?_⟩
  have hgeom :=
    iterate_seminorm_le_geometric_of_localSeminormContraction hlocal hx0
  have hconv := tendsto_iterate_of_localSeminormContraction
    (fun x => norm_le_powerAdaptedSeminorm L c hN x) hlocal hx0
  constructor
  · intro k
    rw [rectPNormPair_xseq_eq_iterate P x0 k]
    exact (hgeom k).1
  · rw [show P.xseq x0 = (fun k : ℕ => P.xnext^[k] x0) by
      funext k
      exact rectPNormPair_xseq_eq_iterate P x0 k]
    exact hconv

end Ch15
end NumStability
