import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.MeanInequalitiesPow
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
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Carrier.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.BoydInterface
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.BoydUniqueness
import NumStability.Source.Higham.Chapter15.Section02.Boyd.GlobalConvergence.BoydInterface

/-!
# Chapter15 Section02 Boyd GlobalConvergence BoydUniqueness

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydUniqueness` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

/-- Higham p. 291 / Boyd's global convergence statement at the printed
rectangular dimensions and hypotheses.  The raw strictly positive start is
normalized exactly as Algorithm 15.1 prescribes.  The actual iterates converge
to the unique positive maximizing fixed point, and the actual norm estimates
converge to the exact induced `p`-norm. -/
theorem higham15_boyd_global_of_nonnegative_irreducibleGram
    {m n : ℕ} [Nontrivial (Fin n)] (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    (x0 : Fin n → ℝ) (hx0 : ∀ j, 0 < x0 j) :
    ∃ xbar : Fin n → ℝ,
      xbar ∈ boydNonnegativeUnitCarrier p ∧
      (∀ j, 0 < xbar j) ∧
      (RectPNormPair.general hn hpq A).xnext xbar = xbar ∧
      realVecLpNorm p ((RectPNormPair.general hn hpq A).yof xbar) =
        (RectPNormPair.general hn hpq A).opP ∧
      Tendsto ((RectPNormPair.general hn hpq A).xseq
        (realLpNormalizedStart p x0)) atTop (nhds xbar) ∧
      Tendsto ((RectPNormPair.general hn hpq A).gammaSeq
        (realLpNormalizedStart p x0)) atTop
        (nhds (RectPNormPair.general hn hpq A).opP) := by
  let P := RectPNormPair.general hn hpq A
  let s := boydNonnegativeUnitCarrier (n := n) p
  let xstart := realLpNormalizedStart p x0
  obtain ⟨xbar, hxbar, hxbarpos, hfixed, hoptimal⟩ :=
    exists_boydCarrier_positive_opP_fixedPoint hn hpq A hA hGram
  have hxstart : xstart ∈ s := by
    constructor
    · intro j
      exact (realLpNormalizedStart_pos hn (le_of_lt hpq.lt) x0 hx0 j).le
    · exact realLpNormalizedStart_norm_eq_one
        hn (le_of_lt hpq.lt) x0 hx0
  have hunique : ∀ x ∈ s, P.xnext x = x → x = xbar := by
    intro x hx hxfixed
    exact boydCarrier_fixedPoint_unique hn hpq A hA hGram
      hxbar hfixed hx hxfixed
  have hconv := higham15_boyd_global_of_compact_unique_optimal_fixed
    hn hpq A s (isCompact_boydNonnegativeUnitCarrier hpq)
    xstart xbar hxstart
    (rect_general_xnext_mapsTo_boydCarrier hn hpq A hA hGram)
    (fun x hx => hx.2)
    (fun x hx => rect_general_zof_ne_zero_of_mem_boydCarrier
      hn hpq A hA hGram hx)
    (continuousOn_rect_general_xnext_boydCarrier
      hn hpq A hA hGram)
    hunique hoptimal
  exact ⟨xbar, hxbar, hxbarpos, hfixed, hoptimal, hconv⟩

end Ch15
end NumStability
