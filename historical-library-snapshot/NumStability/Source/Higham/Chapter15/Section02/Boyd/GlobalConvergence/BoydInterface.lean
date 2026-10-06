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
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Carrier.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Convergence.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.BoydInterface
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.PNormRectangular

/-!
# Chapter15 Section02 Boyd GlobalConvergence BoydInterface

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

/-- Higham p. 291's scalar-convergence sentence for the literal rectangular
Algorithm 15.1 trace. -/
theorem rect_gammaSeq_tendsto_ciSup {m n : ℕ} (P : RectPNormPair m n)
    (x0 : Fin n → ℝ) (hx0 : P.pIn x0 = 1) :
    Tendsto (P.gammaSeq x0) atTop (𝓝 (⨆ k : ℕ, P.gammaSeq x0 k)) :=
  tendsto_atTop_ciSup (rect_gammaSeq_monotone P x0 hx0)
    (rect_gammaSeq_bddAbove P x0 hx0)

/-- Source-facing raw-start package for Boyd's global hypothesis.  The
printed positive `x₀` is normalized exactly as Algorithm 15.1 prescribes, the
normalized start has unit `p`-norm, and every subsequent actual iterate stays
strictly positive. -/
theorem higham15_boyd_normalized_positive_orbit {m n : ℕ}
    [Nontrivial (Fin n)] (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    (x0 : Fin n → ℝ) (hx0 : ∀ j, 0 < x0 j) :
    realVecLpNorm p (realLpNormalizedStart p x0) = 1 ∧
      ∀ k j,
        0 < (RectPNormPair.general hn hpq A).xseq
          (realLpNormalizedStart p x0) k j := by
  constructor
  · exact realLpNormalizedStart_norm_eq_one hn (le_of_lt hpq.lt) x0 hx0
  · exact rect_general_xseq_pos_of_nonneg_gram_irreducible
      hn hpq A hA hGram (realLpNormalizedStart p x0)
      (realLpNormalizedStart_pos hn (le_of_lt hpq.lt) x0 hx0)

/-- Generic global convergence theorem for the literal smooth rectangular
Algorithm 15.1.  Strict Lyapunov increase is derived internally from Lemma
15.2 and the actual stopping rule.  The source-derived theorems above now
supply compactness, invariance, continuity, existence, positivity, and exact
induced-norm optimality under Boyd's printed hypotheses; uniqueness of the
positive normalized fixed point remains the separate nonlinear
Perron--Frobenius gate. -/
theorem higham15_boyd_global_of_compact_unique_optimal_fixed
    {m n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ)
    (s : Set (Fin n → ℝ)) (hs : IsCompact s)
    (x0 xbar : Fin n → ℝ)
    (hx0 : x0 ∈ s)
    (hmap : MapsTo (RectPNormPair.general hn hpq A).xnext s s)
    (hunit : ∀ x ∈ s, realVecLpNorm p x = 1)
    (hz : ∀ x ∈ s, (RectPNormPair.general hn hpq A).zof x ≠ 0)
    (hcontinuous : ContinuousOn
      (RectPNormPair.general hn hpq A).xnext s)
    (hunique : ∀ x ∈ s,
      (RectPNormPair.general hn hpq A).xnext x = x → x = xbar)
    (hoptimal : realVecLpNorm p
      ((RectPNormPair.general hn hpq A).yof xbar) =
        (RectPNormPair.general hn hpq A).opP) :
    Tendsto ((RectPNormPair.general hn hpq A).xseq x0) atTop
        (nhds xbar) ∧
      Tendsto ((RectPNormPair.general hn hpq A).gammaSeq x0) atTop
        (nhds (RectPNormPair.general hn hpq A).opP) := by
  let P := RectPNormPair.general hn hpq A
  let g : (Fin n → ℝ) → ℝ := fun x => realVecLpNorm p (P.yof x)
  have hg : Continuous g := by
    simpa [P, g] using continuous_rect_general_objective hn hpq A
  have hmono : ∀ x ∈ s, g x ≤ g (P.xnext x) := by
    intro x hx
    have hchain := P.higham15_lemma15_2b_rectangular x (hunit x hx)
    exact hchain.1.trans hchain.2.1
  have hfixed_of_back : ∀ x ∈ s,
      g (P.xnext x) ≤ g x → P.xnext x = x := by
    intro x hx hback
    exact rect_general_xnext_eq_of_objective_not_increased
      hn hpq A x (hunit x hx) (hz x hx) hback
  have hiter : Tendsto (fun k : ℕ => P.xnext^[k] x0) atTop
      (nhds xbar) :=
    tendsto_iterate_of_compact_strictLyapunov_unique_fixed
      s hs hx0 hmap hcontinuous g hg hmono hfixed_of_back hunique
  have hxlim : Tendsto (P.xseq x0) atTop (nhds xbar) := by
    rw [show P.xseq x0 = (fun k : ℕ => P.xnext^[k] x0) by
      funext k
      exact rectPNormPair_xseq_eq_iterate P x0 k]
    exact hiter
  refine ⟨hxlim, ?_⟩
  have hglim : Tendsto (fun k => g (P.xseq x0 k)) atTop
      (nhds (g xbar)) := hg.continuousAt.tendsto.comp hxlim
  simpa [RectPNormPair.gammaSeq, g, P, hoptimal] using hglim

end Ch15
end NumStability
