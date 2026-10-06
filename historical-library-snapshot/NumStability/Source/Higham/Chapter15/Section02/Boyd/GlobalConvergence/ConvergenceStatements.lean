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
import NumStability.Algorithms.NormEstimation.PNorm.Convergence.ConvergenceStatements
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Algorithm01.PNormPowerMethod.ConvergenceStatements
import NumStability.Source.Higham.Chapter15.Algorithm01.PNormPowerMethod.PNormPowerMethod
import NumStability.Source.Higham.Chapter15.Equation03.GradientQuotient.ConvergenceStatements
import NumStability.Source.Higham.Chapter15.Equation03.GradientQuotient.PNormPowerMethod

/-!
# Chapter15 Section02 Boyd GlobalConvergence ConvergenceStatements

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

/-- **Higham p. 291, scalar convergence.**  The increasing estimates
`γₖ = ‖A xₖ‖ₚ` actually tend to their conditional supremum.  This is the
topological `Tendsto` theorem missing from the earlier pairwise bounds. -/
theorem gammaSeq_tendsto_ciSup (x0 : Fin n → ℝ) (hx0 : P.pN x0 = 1) :
    Tendsto (P.gammaSeq x0) atTop
      (𝓝 (⨆ k : ℕ, P.gammaSeq x0 k)) :=
  tendsto_atTop_ciSup (P.gammaSeq_monotone x0 hx0)
    (P.gammaSeq_bddAbove x0 hx0)

/-- Existence form of Higham's scalar-convergence sentence, including the
source bounds on the limiting estimate. -/
theorem exists_gammaSeq_limit (x0 : Fin n → ℝ) (hx0 : P.pN x0 = 1) :
    ∃ γ : ℝ,
      Tendsto (P.gammaSeq x0) atTop (𝓝 γ) ∧
        P.gammaSeq x0 0 ≤ γ ∧ γ ≤ P.opP := by
  let γ : ℝ := ⨆ k : ℕ, P.gammaSeq x0 k
  have hlim : Tendsto (P.gammaSeq x0) atTop (𝓝 γ) := by
    simpa [γ] using P.gammaSeq_tendsto_ciSup x0 hx0
  have hmem : γ ∈ Set.Icc (P.gammaSeq x0 0) P.opP :=
    isClosed_Icc.mem_of_tendsto hlim <|
      Eventually.of_forall fun k =>
        ⟨P.gammaSeq_ge_start x0 hx0 k, P.gammaSeq_le_opP x0 hx0 k⟩
  exact ⟨γ, hlim, hmem.1, hmem.2⟩

end PNormPair

/-- Concrete Euclidean closure of Higham's convergent-subsequence sentence.
No compactness premise remains: the repository already proves compactness of
the finite-dimensional Euclidean unit sphere. -/
theorem xseq_two_has_convergent_subsequence {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x0 : Fin n → ℝ) (hx0 : vecNorm2 x0 = 1) :
    ∃ xbar : Fin n → ℝ, vecNorm2 xbar = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto ((pNormPair_two hn A).xseq x0 ∘ φ) atTop (𝓝 xbar) := by
  exact (pNormPair_two hn A).xseq_has_convergent_subsequence x0 hx0
    isCompact_vecNorm2_unit_sphere

/-- Source-faithful conditional core of the p. 291 stationary sentence for
the concrete smooth endpoint `p=2`: if the iterates converge, the update is
continuous at their limit, and `Ax̄ ≠ 0`, then the limit is a stationary point
of `F(x)=‖Ax‖₂/‖x‖₂` (its directional gradient is zero). -/
theorem xseq_two_limit_is_stationary_of_continuousAt {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x0 xbar : Fin n → ℝ)
    (hx0 : vecNorm2 x0 = 1)
    (hlim : Tendsto ((pNormPair_two hn A).xseq x0) atTop (𝓝 xbar))
    (hcont : ContinuousAt (pNormPair_two hn A).xnext xbar)
    (hy : (pNormPair_two hn A).yof xbar ≠ 0) :
    HasDirectionalGradientAt (eq15_3_F_two hn A) 0 xbar := by
  let P := pNormPair_two hn A
  have hnormlim : Tendsto (fun k => vecNorm2 (P.xseq x0 k)) atTop
      (𝓝 (vecNorm2 xbar)) := continuous_vecNorm2.continuousAt.tendsto.comp hlim
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hseqnorm : (fun k => vecNorm2 (P.xseq x0 k)) = fun _ : ℕ => (1 : ℝ) := by
    funext k
    exact P.xseq_punit x0 hx0 k
  have hxbar : vecNorm2 xbar = 1 := by
    rw [hseqnorm] at hnormlim
    exact tendsto_nhds_unique hnormlim hone
  have hfixed : P.xnext xbar = xbar :=
    P.xseq_limit_is_fixed_of_continuousAt x0 xbar hlim hcont
  have hgradzero : eq15_3_gradient_two hn A xbar = 0 :=
    eq15_3_gradient_two_eq_zero_of_fixed hn A xbar hxbar hfixed
  have hxbarne : xbar ≠ 0 := by
    intro h
    subst xbar
    have hzero : vecNorm2 (0 : Fin n → ℝ) = 0 := by
      simpa using (vecNorm2_zero (n := n))
    rw [hzero] at hxbar
    norm_num at hxbar
  have hgrad := eq15_3_directional_two hn A xbar hxbarne hy
  rwa [hgradzero] at hgrad

end Ch15
end NumStability
