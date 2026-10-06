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
import NumStability.Algorithms.NormEstimation.OneNorm.FiniteIndex.Basic
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Carrier.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Duality.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# Chapter15 Section02 Boyd SourceDomain BoydLocal

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydSourceLocal` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

/-- On its source domain, the literal `RectPNormPair.general.xnext` agrees
with the explicit smooth formula. -/
theorem rect_general_xnext_eq_boydSmoothRectUpdate {m n : ℕ}
    (hn : 0 < n) {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hy : boydRectActionCLM A x ≠ 0)
    (hz : boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) ≠ 0) :
    (RectPNormPair.general hn hpq A).xnext x =
      boydSmoothRectUpdate (p := p) (q := q) A x := by
  let P := RectPNormPair.general hn hpq A
  have hyof : P.yof x = boydRectActionCLM A x := by
    rfl
  have hdp : P.dpOut (P.yof x) = realLpGradient p (boydRectActionCLM A x) := by
    change realLpDual hpq (P.yof x) = _
    rw [realLpDual_eq_realLpGradient hpq (P.yof x)]
    · rw [hyof]
    · simpa [hyof] using hy
  have hzof : P.zof x = boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) := by
    funext j
    change (∑ i : Fin m, A i j * P.dpOut (P.yof x) i) = _
    rw [hdp]
    rfl
  change realLpDualUnit hn hpq.symm (P.zof x) = _
  rw [realLpDualUnit, if_neg (by simpa [hzof] using hz),
    realLpDual_eq_realLpGradient hpq.symm (P.zof x)]
  · simp [boydSmoothRectUpdate, hzof]
  · simpa [hzof] using hz

/-- The actual source update has an honest Frechet derivative under Boyd's
coordinate hypotheses.  The proof uses neighborhood stability of the
nonzero coordinates, not merely pointwise rewriting. -/
theorem rect_general_xnext_hasFDerivAt_boyd {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hzcoord : ∀ j,
      boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A x)) j ≠ 0) :
    HasFDerivAt (RectPNormPair.general hn hpq A).xnext
      (boydSmoothRectDerivative (p := p) (q := q) A x) x := by
  let W := boydSmoothRectUpdate (p := p) (q := q) A
  let L := boydSmoothRectDerivative (p := p) (q := q) A x
  have hW : HasFDerivAt W L x := by
    simpa [W, L] using boydSmoothRectUpdate_hasFDerivAt
      hpq.lt hpq.symm.lt A x hycoord hzcoord
  have hAcont : ContinuousAt (boydRectActionCLM A) x :=
    (boydRectActionCLM A).continuous.continuousAt
  have hgp : DifferentiableAt ℝ
      (fun u : Fin n → ℝ =>
        realLpGradient p (boydRectActionCLM A u)) x :=
    (differentiableAt_realLpGradient_of_all_ne hpq.lt _ hycoord).comp x
      (boydRectActionCLM A).differentiableAt
  have hzcont : ContinuousAt
      (fun u : Fin n → ℝ =>
        boydRectTransposeActionCLM A
          (realLpGradient p (boydRectActionCLM A u))) x :=
    ((boydRectTransposeActionCLM A).differentiableAt.comp x hgp).continuousAt
  let i0 : Fin n := ⟨0, hn⟩
  let r0 : Fin m := ⟨0, hm⟩
  have hy0 : boydRectActionCLM A x ≠ 0 := by
    intro hzero
    exact hycoord r0 (by simpa using congrFun hzero r0)
  have hz0 : boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) ≠ 0 := by
    intro hzero
    exact hzcoord i0 (by simpa using congrFun hzero i0)
  have hey : ∀ᶠ u in nhds x, boydRectActionCLM A u ≠ 0 :=
    hAcont.eventually_ne hy0
  have hez : ∀ᶠ u in nhds x,
      boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A u)) ≠ 0 :=
    hzcont.eventually_ne hz0
  have heq : (RectPNormPair.general hn hpq A).xnext =ᶠ[nhds x] W := by
    filter_upwards [hey, hez] with u hyu hzu
    exact rect_general_xnext_eq_boydSmoothRectUpdate hn hpq A u hyu hzu
  exact hW.congr_of_eventuallyEq heq

/-- Consequently the actual `fderiv` is definitionally identified with the
source smooth-composition derivative, rather than left as an existential
linear map. -/
theorem rect_general_fderiv_xnext_eq_boydSmoothRectDerivative {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hzcoord : ∀ j,
      boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A x)) j ≠ 0) :
    fderiv ℝ (RectPNormPair.general hn hpq A).xnext x =
      boydSmoothRectDerivative (p := p) (q := q) A x := by
  exact (rect_general_xnext_hasFDerivAt_boyd
    hm hn hpq A x hycoord hzcoord).fderiv

/-- Literal `RectPNormPair.general` fixedness derived on the corrected smooth
domain.  All `A x` coordinates are required here because that is the current
Lemma-2 differentiability domain; the outer nonzero condition is derived. -/
theorem rect_general_xnext_eq_of_stationarity
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hunit : realLpPowerSum p x = 1)
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    (RectPNormPair.general hn hpq A).xnext x = x := by
  let i0 : Fin m := ⟨0, hm⟩
  let j0 : Fin n := ⟨0, hn⟩
  have hy : boydRectActionCLM A x ≠ 0 := by
    intro hzero
    exact hycoord i0 (by simpa using congrFun hzero i0)
  have hSpos := realLpPowerSum_pos hpq.lt hy
  have hzcoord := boyd_stationarity_outer_coord_ne
    A x hxcoord hSpos hstationary
  have hz : boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) ≠ 0 := by
    intro hzero
    exact hzcoord j0 (by simpa using congrFun hzero j0)
  rw [rect_general_xnext_eq_boydSmoothRectUpdate hn hpq A x hy hz]
  exact boydSmoothRectUpdate_eq_of_stationarity
    hpq A x hxcoord hunit hSpos hstationary

/-- Terminal whole-space Lemma-2 bridge for the literal source update.  It
identifies the actual Fréchet derivative with `S⁻¹ P B` pointwise on every
direction.  No tangent-only restriction and no target-bearing derivative
hypothesis remains. -/
theorem rect_general_fderiv_xnext_apply_eq_inv_projectedLemma3B
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hunit : realLpPowerSum p x = 1)
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    fderiv ℝ (RectPNormPair.general hn hpq A).xnext x h =
      fun j => (realLpPowerSum p (boydRectActionCLM A x))⁻¹ *
        boydProjectedLemma3B p A x h j := by
  let i0 : Fin m := ⟨0, hm⟩
  have hy : boydRectActionCLM A x ≠ 0 := by
    intro hzero
    exact hycoord i0 (by simpa using congrFun hzero i0)
  have hSpos := realLpPowerSum_pos hpq.lt hy
  have hzcoord := boyd_stationarity_outer_coord_ne
    A x hxcoord hSpos hstationary
  rw [rect_general_fderiv_xnext_eq_boydSmoothRectDerivative
    hm hn hpq A x hycoord hzcoord]
  exact boydSmoothRectDerivative_apply_eq_inv_projectedLemma3B
    hpq A x h hxcoord hycoord hunit hSpos hstationary

end Ch15
end NumStability
