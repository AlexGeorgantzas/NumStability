import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Extend
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
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.BoydDomain
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.RowwiseDomain.Basic
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.BoydDomain
import NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.BoydLocal

/-!
# Chapter15 Section02 Boyd SourceDomain BoydRowwise

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydRowwiseDomain` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

/-- The actual `RectPNormPair.general.xnext` has the rowwise-domain derivative
in the nonsmooth inner range. -/
theorem rect_general_xnext_hasFDerivAt_boyd_of_rowwise_lt_two
    {m n : Nat} (hn : 0 < n) {p q : Real}
    (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (hy : boydRectActionCLM A x ≠ 0)
    (hz : boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) ≠ 0)
    (hrowwise : IsBoydRowwiseCompositionSmooth A x) :
    HasFDerivAt (RectPNormPair.general hn hpq A).xnext
      (boydSmoothRectDerivative (p := p) (q := q) A x) x := by
  let W := boydSmoothRectUpdate (p := p) (q := q) A
  let L := boydSmoothRectDerivative (p := p) (q := q) A x
  have hW : HasFDerivAt W L x := by
    simpa [W, L] using boydSmoothRectUpdate_hasFDerivAt_of_rowwise_lt_two
      hpq hp2 A x hy hz hrowwise
  have hAcont : ContinuousAt (boydRectActionCLM A) x :=
    (boydRectActionCLM A).continuous.continuousAt
  have hzcont : ContinuousAt
      (fun u : Fin n -> Real => boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A u))) x := by
    simpa [boydRectNormalMap, boydRectInnerNormalMap] using
      (differentiableAt_boydRectNormalMap_of_rowwise
        hpq.lt A x hy hrowwise).continuousAt
  have hey : ∀ᶠ u in nhds x, boydRectActionCLM A u ≠ 0 :=
    hAcont.eventually_ne hy
  have hez : ∀ᶠ u in nhds x,
      boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A u)) ≠ 0 :=
    hzcont.eventually_ne hz
  have heq : (RectPNormPair.general hn hpq A).xnext =ᶠ[nhds x] W := by
    filter_upwards [hey, hez] with u hyu hzu
    exact rect_general_xnext_eq_boydSmoothRectUpdate hn hpq A u hyu hzu
  exact hW.congr_of_eventuallyEq heq

/-- Identification of the actual update's Fréchet derivative on the rowwise
`p < 2` branch. -/
theorem rect_general_fderiv_xnext_eq_boydSmoothRectDerivative_of_rowwise_lt_two
    {m n : Nat} (hn : 0 < n) {p q : Real}
    (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (hy : boydRectActionCLM A x ≠ 0)
    (hz : boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) ≠ 0)
    (hrowwise : IsBoydRowwiseCompositionSmooth A x) :
    fderiv Real (RectPNormPair.general hn hpq A).xnext x =
      boydSmoothRectDerivative (p := p) (q := q) A x :=
  (rect_general_xnext_hasFDerivAt_boyd_of_rowwise_lt_two
    hn hpq hp2 A x hy hz hrowwise).fderiv

/-- Unified genuine Fréchet-derivative endpoint for the literal update.  The
inner map uses the whole-space `p ≥ 2` theorem or the zero-row theorem below
two; the coordinate premise on the outer input is precisely what is needed
when the conjugate exponent itself lies below two. -/
theorem rect_general_xnext_hasFDerivAt_boyd_rowwise_source_domain
    {m n : Nat} (hn : 0 < n) {p q : Real}
    (hpq : p.HolderConjugate q)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (hy : boydRectActionCLM A x ≠ 0)
    (hzcoord : ∀ j, boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) j ≠ 0)
    (hsmooth : IsBoydInnerRowwiseSmoothDomain p A x) :
    HasFDerivAt (RectPNormPair.general hn hpq A).xnext
      (boydSmoothRectDerivative (p := p) (q := q) A x) x := by
  by_cases hp2 : 2 ≤ p
  · exact rect_general_xnext_hasFDerivAt_boyd_of_two_le
      hn hpq hp2 A x hy hzcoord
  · have hrowwise : IsBoydRowwiseCompositionSmooth A x :=
      Or.resolve_left hsmooth hp2
    have hplt : p < 2 := lt_of_not_ge hp2
    let j0 : Fin n := ⟨0, hn⟩
    have hz : boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A x)) ≠ 0 := by
      intro hzero
      exact hzcoord j0 (by simpa using congrFun hzero j0)
    exact rect_general_xnext_hasFDerivAt_boyd_of_rowwise_lt_two
      hn hpq hplt A x hy hz hrowwise

/-- Unified identification of the actual update derivative with the explicit
smooth-composition derivative. -/
theorem rect_general_fderiv_xnext_eq_boydSmoothRectDerivative_rowwise_source_domain
    {m n : Nat} (hn : 0 < n) {p q : Real}
    (hpq : p.HolderConjugate q)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (hy : boydRectActionCLM A x ≠ 0)
    (hzcoord : ∀ j, boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) j ≠ 0)
    (hsmooth : IsBoydInnerRowwiseSmoothDomain p A x) :
    fderiv Real (RectPNormPair.general hn hpq A).xnext x =
      boydSmoothRectDerivative (p := p) (q := q) A x :=
  (rect_general_xnext_hasFDerivAt_boyd_rowwise_source_domain
    hn hpq A x hy hzcoord hsmooth).fderiv

/-- Terminal actual-`fderiv = S⁻¹ P B` bridge on the `p < 2` zero-row
domain. -/
theorem rect_general_fderiv_xnext_apply_eq_inv_projectedLemma3B_of_rowwise_lt_two
    {m n : Nat} (hn : 0 < n) {p q : Real}
    (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (A : Fin m -> Fin n -> Real) (x h : Fin n -> Real)
    (hxcoord : ∀ j, x j ≠ 0)
    (hrowwise : IsBoydRowwiseCompositionSmooth A x)
    (hunit : realLpPowerSum p x = 1)
    (hSpos : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    fderiv Real (RectPNormPair.general hn hpq A).xnext x h =
      fun j => (realLpPowerSum p (boydRectActionCLM A x))⁻¹ *
        boydProjectedLemma3B p A x h j := by
  have hy : boydRectActionCLM A x ≠ 0 := by
    intro hzero
    rw [hzero] at hSpos
    simp [realLpPowerSum, Real.zero_rpow (ne_of_gt hpq.pos)] at hSpos
  have hzcoord := boyd_stationarity_outer_coord_ne
    A x hxcoord hSpos hstationary
  let j0 : Fin n := ⟨0, hn⟩
  have hz : boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) ≠ 0 := by
    intro hzero
    exact hzcoord j0 (by simpa using congrFun hzero j0)
  rw [rect_general_fderiv_xnext_eq_boydSmoothRectDerivative_of_rowwise_lt_two
    hn hpq hp2 A x hy hz hrowwise]
  exact boydSmoothRectDerivative_apply_eq_inv_projectedLemma3B_of_rowwise_lt_two
    hn hpq hp2 A x h hxcoord hrowwise hunit hSpos hstationary

/-- Unified terminal bridge for Higham Chapter 15: zero rows are admitted in
the nonsmooth inner range, while the existing whole-space theorem supplies the
`2 ≤ p` branch. -/
theorem rect_general_fderiv_xnext_apply_eq_inv_projectedLemma3B_rowwise_source_domain
    {m n : Nat} (hn : 0 < n) {p q : Real}
    (hpq : p.HolderConjugate q)
    (A : Fin m -> Fin n -> Real) (x h : Fin n -> Real)
    (hxcoord : ∀ j, x j ≠ 0)
    (hsmooth : IsBoydInnerRowwiseSmoothDomain p A x)
    (hunit : realLpPowerSum p x = 1)
    (hSpos : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    fderiv Real (RectPNormPair.general hn hpq A).xnext x h =
      fun j => (realLpPowerSum p (boydRectActionCLM A x))⁻¹ *
        boydProjectedLemma3B p A x h j := by
  by_cases hp2 : 2 ≤ p
  · have hy : boydRectActionCLM A x ≠ 0 := by
      intro hzero
      rw [hzero] at hSpos
      simp [realLpPowerSum, Real.zero_rpow (ne_of_gt hpq.pos)] at hSpos
    have hzcoord := boyd_stationarity_outer_coord_ne
      A x hxcoord hSpos hstationary
    rw [rect_general_fderiv_xnext_eq_boydSmoothRectDerivative_of_two_le
      hn hpq hp2 A x hy hzcoord]
    exact boydSmoothRectDerivative_apply_eq_inv_projectedLemma3B_of_two_le
      hpq hp2 A x h hxcoord hunit hSpos hstationary
  · have hrowwise : IsBoydRowwiseCompositionSmooth A x :=
      Or.resolve_left hsmooth hp2
    exact
      rect_general_fderiv_xnext_apply_eq_inv_projectedLemma3B_of_rowwise_lt_two
        hn hpq (lt_of_not_ge hp2) A x h hxcoord hrowwise
          hunit hSpos hstationary

end Ch15
end NumStability
