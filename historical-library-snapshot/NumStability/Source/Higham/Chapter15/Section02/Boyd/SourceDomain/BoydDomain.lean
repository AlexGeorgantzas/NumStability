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
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.BoydLocal

/-!
# Chapter15 Section02 Boyd SourceDomain BoydDomain

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydSourceDomain` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

/-- The exact inner smoothness condition inherited from Boyd Lemma 2: no
extra condition is needed for `p >= 2`; in the range `1 < p < 2`, every
coordinate of `A x` must be nonzero. -/
def IsBoydInnerSmoothDomain {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Prop :=
  2 ≤ p ∨ ∀ i, boydRectActionCLM A x i ≠ 0

/-- The actual `RectPNormPair.general.xnext` has the preceding derivative on
the `p >= 2` branch. -/
theorem rect_general_xnext_hasFDerivAt_boyd_of_two_le {m n : ℕ}
    (hn : 0 < n) {p q : ℝ} (hpq : p.HolderConjugate q) (hp2 : 2 ≤ p)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hy : boydRectActionCLM A x ≠ 0)
    (hzcoord : ∀ j,
      boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A x)) j ≠ 0) :
    HasFDerivAt (RectPNormPair.general hn hpq A).xnext
      (boydSmoothRectDerivative (p := p) (q := q) A x) x := by
  let W := boydSmoothRectUpdate (p := p) (q := q) A
  let L := boydSmoothRectDerivative (p := p) (q := q) A x
  have hW : HasFDerivAt W L x := by
    simpa [W, L] using boydSmoothRectUpdate_hasFDerivAt_of_two_le
      hpq.lt hp2 hpq.symm.lt A x hy hzcoord
  have hAcont : ContinuousAt (boydRectActionCLM A) x :=
    (boydRectActionCLM A).continuous.continuousAt
  have hgp : DifferentiableAt ℝ
      (fun u : Fin n → ℝ =>
        realLpGradient p (boydRectActionCLM A u)) x :=
    (differentiableAt_realLpGradient_of_two_le hpq.lt hp2
      (boydRectActionCLM A x) hy).comp x
      (boydRectActionCLM A).differentiableAt
  have hzcont : ContinuousAt
      (fun u : Fin n → ℝ =>
        boydRectTransposeActionCLM A
          (realLpGradient p (boydRectActionCLM A u))) x :=
    ((boydRectTransposeActionCLM A).differentiableAt.comp x hgp).continuousAt
  let i0 : Fin n := ⟨0, hn⟩
  have hz : boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) ≠ 0 := by
    intro hzero
    exact hzcoord i0 (by simpa using congrFun hzero i0)
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

/-- Hence the actual update's Fréchet derivative is the smooth-composition
derivative on the completed `p >= 2` domain. -/
theorem rect_general_fderiv_xnext_eq_boydSmoothRectDerivative_of_two_le
    {m n : ℕ} (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (hp2 : 2 ≤ p)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hy : boydRectActionCLM A x ≠ 0)
    (hzcoord : ∀ j,
      boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A x)) j ≠ 0) :
    fderiv ℝ (RectPNormPair.general hn hpq A).xnext x =
      boydSmoothRectDerivative (p := p) (q := q) A x :=
  (rect_general_xnext_hasFDerivAt_boyd_of_two_le
    hn hpq hp2 A x hy hzcoord).fderiv

/-- Stationarity fixes the literal update without any coordinatewise
nonvanishing assumption on `A x`; positivity of the source power sum is the
precise nonzero-vector condition actually needed here. -/
theorem rect_general_xnext_eq_of_stationarity_source_domain
    {m n : ℕ} (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hunit : realLpPowerSum p x = 1)
    (hSpos : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    (RectPNormPair.general hn hpq A).xnext x = x := by
  let j0 : Fin n := ⟨0, hn⟩
  have hy : boydRectActionCLM A x ≠ 0 := by
    intro hzero
    rw [hzero] at hSpos
    simp [realLpPowerSum, Real.zero_rpow (ne_of_gt hpq.pos)] at hSpos
  have hzcoord := boyd_stationarity_outer_coord_ne
    A x hxcoord hSpos hstationary
  have hz : boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) ≠ 0 := by
    intro hzero
    exact hzcoord j0 (by simpa using congrFun hzero j0)
  rw [rect_general_xnext_eq_boydSmoothRectUpdate hn hpq A x hy hz]
  exact boydSmoothRectUpdate_eq_of_stationarity
    hpq A x hxcoord hunit hSpos hstationary

/-- Terminal actual-`fderiv = S⁻¹PB` bridge under Boyd's exact source-domain
condition. -/
theorem rect_general_fderiv_xnext_apply_eq_inv_projectedLemma3B_source_domain
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hsmooth : IsBoydInnerSmoothDomain p A x)
    (hunit : realLpPowerSum p x = 1)
    (hSpos : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    fderiv ℝ (RectPNormPair.general hn hpq A).xnext x h =
      fun j => (realLpPowerSum p (boydRectActionCLM A x))⁻¹ *
        boydProjectedLemma3B p A x h j := by
  have hy : boydRectActionCLM A x ≠ 0 := by
    intro hzero
    rw [hzero] at hSpos
    simp [realLpPowerSum, Real.zero_rpow (ne_of_gt hpq.pos)] at hSpos
  have hzcoord := boyd_stationarity_outer_coord_ne
    A x hxcoord hSpos hstationary
  rcases hsmooth with hp2 | hycoord
  · rw [rect_general_fderiv_xnext_eq_boydSmoothRectDerivative_of_two_le
      hn hpq hp2 A x hy hzcoord]
    exact boydSmoothRectDerivative_apply_eq_inv_projectedLemma3B_of_two_le
      hpq hp2 A x h hxcoord hunit hSpos hstationary
  · exact rect_general_fderiv_xnext_apply_eq_inv_projectedLemma3B
      hm hn hpq A x h hxcoord hycoord hunit hstationary

end Ch15
end NumStability
