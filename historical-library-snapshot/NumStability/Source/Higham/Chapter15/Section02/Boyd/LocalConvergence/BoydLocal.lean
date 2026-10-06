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
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydLocalStability
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.SecondVariation.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Section02.Boyd.LocalConvergence.BoydLocalStability
import NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.BoydLocal

/-!
# Chapter15 Section02 Boyd LocalConvergence BoydLocal

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

/-- Concrete source-facing *conditional* endpoint.  The first conjunct is
Boyd Lemma 2 for the literal rectangular update under his nonzero-coordinate
regularity.  The second is the tangent stable-power conclusion from the
nondegenerate Hessian data.  This is deliberately not advertised as a closure
of literal Lemma 3: invariance, weighted symmetry, positive semidefiniteness,
and the Hessian/Rayleigh identity for the concrete formula remain visible
premises below and are the exact open source-strength structural boundary. -/
theorem rect_general_boyd_tangent_power_stable_of_nondegenerate_hessian
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hzcoord : ∀ j,
      boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A x)) j ≠ 0)
    (T : Submodule ℝ (Fin n → ℝ))
    (hInv : ∀ h : T,
      boydSmoothRectDerivative (p := p) (q := q) A x h ∈ T)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E ≃L[ℝ] T) (H : E → ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hsymm : (boydWeightedTangentDerivative T
      (boydSmoothRectDerivative (p := p) (q := q) A x) hInv e :
        E →ₗ[ℝ] E).IsSymmetric)
    (hpsd : ∀ h : E, 0 ≤ inner ℝ
      (boydWeightedTangentDerivative T
        (boydSmoothRectDerivative (p := p) (q := q) A x) hInv e h) h)
    (hidentity : ∀ h : E, H h = κ *
      (inner ℝ (boydWeightedTangentDerivative T
        (boydSmoothRectDerivative (p := p) (q := q) A x) hInv e h) h -
          ‖h‖ ^ 2))
    (hnondeg : IsBoydNondegenerateTangentHessian H) :
    HasFDerivAt (RectPNormPair.general hn hpq A).xnext
      (boydSmoothRectDerivative (p := p) (q := q) A x) x ∧
      ∃ N : ℕ, 0 < N ∧ ∃ K : NNReal,
        0 < K ∧ K < 1 ∧
          ContinuousLinearMap.opNorm
            ((boydInvariantRestriction T
              (boydSmoothRectDerivative (p := p) (q := q) A x) hInv) ^ N) ≤
                (K : ℝ) ^ N := by
  constructor
  · exact rect_general_xnext_hasFDerivAt_boyd
      hm hn hpq A x hycoord hzcoord
  · exact boyd_tangent_restriction_power_stable_of_nondegenerate_hessian
      T (boydSmoothRectDerivative (p := p) (q := q) A x) hInv e H hκ
        hsymm hpsd hidentity hnondeg

/-- Generic local-convergence consumer retained for downstream use.  Unlike
the tangent theorem above, this older whole-space wrapper takes stable power
as an input and therefore is not itself evidence that Boyd Lemma 3 is closed.
The calculus theorem supplies the derivative of the *actual* update, while
the concrete whole-space upgrade remains a separate source boundary. -/
theorem higham15_boyd_local_corrected_of_actual_derivative_power_stable
    {m n : ℕ} (P : RectPNormPair m n)
    (x0 xbar : Fin n → ℝ)
    (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    {N : ℕ} (hN : 0 < N) {c K : NNReal}
    (hc : 0 < c) (hcK : c < K) (hK : K < 1)
    (hfixed : P.xnext xbar = xbar)
    (hderiv : HasFDerivAt P.xnext L xbar)
    (hstable : ‖L ^ N‖ ≤ (c : ℝ) ^ N) :
    ∃ δ : ℝ, 0 < δ ∧
      (powerAdaptedSeminorm L c N (x0 - xbar) ≤ δ →
        (∀ k : ℕ,
          powerAdaptedSeminorm L c N (P.xseq x0 k - xbar) ≤
            (K : ℝ) ^ k * powerAdaptedSeminorm L c N (x0 - xbar)) ∧
        Tendsto (P.xseq x0) atTop (nhds xbar)) :=
  higham15_boyd_local_linear_of_fderiv_power_stable
    P x0 xbar L hN hc hcK hK hstable hfixed hderiv

end Ch15
end NumStability
