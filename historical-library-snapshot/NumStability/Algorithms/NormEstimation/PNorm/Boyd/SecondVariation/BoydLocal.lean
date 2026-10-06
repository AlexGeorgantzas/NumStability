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
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydLocal
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Boyd SecondVariation BoydLocal

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

/-- A nondegenerate strict tangent maximum is expressed only through a
uniform negative Hessian gap.  In particular, neither contraction nor power
stability occurs in this definition.  Boyd's nonzero-coordinate regularity
is supplied separately when this predicate is applied to the concrete
normalized-dual update below. -/
def IsBoydNondegenerateTangentHessian
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E → ℝ) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∀ h : E, H h ≤ -η * ‖h‖ ^ 2

/-- Restriction of a derivative to an invariant tangent subspace. -/
noncomputable def boydInvariantRestriction
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : Submodule ℝ V) (L : V →L[ℝ] V)
    (hInv : ∀ h : T, L h ∈ T) : T →L[ℝ] T :=
  (L.comp T.subtypeL).codRestrict T hInv

/-- The tangent derivative transported to a Hilbert model carrying Boyd's
weighted inner product.  A continuous linear equivalence is used, rather
than an isometry, because its norm is generally not the repository's default
Euclidean norm. -/
noncomputable def boydWeightedTangentDerivative
    {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : Submodule ℝ V) (L : V →L[ℝ] V)
    (hInv : ∀ h : T, L h ∈ T) (e : E ≃L[ℝ] T) : E →L[ℝ] E :=
  e.symm.toContinuousLinearMap.comp
    ((boydInvariantRestriction T L hInv).comp e.toContinuousLinearMap)

/-- A symmetric positive-semidefinite operator whose Rayleigh quotient has a
uniform gap below one is a strict contraction.  This is the spectral step in
Boyd Lemma 3. -/
theorem opNorm_le_one_sub_of_symmetric_psd_rayleigh_gap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : E →L[ℝ] E) {δ : ℝ} (hδ1 : δ < 1)
    (hsymm : (L : E →ₗ[ℝ] E).IsSymmetric)
    (hpsd : ∀ h : E, 0 ≤ inner ℝ (L h) h)
    (hupper : ∀ h : E,
      inner ℝ (L h) h ≤ (1 - δ) * ‖h‖ ^ 2) :
    ‖L‖ ≤ 1 - δ := by
  rw [L.norm_eq_iSup_rayleighQuotient hsymm]
  apply ciSup_le
  intro h
  by_cases hh : h = 0
  · subst h
    simp [le_of_lt (sub_pos.mpr hδ1)]
  have hnorm2 : 0 < ‖h‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hh)
  have hray_nonneg : 0 ≤ L.rayleighQuotient h := by
    rw [ContinuousLinearMap.rayleighQuotient]
    exact div_nonneg
      (by simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hpsd h)
      (le_of_lt hnorm2)
  rw [abs_of_nonneg hray_nonneg]
  rw [ContinuousLinearMap.rayleighQuotient]
  apply (div_le_iff₀ hnorm2).2
  simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hupper h

/-- Pure tangent-Hessian nondegeneracy, together with Boyd's Hessian/Rayleigh
identity and weighted self-adjoint positive-semidefinite linearization,
produces a one-step strict contraction in the weighted tangent norm. -/
theorem boyd_weighted_tangent_contraction_of_nondegenerate_hessian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : E →L[ℝ] E) (H : E → ℝ) {κ : ℝ}
    (hκ : 0 < κ)
    (hsymm : (L : E →ₗ[ℝ] E).IsSymmetric)
    (hpsd : ∀ h : E, 0 ≤ inner ℝ (L h) h)
    (hidentity : ∀ h : E,
      H h = κ * (inner ℝ (L h) h - ‖h‖ ^ 2))
    (hnondeg : IsBoydNondegenerateTangentHessian H) :
    ∃ c : NNReal, 0 < c ∧ c < 1 ∧ ‖L‖ ≤ (c : ℝ) := by
  obtain ⟨η, hη, hgap⟩ := hnondeg
  let δ : ℝ := min (η / κ) (1 / 2)
  have hδ0 : 0 < δ :=
    lt_min (div_pos hη hκ) (by norm_num)
  have hδ1 : δ < 1 :=
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hκδ : κ * δ ≤ η := by
    have hd : δ ≤ η / κ := min_le_left _ _
    calc
      κ * δ ≤ κ * (η / κ) :=
        mul_le_mul_of_nonneg_left hd (le_of_lt hκ)
      _ = η := by field_simp
  have hgapδ : ∀ h : E, H h ≤ -(κ * δ) * ‖h‖ ^ 2 := by
    intro h
    calc
      H h ≤ -η * ‖h‖ ^ 2 := hgap h
      _ ≤ -(κ * δ) * ‖h‖ ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hκδ (sq_nonneg ‖h‖)
        linarith
  have hupper : ∀ h : E,
      inner ℝ (L h) h ≤ (1 - δ) * ‖h‖ ^ 2 := by
    intro h
    have hscaled :
        κ * (inner ℝ (L h) h - ‖h‖ ^ 2) ≤
          κ * (-δ * ‖h‖ ^ 2) := by
      calc
        κ * (inner ℝ (L h) h - ‖h‖ ^ 2) = H h := (hidentity h).symm
        _ ≤ -(κ * δ) * ‖h‖ ^ 2 := hgapδ h
        _ = κ * (-δ * ‖h‖ ^ 2) := by ring
    nlinarith
  have hnorm :=
    opNorm_le_one_sub_of_symmetric_psd_rayleigh_gap L hδ1 hsymm hpsd hupper
  let c : NNReal := ⟨1 - δ, le_of_lt (sub_pos.mpr hδ1)⟩
  refine ⟨c, ?_, ?_, ?_⟩
  · change 0 < (c : ℝ)
    exact sub_pos.mpr hδ1
  · change (c : ℝ) < 1
    exact sub_lt_self (1 : ℝ) hδ0
  · simpa [c] using hnorm

/-- Strong corrected Boyd Lemma 3 endpoint.  The Hessian gap is a pure
nondegeneracy hypothesis; symmetry, positive semidefiniteness, invariance,
and the Hessian/Rayleigh identity are displayed as the precise second-order
regularity premises.  The conclusion is stable power of the *actual tangent
restriction* in the repository norm, obtained by transferring the weighted
contraction through norm equivalence. -/
theorem boyd_tangent_restriction_power_stable_of_nondegenerate_hessian
    {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : Submodule ℝ V) (L : V →L[ℝ] V)
    (hInv : ∀ h : T, L h ∈ T) (e : E ≃L[ℝ] T)
    (H : E → ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hsymm :
      (boydWeightedTangentDerivative T L hInv e : E →ₗ[ℝ] E).IsSymmetric)
    (hpsd : ∀ h : E,
      0 ≤ inner ℝ (boydWeightedTangentDerivative T L hInv e h) h)
    (hidentity : ∀ h : E,
      H h = κ *
        (inner ℝ (boydWeightedTangentDerivative T L hInv e h) h - ‖h‖ ^ 2))
    (hnondeg : IsBoydNondegenerateTangentHessian H) :
    ∃ N : ℕ, 0 < N ∧ ∃ K : NNReal,
      0 < K ∧ K < 1 ∧
        ContinuousLinearMap.opNorm
          ((boydInvariantRestriction T L hInv) ^ N) ≤ (K : ℝ) ^ N := by
  let S := boydWeightedTangentDerivative T L hInv e
  obtain ⟨c, hc0, hc1, hSc⟩ :=
    boyd_weighted_tangent_contraction_of_nondegenerate_hessian
      S H hκ (by simpa [S] using hsymm) (by simpa [S] using hpsd)
        (by simpa [S] using hidentity) hnondeg
  let K : NNReal := (c + 1) / 2
  have hcK : c < K := by
    rw [show K = (c + 1) / 2 by rfl]
    apply (lt_div_iff₀ (by norm_num : (0 : NNReal) < 2)).2
    calc
      c * 2 = c + c := by ring
      _ < c + 1 := by simpa [add_comm] using add_lt_add_left hc1 c
  have hK1 : K < 1 := by
    rw [show K = (c + 1) / 2 by rfl]
    apply (div_lt_iff₀ (by norm_num : (0 : NNReal) < 2)).2
    calc
      c + 1 < 1 + 1 := by simpa [add_comm] using add_lt_add_right hc1 1
      _ = 1 * 2 := by ring
  have hK0 : 0 < K := lt_of_lt_of_le hc0 (le_of_lt hcK)
  letI : Norm (T →L[ℝ] T) :=
    ContinuousLinearMap.hasOpNorm (σ₁₂ := RingHom.id ℝ)
  obtain ⟨N, hN, hpow⟩ :=
    exists_pos_power_bound_of_equivalent_contraction
      e (boydInvariantRestriction T L hInv) hcK (by simpa [S,
        boydWeightedTangentDerivative] using hSc)
  exact ⟨N, hN, K, hK0, hK1, hpow⟩

end Ch15
end NumStability
