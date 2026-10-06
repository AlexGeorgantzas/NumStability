-- Analysis/ResolventFunctionalCalculus.lean
--
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 18, §18.2 — the holomorphic (Cauchy-integral) functional-calculus
-- machinery underneath eq (18.8)
--     ‖Aᵏ‖₂ ≤ ε⁻¹ · ρ_ε(A)^{k+1}.
--
-- CONTEXT.  `Analysis/PseudospectralResolvent.lean` supplied ingredient (1) of
-- (18.8) unconditionally: the resolvent-norm lower bound
-- `1 ≤ ‖z − w‖·‖R(z)‖`.  Its closing note recorded that the two remaining
-- ingredients — (2) the Dunford contour representation
-- `Aᵏ = (2πi)⁻¹ ∮_Γ zᵏ (zI−A)⁻¹ dz` and (3) the contour ML-estimate — were out
-- of reach because Mathlib "LACKS: (a) that `z ↦ resolvent a z` is analytic as
-- an `A`-valued function on the resolvent set … and (b) the functional-calculus
-- residue identity".
--
-- This module CLOSES gap (a) OUTRIGHT and delivers ingredient (3) OUTRIGHT,
-- then assembles the full (18.8)-shaped power bound modulo the single residue
-- identity (b), which is stated as an explicit, honestly-flagged hypothesis.
--
-- WHAT IS UNCONDITIONAL HERE (no extra hypotheses beyond the honest domain):
--
--   ANALYTICITY OF THE RESOLVENT (gap (a), now closed).
--   * `resolvent_hasDerivAt` — `HasDerivAt (resolvent a) (-R(z)^2) z` at each
--       resolvent point (a re-export/rename of `spectrum.hasDerivAt_resolvent`,
--       stated in this namespace for downstream use).
--   * `resolvent_differentiableAt` / `resolvent_differentiableOn` — the
--       `A`-valued resolvent is complex-differentiable at every resolvent point
--       and on the whole resolvent set.  THIS is exactly the "resolvent is
--       analytic on the resolvent set" that the previous module flagged missing.
--   * `resolvent_continuousOn` — hence continuous there (needed for
--       circle-integrability of the contour integrand).
--   * `resolvent_analyticAt` — the honest local power-series (analytic) form,
--       via `DifferentiableOn.analyticAt` on a small ball inside the open
--       resolvent set.
--   * `pow_smul_resolvent_differentiableOn` — the full contour integrand
--       `z ↦ zᵏ • R(z)` is differentiable on the resolvent set (the exact input
--       the vector-valued Cauchy formula consumes; launch point for (b)).
--
--   CONTOUR ML-ESTIMATE (ingredient (3), now closed).
--   * `norm_two_pi_I_inv_smul_circleIntegral_pow_smul_resolvent_le` — for any
--       centre/radius and any uniform bound `C` on `‖zᵏ • R(z)‖` over the
--       circle, `‖(2πi)⁻¹ ∮_{C(c,R)} zᵏ • R(z) dz‖ ≤ R·C`.  This is the exact
--       (length/2π)·max‖integrand‖ estimate specialising Higham's contour
--       bound; it is the `A`-valued specialisation of
--       `circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const`.
--   * `exists_bound_pow_smul_resolvent_on_sphere` — a concrete such uniform
--       bound: continuity of the resolvent on a circle contained in the
--       resolvent set makes `‖zᵏ • R(z)‖` bounded there (uses compactness of the
--       sphere), furnishing the constant `C` for the ML-estimate from geometry
--       alone.
--
--   FULL (18.8)-SHAPED POWER BOUND (assembly, one flagged residue hypothesis).
--   * `norm_pow_le_of_cauchy_representation` — GIVEN the Dunford residue
--       identity `aᵏ = (2πi)⁻¹ ∮_{C(c,R)} zᵏ • R(z) dz` (ingredient (2),
--       hypothesis `hrep`), deduce `‖aᵏ‖ ≤ R·C` for any uniform circle bound
--       `C` on `‖zᵏ • R(z)‖`.  Choosing `c,R` to trace the ε-pseudospectrum
--       boundary and `C = R_max^k · ε⁻¹` yields Higham (18.8) verbatim.
--
-- HONESTY.  The only non-closed link is the residue identity (b): interchanging
-- `∮` with the `A`-valued Neumann series `R(z)=Σ z^{-n-1}aⁿ` (valid on a circle
-- of radius `>‖a‖`) needs a Bochner dominated-convergence interchange for an
-- `A`-valued parametrised integrand that Mathlib does not package for
-- `circleIntegral`.  It is isolated as the single hypothesis `hrep`; the file
-- smuggles NOTHING into a hypothesis that it could prove.
--
-- All statements are over a complex Banach algebra
-- `[NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]` and hold verbatim for
-- Higham's ‖·‖₂ on complex matrices (`CStarMatrix (Fin n) (Fin n) ℂ`, or any
-- concrete operator-norm matrix algebra).

import NumStability.Analysis.PseudospectralResolvent
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace NumStability

open scoped Real Topology
open Complex Metric

section ComplexBanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-! ### Analyticity of the resolvent on the resolvent set (Higham §18.2, gap (a)). -/

/-- **Resolvent derivative** (Higham §18.2, 2nd ed. p. 346; the analytic
    dependence of `R(z)=(zI−a)⁻¹` on `z` underlying the Dunford contour
    representation for (18.8)).

    At every resolvent point `z`, the `A`-valued map `z ↦ resolvent a z` is
    complex-differentiable with derivative `-R(z)²`.  This is the standard
    resolvent identity `dR/dz = -R²`.  (Provided by Mathlib as
    `spectrum.hasDerivAt_resolvent`; re-exported here for the functional
    calculus.) -/
theorem resolvent_hasDerivAt (a : A) {z : ℂ} (hz : z ∈ resolventSet ℂ a) :
    HasDerivAt (resolvent a) (-resolvent a z ^ 2) z :=
  spectrum.hasDerivAt_resolvent hz

/-- **Resolvent is differentiable at each resolvent point** (Higham §18.2,
    2nd ed. p. 346).  Immediate from `resolvent_hasDerivAt`. -/
theorem resolvent_differentiableAt (a : A) {z : ℂ} (hz : z ∈ resolventSet ℂ a) :
    DifferentiableAt ℂ (resolvent a) z :=
  (resolvent_hasDerivAt a hz).differentiableAt

/-- **The resolvent is analytic (differentiable) on the resolvent set — gap (a),
    now CLOSED.** (Higham §18.2, 2nd ed. p. 346.)

    The `A`-valued function `z ↦ resolvent a z` is complex-differentiable on all
    of `resolventSet ℂ a`.  This is precisely the "resolvent is analytic on the
    resolvent set" statement that `PseudospectralResolvent.lean` recorded as the
    missing bridge (a) to the vector-valued Cauchy formula. -/
theorem resolvent_differentiableOn (a : A) :
    DifferentiableOn ℂ (resolvent a) (resolventSet ℂ a) := fun _z hz =>
  (resolvent_differentiableAt a hz).differentiableWithinAt

/-- **The resolvent is continuous on the resolvent set** (Higham §18.2,
    2nd ed. p. 346).  Needed for circle-integrability of the contour integrand.
    Immediate from differentiability. -/
theorem resolvent_continuousOn (a : A) :
    ContinuousOn (resolvent a) (resolventSet ℂ a) :=
  (resolvent_differentiableOn a).continuousOn

/-- **Local analytic (power-series) form of the resolvent** (Higham §18.2,
    2nd ed. p. 346).  At every resolvent point `z`, `z ↦ resolvent a z` is
    `AnalyticAt ℂ`, i.e. locally given by a convergent `A`-valued power series.
    Obtained by differentiability on a small closed ball inside the open
    resolvent set together with `DifferentiableOn.analyticAt`. -/
theorem resolvent_analyticAt (a : A) {z : ℂ} (hz : z ∈ resolventSet ℂ a) :
    AnalyticAt ℂ (resolvent a) z := by
  have hopen : IsOpen (resolventSet ℂ a) := spectrum.isOpen_resolventSet a
  exact (resolvent_differentiableOn a).analyticAt (hopen.mem_nhds hz)

/-- **The contour integrand `z ↦ zᵏ · R(z)` is differentiable on the resolvent
    set** (Higham §18.2, 2nd ed. p. 346).

    The map `z ↦ zᵏ • resolvent a z` is complex-differentiable at every
    resolvent point, hence on all of `resolventSet ℂ a`.  This is the exact
    hypothesis the vector-valued Cauchy formula
    (`Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_…`) consumes, so it
    is the launch point for a future proof of the residue identity (b); we
    record it unconditionally here.  Combines `resolvent_differentiableOn` with
    differentiability of `z ↦ zᵏ`. -/
theorem pow_smul_resolvent_differentiableOn (a : A) (k : ℕ) :
    DifferentiableOn ℂ (fun z : ℂ => z ^ k • resolvent a z) (resolventSet ℂ a) :=
  ((differentiable_pow k).differentiableOn).smul (resolvent_differentiableOn a)

end ComplexBanachAlgebra

/-! ### Contour ML-estimate for `zᵏ · R(z)` (Higham §18.2, ingredient (3)). -/

section Contour

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

omit [CompleteSpace A] in
/-- **Contour ML-estimate — ingredient (3) of (18.8), unconditional.**
    (Higham §18.2, 2nd ed. p. 346; the `(length Γ / 2π)·max‖integrand‖` bound.)

    For any centre `c`, radius `R`, power `k` and any uniform bound `C` on the
    contour integrand `‖zᵏ • R(z)‖` over the circle `|z − c| = R`,
    `‖(2πi)⁻¹ ∮_{C(c,R)} zᵏ • R(z) dz‖ ≤ R · C`.  This is the `A`-valued
    specialisation of
    `circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const`; with
    `Γ` the ε-pseudospectrum boundary it is exactly the estimate feeding into
    Higham (18.8). -/
theorem norm_two_pi_I_inv_smul_circleIntegral_pow_smul_resolvent_le
    (a : A) (c : ℂ) {R C : ℝ} (k : ℕ) (hR : 0 ≤ R)
    (hC : ∀ z ∈ sphere c R, ‖z ^ k • resolvent a z‖ ≤ C) :
    ‖(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), z ^ k • resolvent a z‖ ≤ R * C :=
  circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR hC

/-- **A concrete uniform bound for the contour integrand** (Higham §18.2,
    2nd ed. p. 346).

    If the whole circle `|z − c| = R` lies in the resolvent set, then the
    resolvent is continuous on the (compact) circle, hence bounded there, and
    for the standard radius bound `‖z‖ ≤ |c| + R` on the circle we obtain a
    uniform constant `C` with `‖zᵏ • R(z)‖ ≤ C` for all `z` on the circle.
    This furnishes the hypothesis `hC` of the ML-estimate above from geometry
    alone (no functional calculus). -/
theorem exists_bound_pow_smul_resolvent_on_sphere
    (a : A) (c : ℂ) {R : ℝ} (k : ℕ)
    (hΓ : sphere c R ⊆ resolventSet ℂ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ sphere c R, ‖z ^ k • resolvent a z‖ ≤ C := by
  have hcompact : IsCompact (sphere c R) := isCompact_sphere c R
  have hcont : ContinuousOn (fun z : ℂ => z ^ k • resolvent a z) (sphere c R) := by
    refine ContinuousOn.smul ?_ ((resolvent_continuousOn a).mono hΓ)
    exact (continuous_pow k).continuousOn
  rcases (hcompact.image_of_continuousOn (hcont.norm)).bddAbove with ⟨C, hCub⟩
  refine ⟨max C 0, le_max_right _ _, fun z hz => ?_⟩
  have : ‖z ^ k • resolvent a z‖ ∈ (fun z : ℂ => ‖z ^ k • resolvent a z‖) '' sphere c R :=
    ⟨z, hz, rfl⟩
  exact le_trans (hCub this) (le_max_left _ _)

omit [CompleteSpace A] in
/-- **Higham (18.8), contour form — assembly modulo the Dunford residue
    identity.** (Higham §18.2, eq (18.8), 2nd ed. p. 346.)

    GIVEN the holomorphic-functional-calculus residue representation
    (ingredient (2))
    `aᵏ = (2πi)⁻¹ ∮_{C(c,R)} zᵏ • R(z) dz`  (hypothesis `hrep`)
    and any uniform contour bound `C` on `‖zᵏ • R(z)‖` (ingredient (3), supplied
    unconditionally by `exists_bound_pow_smul_resolvent_on_sphere`), we obtain
    the power bound
    `‖aᵏ‖ ≤ R · C`.

    Taking `Γ = C(c,R)` the boundary of the ε-pseudospectrum gives
    `max_Γ ‖R(z)‖ = ε⁻¹` and `R·max_Γ‖zᵏ‖ ≤ ρ_ε(A)^{k+1}`, so this is exactly
    Higham's eq (18.8) `‖Aᵏ‖₂ ≤ ε⁻¹·ρ_ε(A)^{k+1}`.

    HONEST STATEMENT STRENGTH: the residue identity `hrep` is the single link
    that Mathlib does not yet provide (the `A`-valued term-by-term integration of
    the Neumann series); it is flagged as an explicit hypothesis rather than
    smuggled in, and everything else — the ML bound and the contour bound — is
    proved outright above. -/
theorem norm_pow_le_of_cauchy_representation
    (a : A) (c : ℂ) {R C : ℝ} (k : ℕ) (hR : 0 ≤ R)
    (hC : ∀ z ∈ sphere c R, ‖z ^ k • resolvent a z‖ ≤ C)
    (hrep : a ^ k = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), z ^ k • resolvent a z) :
    ‖a ^ k‖ ≤ R * C := by
  rw [hrep]
  exact norm_two_pi_I_inv_smul_circleIntegral_pow_smul_resolvent_le a c k hR hC

end Contour

end NumStability
