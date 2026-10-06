import NumStability.Analysis.LinearOperators.Pseudospectra.PowerBounds.Contour

/-!
# Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Equations08To14.PowerBound

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Analysis/PseudospectralPowerBound.lean
--
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 18, Section 18.1, equations (18.8)--(18.9), p. 345.
--
-- This file completes the exact pseudospectral-radius packaging of the
-- Cauchy/resolvent power estimate.  The earlier Dunford development proves
-- the residue identity on circles of radius larger than the algebra norm.
-- Here Cauchy--Goursat deformation moves that identity to every circle lying
-- outside the resolvent-form epsilon-pseudospectrum, and a right-hand limit
-- gives the printed radius (rather than an arbitrary larger circle radius).



namespace NumStability

open scoped Real Topology
open Complex Metric Set Filter

section ComplexBanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]




















































variable [CompleteSpace A]




































































































































































/-- **Higham, 2nd ed., equation (18.8), exact printed endpoint.**

For `epsilon > 0`, if `rho` is the maximum modulus in the resolvent-form
`epsilon`-pseudospectrum (the representation printed immediately before
(18.8)), then for every `k`,

`  ‖a^k‖ ≤ epsilon⁻¹ * rho^(k+1).`

No larger contour radius, residue identity, resolvent bound, or target-scale
inequality is supplied by the caller. -/
theorem higham18_eq18_8_resolventPseudospectralRadius
    (a : A) (epsilon rho : ℝ) (hepsilon : 0 < epsilon)
    (hrho : IsGreatest (resolventPseudospectrumModulusSet epsilon a) rho)
    (k : ℕ) :
    ‖a ^ k‖ ≤ epsilon⁻¹ * rho ^ (k + 1) := by
  let f : ℝ → ℝ := fun R => epsilon⁻¹ * R ^ (k + 1)
  have hf : Tendsto f (nhdsWithin rho (Ioi rho))
      (nhds (epsilon⁻¹ * rho ^ (k + 1))) := by
    exact (continuousAt_const.mul (continuousAt_id.pow (k + 1))).tendsto.mono_left
      inf_le_left
  have hbound : ∀ᶠ R in nhdsWithin rho (Ioi rho), ‖a ^ k‖ ≤ f R := by
    filter_upwards [self_mem_nhdsWithin] with R hR
    exact norm_pow_le_inv_mul_pow_of_resolventPseudospectralRadius_lt
      a k hrho hR
  have hlimit : ‖a ^ k‖ ≤ epsilon⁻¹ * rho ^ (k + 1) :=
    ge_of_tendsto hf hbound
  have hrhs : 0 ≤ epsilon⁻¹ * rho ^ (k + 1) :=
    mul_nonneg (inv_nonneg.mpr hepsilon.le)
      (pow_nonneg (resolventPseudospectralRadius_nonneg hrho) _)
  calc
    ‖a ^ k‖ ≤ max (epsilon⁻¹ * rho ^ (k + 1)) 0 :=
      hlimit.trans (le_max_left _ _)
    _ = epsilon⁻¹ * rho ^ (k + 1) := max_eq_left hrhs

/-- **Higham equation (18.8), with the radius defined by (18.9).**

This is the assumption-free source-facing endpoint: positivity of `epsilon`
both supplies the compactness/attainment of the maximum in (18.9) and yields
the exact printed constant and exponent. -/
theorem higham18_eq18_8 [Nontrivial A]
    (a : A) (epsilon : ℝ) (hepsilon : 0 < epsilon) (k : ℕ) :
    ‖a ^ k‖ ≤ epsilon⁻¹ *
      resolventPseudospectralRadius epsilon a ^ (k + 1) :=
  higham18_eq18_8_resolventPseudospectralRadius a epsilon
    (resolventPseudospectralRadius epsilon a) hepsilon
    (resolventPseudospectralRadius_isGreatest a hepsilon) k

end ComplexBanachAlgebra

end NumStability
